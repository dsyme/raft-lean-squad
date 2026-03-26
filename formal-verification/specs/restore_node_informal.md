# Informal Specification: `Raft::restore`

> 🔬 *Lean Squad — auto-generated informal specification.*

## Source

`src/raft.rs`, function `pub fn restore(&mut self, snap: Snapshot) -> bool` (≈ line 2618).

---

## Purpose

`Raft::restore` installs a snapshot into a follower's Raft state machine:
it updates the Raft log, the cluster configuration (via `confchange::restore`),
and the progress tracker. On success it returns `true` and marks the snapshot
as pending application. On any rejection it returns `false` without performing
a full restore.

---

## Preconditions

None enforced by `assert!` in this function. All checks are soft guards that
return early. Callers are expected to only call this on followers, but the
function defends against violations.

---

## Postconditions by path

The function has five distinct control-flow paths:

### Path A — Stale snapshot (`snap.index < committed`)

- **Guard**: `snap.get_metadata().index < self.raft_log.committed`
- **Action**: no state change (logs an info message)
- **Return**: `false`

### Path B — Non-follower defense

- **Guard**: `self.state != StateRole::Follower`
- **Action**: `become_follower(self.term + 1, INVALID_INDEX)` — advances term, demotes to follower
- **Return**: `false`

### Path C — Node not in snapshot config

- **Guard**: `self.id` is not found in `cs.voters ∪ cs.learners ∪ cs.voters_outgoing`
  (note: `learners_next` is excluded because any node there must already be in `voters_outgoing`)
- **Action**: no state change (logs a warning)
- **Return**: `false`

### Path D — Fast-forward (snapshot already in log)

- **Guard**: `pending_request_snapshot == INVALID_INDEX`
  AND `raft_log.match_term(snap.index, snap.term)` is true
  (meaning the snapshot's index/term are already reflected in the local log)
- **Action**: `raft_log.commit_to(snap.index)` — commits up to the snapshot index, no structural log change
- **Return**: `false`

### Path E — Full restore (success)

- **Guard**: none of the above conditions triggered
- **Actions** (in order):
  1. `raft_log.restore(snap)` — installs snap as the pending unstable snapshot;
     advances `committed` to `snap.index`; clears unstable entries
  2. `confchange::restore(&mut prs, last_index, cs)` — rebuilds the progress tracker
     from the snapshot's `ConfState`, using `last_index` as the initial `next_idx` for peers
  3. `post_conf_change()` — updates `self.promotable` based on whether this node is a voter;
     returns new `ConfState` which is asserted to equal the snapshot's `ConfState`
  4. `prs.get_mut(self.id).maybe_update(pr.next_idx - 1)` — sets self's matched to `next_idx - 1`
     (a minor self-progress update; documented as "untested and likely unneeded")
  5. `pending_request_snapshot = INVALID_INDEX` — clears any outstanding snapshot request
- **Return**: `true`

---

## Invariants

- **Commit-monotonicity**: committed index only increases (guard A prevents rollback).
- **Role invariant**: after return, if the function returned `true`, the node is still a Follower
  (the non-follower guard always fires before full restore can happen).
- **Membership**: if full restore succeeds, `self.id` is in the restored config's voter or learner set.
- **No pending request after restore**: on Path E, `pending_request_snapshot` is `INVALID_INDEX`.

---

## Edge Cases

- **`snap.index == committed`**: Path A applies (not strictly less than), so the snapshot
  is applied unless it equals committed exactly — actually the guard is `<` so `==` proceeds.
  Wait: guard is `snap.index < self.raft_log.committed` so `snap.index == committed` goes through.
- **Self not in config**: Path C applies — defensive safety against corrupted snapshots.
- **Term match at snapshot index**: Path D applies — efficient fast-forward without log restructuring.
- **Pending snapshot request**: Path D is bypassed when `pending_request_snapshot != INVALID_INDEX`,
  even if the term matches; ensures we don't skip a snapshot that was explicitly requested.

---

## Examples

| Path | snap.index | committed | state     | match_term | in_config | pending_req | Returns |
|------|-----------|-----------|-----------|------------|-----------|-------------|---------|
| A    | 99        | 100       | Follower  | false      | true      | 0           | false   |
| B    | 200       | 100       | Leader    | false      | true      | 0           | false   |
| C    | 200       | 100       | Follower  | false      | false     | 0           | false   |
| D    | 200       | 100       | Follower  | true       | true      | 0           | false   |
| E    | 200       | 100       | Follower  | false      | true      | 0           | true    |

---

## Inferred Intent

The function is a safety-gated snapshot installer. The four guard paths are
defensive layers: snapshot staleness check, role sanity, membership check, and
the "fast-forward" optimisation (if we already have that log prefix, just advance
the commit pointer instead of restructuring the log). Path E is the interesting
correctness-critical path.

---

## Open Questions

1. **`maybe_update(pr.next_idx - 1)` semantics**: the code comment says "untested and likely unneeded".
   Is this correct, or could it cause `matched` to exceed `last_index`? Should this be removed?
2. **`post_conf_change` assertion**: the fatal `assert` that `new_cs == cs` after `confchange::restore`
   should always hold — can it fail due to a race or bug in `confchange::restore`?
3. **`learners_next` exclusion from membership check**: the comment says any `learners_next` member
   must already be in `voters_outgoing`. Is this invariant enforced upstream?
4. **Applied index**: after restore, is `applied <= committed` guaranteed, or can there be a window
   where `applied > committed` with `max_apply_unpersisted_log_limit > 0`?
