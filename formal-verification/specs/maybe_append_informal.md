# Informal Specification: `RaftLog::maybe_append`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**Source**: `src/raft_log.rs` lines 267–298  
**Depends on**: `find_conflict` (formalised in `FVSquad/FindConflict.lean`)

---

## Purpose

`maybe_append` is the **log-append gate** in a Raft follower. When a leader
sends an `AppendEntries` message, the follower must decide whether to accept and
apply the new entries. The function:

1. Validates the leader's log consistency claim (`idx`, `term`) against the
   local log using `match_term`.
2. If validation passes, finds the first entry in `ents` that conflicts with
   the local log (`find_conflict`).
3. If a conflict exists beyond the committed prefix, truncates the log at the
   conflict point and appends the new suffix.
4. Advances the committed index to `min(committed, last_new_index)`.
5. Returns `Some((conflict_idx, last_new_index))` on success; `None` on failure.

---

## Signature

```rust
pub fn maybe_append(
    &mut self,
    idx: u64,       // index of the entry *preceding* the new entries (leader's prevLogIndex)
    term: u64,      // term of the entry at idx (leader's prevLogTerm)
    committed: u64, // leader's committed index
    ents: &[Entry], // new entries to append (may be empty)
) -> Option<(u64, u64)>
// returns Some((conflict_idx, last_new_index)) on success, None on failure
```

---

## Preconditions

1. `idx` is a valid log index (≤ `last_index()`), or the special case `(idx=0,
   term=0)` which trivially matches the log base.
2. `ents` entries are consecutive: `ents[i].index = idx + i + 1` for all `i`.
3. `committed ≥ self.committed` is not required; the function never *decreases*
   `self.committed` regardless of the input.

---

## Postconditions

### Failure path (`match_term(idx, term)` returns `false`)

* **MA-Fail-1**: Returns `None`.
* **MA-Fail-2**: The log is unchanged (`self.entries` unmodified).
* **MA-Fail-3**: `self.committed` is unchanged.

### Success path (`match_term(idx, term)` returns `true`)

Let:
- `conflict = find_conflict(self, ents)` (0 if no conflict)
- `last_new_index = idx + ents.len()`

* **MA-Succ-1**: Returns `Some((conflict, last_new_index))`.

* **MA-Succ-2 (no conflict)**: If `conflict == 0`, the log is unchanged
  (all entries in `ents` already match the log).

* **MA-Succ-3 (conflict beyond committed)**: If `conflict > self.committed`,
  the log is truncated at `conflict` and `ents[conflict - (idx+1)..]` is appended.
  Any `persisted` index ≥ `conflict` is reset to `conflict - 1`.

* **MA-Succ-4 (conflict at or before committed)**: Panics — this is a safety
  violation (rewriting committed history). This is a **hard invariant** of Raft.

* **MA-Succ-5 (commit advance)**: `self.committed` is advanced to
  `min(committed, last_new_index)`, but only if that value exceeds
  the current `self.committed` (committed never decreases).

* **MA-Succ-6 (commit ceiling)**: The new `self.committed` is always ≤
  `last_new_index`; the leader cannot commit an entry beyond what was just sent.

* **MA-Succ-7 (commit floor)**: The new `self.committed ≥ original self.committed`
  (committed never decreases).

---

## Invariants

* **MA-Inv-1 (committed prefix preserved)**: All entries at indices ≤
  `self.committed` (before the call) remain unchanged after the call.
* **MA-Inv-2 (conflict always beyond idx)**: When `ents` is non-empty and a
  conflict exists, `conflict > idx` (entries are indexed sequentially from
  `idx + 1`).
* **MA-Inv-3 (log suffix coherence)**: After a successful append, entries
  `[idx+1, last_new_index]` in the log exactly match `ents`.

---

## Edge Cases

| Case | Behaviour |
|------|-----------|
| `ents` is empty | Returns `Some((0, idx))`; log unchanged; commit may advance |
| `match_term` fails (idx out of range or term mismatch) | Returns `None` |
| All entries in `ents` already match the log | `conflict = 0`; log unchanged |
| `conflict` exactly equals `committed + 1` | Truncate+append is allowed |
| `committed > last_new_index` | Commit is clamped to `last_new_index` |
| `(idx=0, term=0)` | Matches the log base (empty or snapshot base) |

---

## Examples (from `test_log_maybe_append`)

Initial log: `[(1,1), (2,2), (3,3)]`, `last_index=3`, `last_term=3`, `commit=1`.

| idx | term | committed | ents | result | new_commit |
|-----|------|-----------|------|--------|------------|
| 3   | 2    | 3         | `[(4,4)]` | `None` | 1 (unchanged) |
| 4   | 3    | 3         | `[(6,4)]` | `None` | 1 (idx out of range) |
| 3   | 3    | 3         | `[]`  | `Some((0,3))` | 3 |
| 3   | 3    | 4         | `[]`  | `Some((0,3))` | 3 (clamped to last_new_index=3) |
| 3   | 3    | 2         | `[]`  | `Some((0,3))` | 2 |
| 3   | 3    | 0         | `[]`  | `Some((0,3))` | 1 (no decrease) |
| 3   | 3    | 3         | `[(4,4)]` | `Some((0,4))` | 3 |
| 2   | 2    | 3         | `[(3,4)]` | `Some((3,3))` | 3 (conflict replaces entry 3) |

---

## Inferred Intent

The function implements Raft §5.3 *AppendEntries consistency check*:
- The `(idx, term)` pair is the *prevLogIndex/prevLogTerm* check from the protocol.
- On success, the log is brought into agreement with the leader by
  (a) retaining all matching prefix entries, (b) discarding diverging suffix
  entries, and (c) appending the new entries.
- The commit advance encodes the Raft rule: a follower can advance its commit
  index to the minimum of the leader's commit and the follower's last log index.

---

## Open Questions

1. **Panicking on `conflict ≤ committed`**: is this always reachable in correct
   usage, or is it defensive? Should the function return `Err` instead?
2. **`persisted` semantics**: why is `persisted` reset to `conflict - 1` rather
   than to `min(persisted, conflict - 1)`? (They differ only when
   `persisted < conflict - 1`, which should not happen in correct usage.)
3. **Return value of `conflict_idx`**: when `conflict = 0` (no conflict), the
   return is `(0, last_new_index)`. Is the caller expected to distinguish
   `conflict = 0` (no truncation) from `conflict > 0` (truncation occurred)?

---

## Formal Verification Plan

Target properties for `FVSquad/MaybeAppend.lean`:

| ID | Property | Difficulty |
|----|----------|------------|
| MA-P1 | `match_term` failure ⟹ returns `None` | trivial |
| MA-P2 | Success ⟹ returns `Some((find_conflict(ents), idx + ents.len()))` | definitional |
| MA-P3 | New committed = `max(old_committed, min(committed_arg, last_new_index))` | omega |
| MA-P4 | Committed never decreases | follows from P3 + omega |
| MA-P5 | Committed ≤ last_new_index after success | follows from P3 |
| MA-P6 | Committed prefix (`≤ old_committed`) preserved on success | depends on FC theorems |

These properties are mostly structural/functional and should close with `omega`
and the `FindConflict` theorems already proved.
