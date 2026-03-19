# Informal Specification: `RaftLog::maybe_append` and `RaftLog::maybe_commit`

**Source**: `src/raft_log.rs`
**Target ID**: `maybe_append`
**Phase**: 2 (Informal Spec)

---

## 1. `RaftLog::maybe_append`

### Purpose

`maybe_append(idx, term, committed, ents)` is the receiver-side operation for an
AppendEntries RPC. It checks whether the leader's log is consistent with the follower's
log at the given position `(idx, term)`, and if so, appends any new or conflicting entries
and advances the commit index.

### Signature

```rust
pub fn maybe_append(
    &mut self,
    idx: u64,       // prevLogIndex from the AppendEntries RPC
    term: u64,      // prevLogTerm from the AppendEntries RPC
    committed: u64, // leaderCommit from the AppendEntries RPC
    ents: &[Entry], // entries to append
) -> Option<(u64, u64)>
//         ^conflict_idx   ^last_new_index
```

### Preconditions

- `self.committed <= self.last_index()` (invariant of the log)
- `idx + ents.len()` does not overflow `u64`

### Postconditions

**If `self.term(idx) ≠ Some(term)` (no match)**:
- Returns `None`
- Log state is unchanged

**If `self.term(idx) = Some(term)` (match)**:
- Computes `conflict_idx = find_conflict(ents)`:
  - 0 if all entries in `ents` already match the log
  - Otherwise the index of the first entry in `ents` whose term differs from the log
- **Safety invariant (panic on violation)**: if `conflict_idx > 0` then
  `conflict_idx > self.committed`. A leader MUST NOT send entries that conflict with
  already-committed entries; if it does, this is a fatal error.
- If `conflict_idx > 0`: appends `ents[(conflict_idx - idx - 1)..]` to the log; also
  resets `self.persisted = min(self.persisted, conflict_idx - 1)`
- Sets `last_new_index = idx + ents.len()`
- Advances `self.committed` to `min(committed, last_new_index)` (commit can only
  advance, never decrease; limited to entries that actually exist)
- Returns `Some((conflict_idx, last_new_index))`

### Invariants

- **Commit monotonicity**: `new_committed ≥ old_committed` (because `commit_to` never
  decreases `committed`)
- **Commit bounded by log**: `new_committed ≤ last_new_index = idx + ents.len()`
- **Commit bounded by leader**: `new_committed ≤ committed` (leader's commit value)
- **No truncation of committed**: if a conflict is found, `conflict_idx > self.committed`
  (enforced by panic; postcondition holds for non-panicking executions)
- **Persisted regresses on conflict**: if conflict found, `new_persisted = min(old_persisted,
  conflict_idx - 1)`

### Edge Cases

- `ents = []` (empty entries): `last_new_index = idx`, no entries appended; committed
  advances to `min(committed, idx)` — this is the heartbeat case
- `idx = 0, term = 0`: matches the dummy entry at index 0 (always succeeds if the log
  has a dummy entry with term 0)
- `committed = 0`: commit does not advance (since `committed ≥ old_committed`)
- `conflict_idx = 0` (all entries match): nothing appended, persisted unchanged, only
  commit possibly advances
- Very large `committed` parameter: capped at `last_new_index`, so it cannot
  commit entries beyond the RPC payload

### Examples

Starting from log `[(1,t1), (2,t2), (3,t3)]` with `committed=1, persisted=3`:

1. `maybe_append(3, t3+1, 2, [])` → `None` (term mismatch)
2. `maybe_append(3, t3, 3, [])` → `Some((0, 3))`; committed=3
3. `maybe_append(3, t3, 4, [])` → `Some((0, 3))`; committed=3 (capped at last_new=3)
4. `maybe_append(2, t2, 3, [(3, t4)])` → `Some((3, 3))`; entries[3]=t4; committed=3
5. `maybe_append(0, 0, 1, [(1,t1),(2,t2')])` → conflict at 2, appends from index 2

### Inferred Intent

The function implements the Raft AppendEntries acceptance logic (§5.3). The panic on
conflict ≤ committed encodes the Leader Completeness invariant: a leader that won an
election already has all committed entries, so it can never send a message whose entries
conflict with entries already known to be committed. If such a conflict is observed,
the system is in an impossible state and should crash rather than corrupt committed data.

### Open Questions

1. The `idx + ents.len() as u64` computation could overflow if `ents` is enormous.
   Is there an upper-bound enforced on entry slice length before this call?
2. Is `persisted` required to satisfy `persisted < unstable.offset` before and after?
   The Lean model approximates: persisted tracks how far storage has caught up; conflicts
   can push it backward but it never exceeds `last_index`.
3. Under `max_apply_unpersisted_log_limit > 0`, can `applied > committed` hold? The
   informal spec treats `applied ≤ committed` as the standard invariant.

---

## 2. `RaftLog::maybe_commit`

### Purpose

`maybe_commit(max_index, term)` attempts to advance the commit index to `max_index`.
It only does so if (a) `max_index` is beyond the current commit, and (b) the entry at
`max_index` has the given `term`. Condition (b) prevents committing entries from a
previous term without having a current-term entry in the log (Raft safety, §5.4.2).

### Signature

```rust
pub fn maybe_commit(&mut self, max_index: u64, term: u64) -> bool
```

### Preconditions

- Standard log invariants hold (committed ≤ last_index, etc.)

### Postconditions

- If `max_index > self.committed` and `self.term(max_index) = Ok(term)`:
  - Sets `self.committed = max_index` (via `commit_to`)
  - Returns `true`
- Otherwise:
  - `self.committed` is unchanged
  - Returns `false`

### Invariants

- **Commit monotonicity**: `new_committed ≥ old_committed` always
- **Term requirement**: committed only if the entry's term matches `term`
- **Precision**: `new_committed = max_index` when the function returns `true`

### Edge Cases

- `max_index = self.committed`: returns `false` (no advance; "already committed")
- `max_index < self.committed`: returns `false` (cannot go backward)
- `term` mismatch: returns `false` even if `max_index > committed`

### Examples

State: `committed=3, log=[(1,1),(2,1),(3,1),(4,2),(5,2)]`

1. `maybe_commit(4, 2)` → `true`, `committed=4`
2. `maybe_commit(4, 1)` → `false` (term mismatch: log[4].term=2 ≠ 1)
3. `maybe_commit(3, 1)` → `false` (no advance: max_index ≤ committed)
4. `maybe_commit(5, 2)` → `true`, `committed=5`

### Inferred Intent

This is the quorum commit check. In the leader loop, `maybe_commit` is called after
collecting match indices; it advances the commit only when the quorum index actually
exists in the leader's current term (to satisfy Raft §5.4.2).

### Open Questions

None identified.

---

## 3. `find_conflict` (helper)

`find_conflict(ents)` scans entries left-to-right and returns the index of the first
entry whose term does not match `self.term(entry.index)`. Returns 0 if all match (or
`ents` is empty).

**Key property**: the returned value is 0 or an index ∈ ents such that
`logTerm(result) ≠ Some(ents.term_at(result))`.

---

🔬 *Lean Squad — automated formal verification.*
