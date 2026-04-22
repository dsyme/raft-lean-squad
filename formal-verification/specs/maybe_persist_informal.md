# Informal Specification: `RaftLog::maybe_persist` and `RaftLog::maybe_persist_snap`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/raft_log.rs`, lines 545–610

---

## `maybe_persist(index, term) -> bool`

### Purpose

`maybe_persist` is the callback entry point when a Raft node finishes persisting a batch
of log entries to stable storage (the "ready" flow). It advances the `persisted` index to
`index` if and only if three guards pass:

1. `index > persisted` — we are actually advancing (no regression)
2. `index < first_update_index` — `index` precedes any not-yet-persisted update in the
   unstable buffer. `first_update_index` is either the snapshot index (if an unstable
   snapshot is present) or the `unstable.offset` (the first unstable log entry index).
3. `store.term(index) == term` — the term stored at `index` matches the expected term
   (this guards against the "stale async persist" scenario described in the code comments).

If all three guards pass, `persisted` is set to `index` and `true` is returned.
Otherwise, `persisted` is unchanged and `false` is returned.

### Preconditions

- The caller must pass the `(index, term)` pair that was included in the ready batch
  (i.e., the index and term of the last entry being persisted).
- In normal operation, `index` should be a valid log index (≥ `first_index - 1` and
  ≤ `last_index`).

### Postconditions

- `new_persisted = if guards_pass then index else old_persisted`
- `result = guards_pass`
- `new_persisted ≥ old_persisted` (monotone — never decreases)
- If `result = true`: `new_persisted > old_persisted`, `new_persisted < first_update_index`,
  and `logTerm(new_persisted) = term`

### Invariants

- `persisted` is monotonically non-decreasing across all calls
- `persisted < first_update_index` is preserved (provided initial state is well-formed and
  `first_update_index` only increases or stays the same between calls)

### Edge cases

- `index = persisted`: guard 1 fails → returns false, `persisted` unchanged
- `index < persisted`: guard 1 fails → returns false (would be a regression)
- `index = first_update_index` (not `<`): guard 2 fails → returns false. This is the
  async stale-persist race documented in the code comments.
- `store.term(index) ≠ term`: guard 3 fails → returns false (term mismatch)
- `term = 0`: treated as any other term; returns false if `store.term(index) ≠ 0`

### Examples

| `persisted` | `first_update_index` | `index` | `term` | `store.term(index)` | Result | New `persisted` |
|-------------|---------------------|---------|--------|---------------------|--------|-----------------|
| 3 | 8 | 5 | 2 | 2 | true | 5 |
| 3 | 8 | 3 | 2 | 2 | false | 3 |
| 3 | 8 | 8 | 2 | 2 | false | 3 |
| 3 | 8 | 9 | 2 | 2 | false | 3 |
| 3 | 8 | 5 | 2 | 3 | false | 3 |
| 0 | 5 | 4 | 1 | 1 | true | 4 |
| 0 | 1 | 0 | 0 | 0 | false | 0 |

### Inferred intent

The function is a safety guard for the asynchronous persistence flow. When a Raft node
persists a batch asynchronously, the log state may have changed between when the batch was
sent to storage and when storage confirms completion. The three-guard check ensures that
we never advance `persisted` to a stale or superseded index:

- Guard 1 (monotone): protects against out-of-order completions
- Guard 2 (below unstable): protects against the "figure 8 variant" where a new batch has
  been dispatched whose entries overlap with the completing batch
- Guard 3 (term check): protects against a different entry occupying the same index (from
  a leadership change that caused log truncation and re-insertion)

### Open questions

1. Is `persisted` always guaranteed to be < `first_update_index` when this is called?
   (If so, guard 2 would always pass, and guard 3 would be the real safety gate.)
2. What is the relationship between `persisted` and `committed`? Is it always the case
   that `committed ≤ persisted` must hold, or can committed exceed persisted temporarily?

---

## `maybe_persist_snap(index) -> bool`

### Purpose

The simpler variant: advances `persisted` to `index` (a snapshot index) if
`index > persisted`. No term check is needed because snapshot indices are guaranteed to
be stable. Includes two safety checks (snapshot index ≤ committed, snapshot index <
unstable.offset) that are fatal on violation — indicating programmer error.

### Postconditions

- Returns `true` iff `index > persisted`, in which case `persisted := index`
- Monotone: `new_persisted ≥ old_persisted`

### Edge cases

- `index = persisted`: returns false, no change
- `index < persisted`: returns false (regression rejected monotonically)
- `index > committed`: fatal (snapshot must not exceed committed index)
- `index ≥ unstable.offset`: fatal (snapshot must not overlap unstable log entries)

---

## Lean Modelling Notes

We model the abstract state relevant to these functions as:
- `persisted : Nat` — the stable persistence index
- `firstUpdateIndex : Nat` — the boundary below which storage entries are trusted
- `logTerm : Nat → Nat` — the (infallible) storage term function

We abstract away:
- The `Unstable` buffer internals (used only to compute `firstUpdateIndex`)
- The `store: T` generic; the term function is treated as a total pure function
- Storage error paths (treated as infallible; `is_ok_and` modelled as direct equality)
- The logger and debug/fatal logging
