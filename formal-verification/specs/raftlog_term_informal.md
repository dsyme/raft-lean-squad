# Informal Specification: `RaftLog::term` and `RaftLog::match_term`

> 🔬 *Lean Squad — automated informal specification for `dsyme/fv-squad`.*

## Source

- **File**: `src/raft_log.rs`
- **Functions**: `RaftLog::term(idx: u64) -> Result<u64>`,
  `RaftLog::match_term(idx: u64, term: u64) -> bool`

---

## Purpose

`term(idx)` returns the Raft log term associated with the entry at log index `idx`.
It acts as a **dispatch function** that checks the in-memory unstable buffer first,
then falls back to stable storage.

`match_term(idx, term)` answers: "does the log entry at `idx` have the given `term`?"
It is a convenience wrapper over `term`, used by `find_conflict` and `maybe_append` to
detect log inconsistencies between peers.

---

## Preconditions

- `self` is a well-formed `RaftLog` with `first_index() ≥ 1`.
- `last_index()` is always ≥ `first_index() - 1` (the dummy entry).
- No precondition on `idx` — the function is total (no panic path).

---

## Postconditions

### `term(idx)`

1. **Out-of-range (low)**: if `idx < first_index() - 1` (below the dummy index),
   returns `Ok(0)`.

2. **Out-of-range (high)**: if `idx > last_index()`, returns `Ok(0)`.

3. **Unstable hit**: if `idx` is in `[dummy_index, last_index]` and
   `unstable.maybe_term(idx) = Some(t)`, returns `Ok(t)`.

4. **Store fallback**: if `idx` is in range but not in the unstable buffer,
   delegates to `self.store.term(idx)`:
   - If the store returns `Ok(t)`, returns `Ok(t)`.
   - If the store returns `Err(Compacted)` or `Err(Unavailable)`, propagates the error.
   - Any other error causes a panic (`fatal!`).

5. **Dummy index**: `idx = first_index() - 1` is in range and is typically looked up
   from the snapshot metadata (via unstable or store). For a freshly-initialised log
   the dummy entry has term 0.

### `match_term(idx, term)`

6. Returns `term(idx).map(|t| t == term).unwrap_or(false)`.
7. **Iff characterisation**: `match_term(idx, t) = true ↔ term(idx) = Ok(t)`.
8. **Error case**: if `term(idx)` returns an error, `match_term` returns `false`.
9. **Out-of-range sentinel**: for any `t ≠ 0`, out-of-range indices give
   `match_term(idx, t) = false` (because `term` returns `Ok(0)`, not `Ok(t)`).
10. **Sentinel self-match**: `match_term(idx, 0) = true` for any out-of-range `idx`.

---

## Invariants

- The `term` function never panics under the conditions `Compacted` or `Unavailable`.
- The sentinel value `0` for out-of-range indices is a deliberate choice: Raft terms
  start at 1, so `0` is unambiguously "no term / not applicable".
- `match_term` is deterministic — it depends only on the log state, not on side effects.

---

## Edge Cases

| Case | `term(idx)` result | `match_term(idx, t)` |
|------|--------------------|----------------------|
| `idx < first_index() - 1` | `Ok(0)` | `true` iff `t = 0` |
| `idx > last_index()` | `Ok(0)` | `true` iff `t = 0` |
| `idx = first_index() - 1` (dummy) | `Ok(snap_term)` typically | depends |
| `idx` in unstable entries | `Ok(unstable_term)` | depends |
| `idx` compacted in store | `Err(Compacted)` | `false` |
| `idx` unavailable in store | `Err(Unavailable)` | `false` |

---

## Examples

```
// first_index = 5, last_index = 10, unstable has entries 8..10
log.term(3)   // idx = 3 < dummy(4) → Ok(0)
log.term(4)   // idx = 4 = dummy → Ok(snap_term) from store
log.term(7)   // idx = 7, in store range → Ok(store_term(7))
log.term(9)   // idx = 9, in unstable → Ok(unstable_term(9))
log.term(11)  // idx = 11 > last(10) → Ok(0)

log.match_term(3, 0)   // true  (out-of-range sentinel)
log.match_term(3, 1)   // false (out-of-range, term≠0)
log.match_term(9, 3)   // true  if unstable_term(9) = 3
log.match_term(9, 4)   // false if unstable_term(9) = 3
```

---

## Inferred Intent

The `0` sentinel for out-of-range is intentional: callers that compare terms can safely
detect "index not present in my log" without a separate bounds check. The dispatch order
(unstable first, then store) ensures that recently-received but not-yet-persisted entries
shadow stale store entries — critical for correct term matching during log replication.

`match_term` is used as a gate:
- In `maybe_append`: verifies the leader's prevLog entry matches before accepting entries.
- In `find_conflict`: identifies the first conflicting entry to truncate.

---

## Open Questions

1. Is `term(dummy_idx)` always available (never errors)? The Raft invariant suggests yes,
   since the dummy entry is derived from the last snapshot index — but it depends on
   storage implementation details.
2. Can `term` be called concurrently? The Rust type system prevents aliased mutation, but
   the model ignores concurrency.
3. Should the `Err` path for store errors be modelled as `None` vs `Some 0` vs a separate
   error type? The distinction matters for `match_term` (both `Err` and `Ok(wrong_t)`
   give `false`, but for different reasons).

---

*🔬 Lean Squad — auto-generated informal specification.*
