# Informal Specification: `find_conflict_by_term`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: [`src/raft_log.rs#L218–L257`](../src/raft_log.rs#L218)  
**Phase**: 2 (Informal Spec)  
**Priority**: Medium — used in fast log reconciliation (AppendEntries rejection handling)

---

## Purpose

`find_conflict_by_term(index: u64, term: u64) -> (u64, Option<u64>)` is the **fast log
reconciliation scan** used when a follower rejects an AppendEntries RPC. Given a conflict
hint `(index, term)` from the rejecting follower, it finds the **largest log position** in
`[0, index]` at which the leader's log has a term `≤ term`. This tells the leader how far
back to rewind its `nextIndex` probe to skip over a diverging log tail in one step instead
of probing one-by-one.

In the context of the Raft paper's AppendEntries optimisation (§5.3 and the leader
completeness discussion), the returned index is the last "matching point" in the leader's
view — the leader can safely send entries starting just after this index.

---

## Signature

```rust
pub fn find_conflict_by_term(&self, index: u64, term: u64) -> (u64, Option<u64>)
```

- **`self`**: the leader's `RaftLog`.
- **`index`**: the reject-hint index from the follower. The caller guarantees `index ≤
  self.last_index()` in non-error paths (the code warns and returns early if violated).
- **`term`**: the reject-hint term from the follower (i.e., the term at `index` in the
  follower's log at the time of rejection).
- **Returns**: `(result_index, Some(self.term(result_index)))` where `result_index` is the
  largest index in `[0, index]` with `self.term(result_index) ≤ term`. Returns
  `(result_index, None)` if a term look-up fails (storage error / compaction).

---

## Preconditions

1. `index ≤ self.last_index()` — the normal operating condition. If violated, the
   function logs a warning and returns `(index, None)` early (invalid-input fallback).
2. `term ≥ 0` (always satisfied by `u64`).
3. The log is well-formed: `self.term(i)` is non-decreasing as `i` increases.
   (This is the Raft log monotonicity invariant.)

---

## Postconditions

Let `last = self.last_index()`, and assume `index ≤ last` (the well-formed case).

1. **Result index is in range**: `result_index ≤ index`.
2. **Non-zero term case**: If a storage error does not occur before reaching an index
   where `self.term(i) ≤ term`, then `result_term = Some(self.term(result_index))` and
   `result_term ≤ term`.
3. **Maximality**: For all `j` with `result_index < j ≤ index` (if any),
   `self.term(j) > term` (the scan skips all indices with term strictly greater).
4. **Floor bound**: If `self.term(i) > term` for all `i ∈ [0, index]`, the scan reaches
   index `0` (or the first index of the log), and returns that index with `None` if the
   term lookup fails at the boundary.
5. **Out-of-range input**: If `index > last`, the function returns `(index, None)`
   immediately without scanning.

---

## Invariants and Algorithm

The scan proceeds **backwards** from `index`:

```
conflict_index := index
loop:
  match term(conflict_index):
    Ok(t) if t > term:  conflict_index -= 1     -- too far right, step back
    Ok(t)            :  return (conflict_index, Some(t))  -- found the match point
    Err(_)           :  return (conflict_index, None)     -- storage error
```

Because Raft log terms are **non-decreasing** (by the log matching property), the loop
finds the rightmost index with term `≤ term`. The loop terminates because:
- Either a term `≤ term` is found (log contains index 0 with term 0 ≤ any term).
- Or a storage error is encountered before that point.

**Termination note**: `conflict_index` is a `u64`, so decrementing from 0 would wrap
around. However, the `term()` function returns `Ok(0)` for the dummy entry at index
`first_index() - 1`. Since `term ≥ 0` always holds (u64), the match arm `Ok(t)` where
`t == 0 ≤ term` exits the loop before reaching negative indices. The implementation relies
on this.

---

## Edge Cases

| Scenario | Behaviour |
|----------|-----------|
| `index > last_index()` | Returns `(index, None)` with a warning; no scan |
| `index == 0` | Returns `(0, Some(0))` — dummy entry has term 0 |
| `term == 0` | Returns as soon as it finds `term(i) == 0`, i.e., the dummy entry |
| All log entries in `[0, index]` have term `> term` | Reaches dummy entry at index 0 and returns `(0, Some(0))` |
| Storage error mid-scan | Returns `(conflict_index, None)` at the error point |
| `index == last_index()` and `term(index) ≤ term` | Returns `(index, Some(term(index)))` immediately |
| Full match: `term(index) ≤ term` | Returns without scanning (no loop iteration) |

---

## Examples

Using log `[term=1, term=1, term=2, term=3, term=3]` for indices `[1,2,3,4,5]`:

| Call | Expected return |
|------|----------------|
| `find_conflict_by_term(5, 3)` | `(5, Some(3))` — index 5 has term 3 ≤ 3 |
| `find_conflict_by_term(5, 2)` | `(3, Some(2))` — scan back: 5→term3>2, 4→term3>2, 3→term2≤2 |
| `find_conflict_by_term(5, 1)` | `(2, Some(1))` — scan back to last term-1 entry |
| `find_conflict_by_term(3, 3)` | `(3, Some(2))` — index 3 has term 2 ≤ 3 |
| `find_conflict_by_term(10, 3)` | `(10, None)` — index 10 > last_index=5, warning |

---

## Inferred Intent

The function is used in the **fast AppendEntries rejection path** of `handle_append_response`
(src/raft.rs ~L1657). When a follower rejects with `(reject_hint, log_term)`, the leader
calls `find_conflict_by_term(reject_hint, log_term)` to find the last index in its own log
whose term is ≤ the follower's log term at the reject point. This skips over a diverging
suffix efficiently.

The key correctness property is: **the returned index is a valid probe point** — no entry
between `result_index + 1` and `reject_hint` can match the follower's expectation (because
they all have strictly higher terms in the leader's log).

---

## Open Questions

1. **Underflow**: Is it guaranteed that `conflict_index` never underflows (wraps to
   `u64::MAX`)? The code relies on `term(0)` (or the dummy entry) returning `Ok(0)`,
   which exits before decrement-to-negative. Is this invariant explicitly maintained
   and checked, or just relied upon implicitly?

2. **Compaction interaction**: If `conflict_index` scans into compacted log range, does
   `term()` return `Err(StorageError::Compacted)`? If so, the function returns `(i, None)`
   with the compacted point. Callers may need to handle this gracefully. Should the
   function return `first_index()` instead to avoid returning a compacted index?

3. **Monotonicity assumption**: The scan's correctness depends on log terms being
   non-decreasing. Is this invariant stated and proved in the formal model, or assumed?
   (It is `LogUnstable`'s monotonicity property but not yet linked to `find_conflict_by_term`.)

4. **Test coverage**: There do not appear to be dedicated unit tests for this function.
   Are there integration tests that exercise the fast-reject path?

---

## Proposed Lean Properties

The following properties would be worth proving in a `FindConflictByTerm.lean` file:

1. **Result is in range**: `result_index ≤ index` (when `index ≤ last`).
2. **Term bound**: `result_term ≤ term` (when result is `Some`).
3. **Maximality**: For all `j ∈ (result_index, index]`, `log_term j > term`.
4. **Termination**: The scan terminates (provable from the non-decreasing term invariant
   and the fact that index 0 always has term 0).
5. **Identity on match**: If `log_term index ≤ term`, then `result_index = index`.
6. **Out-of-range early return**: If `index > last_index`, result is `(index, None)`.

A Lean model would use a pure log function `logTerm : Nat → Option Nat` and define
`findConflictByTerm index term` by well-founded recursion on `index`.

---

*Generated by 🔬 Lean Squad (Run 66) — automated formal verification for `dsyme/raft-lean-squad`.*
