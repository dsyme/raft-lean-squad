# Log Ordering — Informal Specification

> **Target**: `is_up_to_date` + `find_conflict_by_term` in `src/raft_log.rs`  
> 🔬 *Lean Squad — informal spec for formal verification target 8.*

---

## Purpose

Two functions in `RaftLog` control how Raft nodes compare and reconcile their logs:

1. **`is_up_to_date(last_index, term) → bool`**: decides whether a candidate's log is
   "at least as up-to-date" as the current node's log. Used in election voting: a node
   only votes for a candidate whose log is at least as up-to-date as its own.

2. **`find_conflict_by_term(index, term) → (u64, Option<u64>)`**: scans backward from
   `index` to find the last log entry with term ≤ `term`. Used after a rejected
   AppendEntries to efficiently skip back to the conflict point.

---

## `is_up_to_date`

### Rust source

```rust
pub fn is_up_to_date(&self, last_index: u64, term: u64) -> bool {
    term > self.last_term() ||
    (term == self.last_term() && last_index >= self.last_index())
}
```

### Preconditions

- No formal preconditions (always safe to call).

### Postconditions

Returns `true` iff the candidate log with `(last_index, term)` is at least as
up-to-date as the current log with `(self.last_index(), self.last_term())`:

- **Higher term always wins**: if `term > self.last_term()`, return `true`.
- **Lower term always loses**: if `term < self.last_term()`, return `false`.
- **Same term: length decides**: if `term == self.last_term()`, return
  `last_index >= self.last_index()`.

### Invariants

The relation defines a **total preorder** on `(lastIndex, lastTerm)` pairs:
- **Reflexive**: every log is up-to-date with itself.
- **Total**: for any two logs, at least one is up-to-date wrt the other.
- **Transitive**: if A ≥ B and B ≥ C then A ≥ C.
- **Antisymmetric** (up to equality): if A ≥ B and B ≥ A then they have the same
  `(lastIndex, lastTerm)`.

This is equivalent to the **lexicographic order** on `(term, lastIndex)` pairs.

### Edge cases

- Empty log: `self.last_term() = 0`, `self.last_index() = 0`. Any non-empty log
  is up-to-date wrt the empty log.
- Equal logs (same `lastIndex` and `lastTerm`): `is_up_to_date` returns `true`
  (reflexive).
- Single-entry log: behaves normally — term and index are both well-defined.

### Examples

| `(last_index, term)` | `(log_last_index, log_last_term)` | Result |
|---|---|---|
| `(5, 3)` | `(4, 2)` | `true` — higher term |
| `(5, 2)` | `(4, 3)` | `false` — lower term |
| `(5, 3)` | `(4, 3)` | `true` — same term, longer |
| `(4, 3)` | `(5, 3)` | `false` — same term, shorter |
| `(5, 3)` | `(5, 3)` | `true` — identical |

### Inferred intent

This is the **Raft "election restriction"** (Section 5.4 of the Raft paper). It
ensures that only candidates with complete information about all committed entries
can be elected. The total preorder property is essential: it means every election
has a single "most up-to-date" candidate in any quorum.

### Open questions

- Does this function correctly handle the initial state where the log is empty
  (`last_index() = 0`, `last_term() = 0`)? The Lean spec assumes index 0 is a
  valid floor.
- Is the term here always the term of the *last entry*, or could it be the
  *current term* of the node? (In the Rust code, it's the term of the last log
  entry.)

---

## `find_conflict_by_term`

### Rust source

```rust
pub fn find_conflict_by_term(&self, index: u64, term: u64) -> (u64, Option<u64>) {
    let mut conflict_index = index;
    let last_index = self.last_index();
    if index > last_index {
        warn!(...);
        return (index, None);
    }
    loop {
        match self.term(conflict_index) {
            Ok(t) => {
                if t > term { conflict_index -= 1 }
                else { return (conflict_index, Some(t)); }
            }
            Err(_) => return (conflict_index, None),
        }
    }
}
```

### Preconditions

- `index ≤ self.last_index()` (documented; violation produces a warning and
  returns `(index, None)` early — this is the `index > last_index` guard).

### Postconditions

Let `result = (j, term_opt)`:
1. **Range**: `j ≤ index` — we only scan backward.
2. **Found case**: `term_opt = Some(t)` and `t ≤ term` — the entry at `j` has
   term at most `term`.
3. **Maximality**: for all `k` with `j < k ≤ index`, the term at `k` is `> term`.
4. **Error case**: `term_opt = None` means the lookup for `j` failed (out of range
   or compacted). In this case `j` may not have a valid term.

### Invariants

- The scan always terminates because `conflict_index` strictly decreases on each
  "term too high" iteration.
- If `index = 0`, the loop would underflow `conflict_index -= 1` (Rust subtraction
  on `u64`). This is a potential edge case: if the log's first entry already has
  term > `term`, the loop would eventually try `conflict_index = 0` and then
  decrement past zero. In practice this is prevented by the log always containing
  index 0 (the initial dummy entry with term 0).

### Edge cases

- `term = 0`: the loop will scan backward until it finds an entry with term 0
  (if it exists) or hits the floor. If all entries have term ≥ 1, the scan will
  reach index 0.
- `index > last_index()`: early return with `(index, None)` (out-of-range guard).
- All entries in `[1..index]` have term > `queryTerm`: the function scans all the
  way to index 0 and returns `(0, ...)`.

### Examples

Log with terms `[_, 1, 2, 3, 3, 4]` (index 1..5):

| `index` | `term` | result `j` |
|---------|--------|------------|
| 5 | 3 | 4 (term[4]=3 ≤ 3) |
| 5 | 4 | 5 (term[5]=4 ≤ 4) |
| 5 | 1 | 1 (term[1]=1 ≤ 1) |
| 2 | 1 | 1 (term[1]=1 ≤ 1) |
| 1 | 0 | 0 (no entry with term ≤ 0) |

### Inferred intent

This function enables **"fast log matching"** — when a follower rejects an
AppendEntries (because its log diverges from the leader's), it can report back the
`(conflict_index, conflict_term)` pair. The leader can then use this to skip
backward to the beginning of the conflicting term, rather than decrementing
`nextIndex` one at a time. This is the "Raft optimization" described in Section 5.3
of the paper and Section 9 of the extended version.

### Open questions

- What happens when `conflict_index` reaches 0 with term > `queryTerm`? The code
  would do `conflict_index -= 1` on a `u64`, wrapping to `u64::MAX`. This appears
  to be a potential bug for malformed logs. In practice, logs always contain a
  dummy entry at index 0 with term 0, preventing this — but this invariant is not
  checked by the function itself.
- Is `find_conflict_by_term` supposed to be called with `index ≤ last_index()`? The
  warning suggests it's a defensive check, but callers should ensure this.
