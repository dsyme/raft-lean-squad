# Informal Specification: `RaftLog::find_conflict`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**Source**: `src/raft_log.rs`, lines 195–216

---

## Purpose

`find_conflict` scans a contiguous slice of log entries (provided by a leader during an
`AppendEntries` RPC) looking for the **first entry whose term does not match** the
corresponding entry already in the log.  If such a mismatch is found, the conflicting
entry's index is returned so that the caller knows where to start overwriting.  If every
entry in the slice is consistent with the local log (or the slice is empty), the function
returns **0** as a sentinel meaning "no conflict".

Informally: *return the index of the first entry the log disagrees with, or 0 if the log
agrees with the entire slice*.

---

## Preconditions

1. The first entry in the slice **must** have an index equal to some agreed-upon starting
   point `from` (documented in the caller contracts).
2. Entry indices in the slice are **strictly increasing** (contiguous, no gaps or
   duplicates).
3. All entry indices are **positive** (> 0).  Index 0 is reserved as the
   "no-conflict" sentinel returned by this function, so no valid entry may have index 0.

---

## Core operation

```
match_term(idx, term) = true   iff   log.term(idx) == Some(term)
```

```
find_conflict(ents):
  for e in ents:
    if !match_term(e.index, e.term): return e.index
  return 0
```

---

## Postconditions

**P1 — Empty:** `find_conflict([]) = 0`.

**P2 — No conflict:** If `find_conflict(ents) = 0`, then for every entry `e` in `ents`,
`match_term(e.index, e.term) = true`.  (Requires the positive-index precondition, since 0
would otherwise be ambiguous with the sentinel.)

**P3 — Conflict found:** If `find_conflict(ents) ≠ 0`, then there exists an entry `e ∈
ents` with `e.index = find_conflict(ents)` such that `match_term(e.index, e.term) =
false`.

**P4 — Prefix matches:** If `ents = pre ++ [e] ++ rest` where every entry in `pre`
matches the log and `e` does not match, then `find_conflict(ents) = e.index`.  In other
words, the result is the *first* mismatch (not just any mismatch).

**P5 — Matching prefix is transparent:** If every entry in a prefix `pre` matches, then
`find_conflict(pre ++ suf) = find_conflict(suf)`.  The function "skips over" matching
entries.

**P6 — Singleton match:** `find_conflict([e]) = 0` when `match_term(e.index, e.term) = true`.

**P7 — Singleton mismatch:** `find_conflict([e]) = e.index` when `match_term(e.index,
e.term) = false`.

---

## Invariants / structural properties

- The result is always an element of `{e.index | e ∈ ents} ∪ {0}`.
- If every entry matches, the result is 0.
- If any entry mismatches, the result equals the index of the **first** (lowest-position
  in the slice) mismatching entry.

---

## Edge cases

| Scenario | Result |
|----------|--------|
| Empty `ents` | 0 |
| All entries match | 0 |
| First entry mismatches | first entry's index |
| All entries mismatch | first entry's index |
| Entries extend beyond existing log (no `match_term` hit) | first new entry's index |

---

## Concrete examples (from test suite)

Previous log: `[(1,1), (2,2), (3,3)]` (index, term).

| Entries provided | Expected result |
|-----------------|----------------|
| `[]` | 0 |
| `[(1,1),(2,2),(3,3)]` | 0 (all match) |
| `[(3,3),(4,4),(5,4)]` | 4 (first new/mismatching index) |
| `[(1,4),(2,4)]` | 1 (first entry mismatches) |
| `[(2,1),(3,4),(4,4)]` | 2 (index 2 has term 1, log has term 2) |

---

## Inferred intent

The function is called during log reconciliation to determine the exact index from which
the follower's log must be overwritten.  Returning 0 is a special signal meaning
"nothing to do" (all entries are consistent, though there may be new entries to append at
the end; the caller handles this by checking whether the returned index exceeds the last
index).

The 0 sentinel is safe only because Raft log indices start at 1 (the initial dummy entry
has index 0 and is never sent in `AppendEntries`).

---

## Open questions

- **Q1:** Can `match_term(e.index, e.term)` return `false` when `e.index` exceeds
  `last_index()` (i.e., the entry is new, not conflicting)?  Answer: yes — `term(idx)`
  returns `Err` for out-of-range indices, and `match_term` treats `Err` as `false`.  So
  new entries (beyond the log) are treated the same as conflicting entries by this
  function; the caller distinguishes them.
- **Q2:** The docs say the first entry index must equal `from`.  Is this formally checked?
  Answer: No — it is a caller precondition, not runtime-checked.  The Lean model assumes
  it as a precondition where it matters.
