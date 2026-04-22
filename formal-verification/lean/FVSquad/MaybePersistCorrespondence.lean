import FVSquad.MaybePersist

/-!
# MaybePersist Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `maybe_persist` and
`maybe_persist_snap` via `#guard` assertions that run the Lean model on concrete
test cases at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases here are mirrored in
`src/raft_log.rs::test_maybe_persist_correspondence` (Rust source side).
Both sides must produce the same `expected` Boolean value on the same inputs.

- **Lean side**: `#guard` evaluates the Lean model at lake-build time.
- **Rust side**: `assert_eq!` in the test verifies at `cargo test` time.

Together they demonstrate that the Lean model and the Rust implementation
agree on all 15 correspondence cases.

## Test fixtures

### `logTerm` fixture for `maybePersist` tests

We model a log with entries at indices 4, 5, 6 with terms 1, 2, 3 respectively,
stored in a log starting after a snapshot at index 3.  This mirrors the Rust
fixture constructed by `make_persist_log(3, 1, &[(4,1),(5,2),(6,3)])`.

```
  index:   0   1   2   3   [snap]   4   5   6
  term:    -   -   -   3            1   2   3
  persisted = 3 (from snapshot)
  first_update_index = 7 (offset after stabilising entries 4–6)
```

### `maybePersistSnap` fixture

Uses `persisted = 3`, `committed = 6`, `first_update_index = 7`
(same setup but snap variant only checks `index > persisted`).

## Case table

| ID | persisted | fui | logTerm(idx) | call(index, term) | expected | Guard failing |
|----|-----------|-----|--------------|-------------------|----------|---------------|
| 1  | 3 | 7 | term(5)=2 | (5, 2) | true  | all pass |
| 2  | 3 | 7 | term(5)=2 | (3, 1) | false | guard 1: 3 ≤ 3 |
| 3  | 3 | 7 | term(5)=2 | (7, 3) | false | guard 2: 7 ≥ 7 |
| 4  | 3 | 7 | term(5)=2 | (5,99) | false | guard 3: term mismatch |
| 5  | 3 | 7 | term(4)=1 | (4, 1) | true  | all pass |
| 6  | 3 | 7 | term(4)=1 | (2, 1) | false | guard 1: 2 ≤ 3 |
| 7  | 3 | 7 | term(6)=3 | (8, 3) | false | guard 2: 8 > 7 |
| 8  | 3 | 7 | term(6)=3 | (6, 3) | true  | all pass |
| 9  | 3 | 7 | term(6)=3 | (6, 1) | false | guard 3: wrong term |
| 10 | 5 | 7 | term(5)=2 | (5, 2) | false | guard 1: 5 ≤ 5 (idempotent) |
| 11 | 3 | 7 | term(5)=2 | (5, 2) | true  | snap: 5 > 3 → true |
| 12 | 5 | 7 | –          | snap(5) | false | snap: 5 ≤ 5 |
| 13 | 6 | 7 | –          | snap(5) | false | snap: 5 ≤ 6 |
| 14 | 3 | 7 | –          | snap(4) | true  | snap: 4 > 3 → true |
| 15 | 0 | 7 | –          | snap(1) | true  | snap: 1 > 0 → true |

-/

open FVSquad.MaybePersist

/-! ## Log-term fixture -/

/-- Term function mirroring the Rust test log: entries at indices 4, 5, 6
    with terms 1, 2, 3 respectively.  All other indices return 0. -/
private def testLogTerm : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | _ => 0

/-! ## `maybePersist` cases (IDs 1–10) -/

-- **Case 1**: All three guards pass → true, persisted advances to 5
#guard (maybePersist 3 7 testLogTerm 5 2).2 == true
#guard (maybePersist 3 7 testLogTerm 5 2).1 == 5

-- **Case 2**: Guard 1 fails — index (3) not strictly greater than persisted (3) → false
#guard (maybePersist 3 7 testLogTerm 3 1).2 == false
#guard (maybePersist 3 7 testLogTerm 3 1).1 == 3

-- **Case 3**: Guard 2 fails — index (7) equals first_update_index (7), not strictly less → false
#guard (maybePersist 3 7 testLogTerm 7 3).2 == false

-- **Case 4**: Guard 3 fails — term mismatch (logTerm 5 = 2, but term arg = 99) → false
#guard (maybePersist 3 7 testLogTerm 5 99).2 == false

-- **Case 5**: All guards pass at index 4 → true, persisted advances to 4
#guard (maybePersist 3 7 testLogTerm 4 1).2 == true
#guard (maybePersist 3 7 testLogTerm 4 1).1 == 4

-- **Case 6**: Guard 1 fails — index (2) below persisted (3) → false
#guard (maybePersist 3 7 testLogTerm 2 1).2 == false

-- **Case 7**: Guard 2 fails — index (8) exceeds first_update_index (7) → false
#guard (maybePersist 3 7 testLogTerm 8 3).2 == false

-- **Case 8**: All guards pass at index 6 → true, persisted advances to 6
#guard (maybePersist 3 7 testLogTerm 6 3).2 == true
#guard (maybePersist 3 7 testLogTerm 6 3).1 == 6

-- **Case 9**: Guard 3 fails — wrong term for index 6 (logTerm 6 = 3, arg = 1) → false
#guard (maybePersist 3 7 testLogTerm 6 1).2 == false

-- **Case 10**: Guard 1 fails after prior advance — idempotent: persisted=5 → call(5,2) = false
#guard (maybePersist 5 7 testLogTerm 5 2).2 == false

/-! ## `maybePersistSnap` cases (IDs 11–15) -/

-- **Case 11**: index (5) > persisted (3) → true, persisted advances to 5
#guard (maybePersistSnap 3 5).2 == true
#guard (maybePersistSnap 3 5).1 == 5

-- **Case 12**: index (5) = persisted (5) → false (not strictly greater)
#guard (maybePersistSnap 5 5).2 == false

-- **Case 13**: index (5) < persisted (6) → false
#guard (maybePersistSnap 6 5).2 == false

-- **Case 14**: index (4) > persisted (3) → true
#guard (maybePersistSnap 3 4).2 == true
#guard (maybePersistSnap 3 4).1 == 4

-- **Case 15**: index (1) > persisted (0) → true (from zero)
#guard (maybePersistSnap 0 1).2 == true
