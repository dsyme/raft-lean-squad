import FVSquad.IsUpToDate

/-!
# IsUpToDate Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `is_up_to_date`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/is_up_to_date/cases.json` are
mirrored both here (Lean model side) and in `src/raft_log.rs::test_is_up_to_date_correspondence`
(Rust source side).  Both sides must produce the same `expected` Boolean value on the same
`(voter_term, voter_index, cand_term, cand_index)` input.

- **Lean side**: `#guard` evaluates `isUpToDate voter cand_term cand_index == expected`
  at lake-build time.  A compile error means the Lean model gives a different answer.
- **Rust side**: `assert_eq!` in the test function verifies the same expected values at
  `cargo test` time.

Together they demonstrate that the Lean model and the Rust implementation agree on all
12 correspondence cases.

## What is checked

For each case we check one observable property:

- **Return value**: `isUpToDate { term := voter_term, index := voter_index } cand_term cand_index == expected`

The function is pure Boolean-valued so this completely characterises its behaviour.

## Test cases (12 total)

Cases 1–9 mirror the 9 cases in the existing Rust unit test `test_is_up_to_date`,
which uses a log of entries `[(1,1),(2,2),(3,3)]` → `(last_term=3, last_index=3)`.
Cases 10–12 exercise additional edge cases.

| ID | voter_term | voter_index | cand_term | cand_index | expected | Property |
|----|-----------|------------|-----------|-----------|---------|---------|
| 1  | 3 | 3 | 4 | 2 | true | IU3 — higher cand term beats lower index |
| 2  | 3 | 3 | 4 | 3 | true | IU3 — higher cand term wins |
| 3  | 3 | 3 | 4 | 4 | true | IU3 — higher cand term wins |
| 4  | 3 | 3 | 2 | 2 | false | IU4 — lower cand term loses |
| 5  | 3 | 3 | 2 | 3 | false | IU4 — lower cand term loses |
| 6  | 3 | 3 | 2 | 4 | false | IU4 — lower cand term loses even with higher index |
| 7  | 3 | 3 | 3 | 2 | false | IU6 — same term, shorter cand log loses |
| 8  | 3 | 3 | 3 | 3 | true  | IU2 — same term, equal length (isUpToDate_refl) |
| 9  | 3 | 3 | 3 | 4 | true  | IU5 — same term, longer cand log wins |
| 10 | 0 | 0 | 0 | 0 | true  | empty voter log: any cand is up-to-date |
| 11 | 5 | 10 | 5 | 9 | false | same term, shorter cand index |
| 12 | 5 | 10 | 6 | 0 | true  | higher cand term wins regardless of index |
-/

namespace FVSquad.IsUpToDateCorrespondence

/-! ## Voter log fixtures -/

private def voter33  : LogId := { term := 3, index := 3 }   -- log [(1,1),(2,2),(3,3)]
private def voter00  : LogId := { term := 0, index := 0 }   -- empty log
private def voter510 : LogId := { term := 5, index := 10 }  -- log with last=(term=5,idx=10)

/-! ## Cases 1–3: higher cand term → always true (IU3) -/

-- Case 1: higher term beats lower index
#guard isUpToDate voter33 4 2 == true

-- Case 2: higher term wins (same index)
#guard isUpToDate voter33 4 3 == true

-- Case 3: higher term wins (higher index)
#guard isUpToDate voter33 4 4 == true

/-! ## Cases 4–6: lower cand term → always false (IU4) -/

-- Case 4: lower term loses (lower index)
#guard isUpToDate voter33 2 2 == false

-- Case 5: lower term loses (same index)
#guard isUpToDate voter33 2 3 == false

-- Case 6: lower term loses even with higher index
#guard isUpToDate voter33 2 4 == false

/-! ## Cases 7–9: equal term — decided by index comparison -/

-- Case 7: same term, shorter cand log → false (IU6)
#guard isUpToDate voter33 3 2 == false

-- Case 8: same term, equal length → true (IU2 isUpToDate_refl)
#guard isUpToDate voter33 3 3 == true

-- Case 9: same term, longer cand log → true (IU5)
#guard isUpToDate voter33 3 4 == true

/-! ## Cases 10–12: additional edge cases -/

-- Case 10: empty voter log → every candidate is at least as up-to-date
#guard isUpToDate voter00 0 0 == true

-- Case 11: same term, shorter cand index → false
#guard isUpToDate voter510 5 9 == false

-- Case 12: higher cand term with lower index → true (term dominates)
#guard isUpToDate voter510 6 0 == true

end FVSquad.IsUpToDateCorrespondence
