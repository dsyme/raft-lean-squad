import FVSquad.CommittedIndex

/-!
# CommittedIndex Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `committed_index`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/committed_index/cases.json` are
mirrored both here (Lean model side) and in
`src/quorum/majority.rs::test_committed_index_correspondence`
(Rust source side).  Both sides must produce the same `expected` index value on
the same `(voters, acked_map)` input.

- **Lean side**: `#guard` evaluates `committedIndex voters acked == expected`
  at lake-build time.  A compile error means the Lean model gives a different answer.
- **Rust side**: `assert_eq!` in the test function verifies the same expected values at
  `cargo test` time.

Together they demonstrate that the Lean model and the Rust `Configuration::committed_index`
agree (for `use_group_commit = false`) on all 8 correspondence cases.

## What is checked

For each case we check one observable property:

- **Return value**: `committedIndex voters (makeAcked acked_pairs) == expected_index`

## Modelling note

The Lean `AckedFn` is `Nat → Nat`.  Missing voters default to `0`, matching Rust's
`l.acked_index(*v).unwrap_or_default()` call in `majority.rs`.

The `use_group_commit = false` path of the Rust function is exactly the Lean model.
The group-commit extension is not tested here.

## Test cases (8 total)

| ID | voters | acked_map | sorted_desc | majority | expected |
|----|--------|-----------|-------------|---------|---------|
| 1  | [1] | {1→5} | [5] | 1 | 5 |
| 2  | [1,2] | {1→5,2→3} | [5,3] | 2 | 3 |
| 3  | [1,2,3] | {1→2,2→4,3→6} | [6,4,2] | 2 | 4 |
| 4  | [1,2,3] | {1→2,2→2,3→2} | [2,2,2] | 2 | 2 |
| 5  | [1,2,3] | {1→0,2→0,3→0} | [0,0,0] | 2 | 0 |
| 6  | [1,2,3,4,5] | {1→1,…,5→5} | [5,4,3,2,1] | 3 | 3 |
| 7  | [1,2] | {1→10} | [10,0] | 2 | 0 |
| 8  | [1,2,3] | {1→10,2→10,3→10} | [10,10,10] | 2 | 10 |
-/

open FVSquad.CommittedIndex

namespace FVSquad.CommittedIndexCorrespondence

/-! ## Helper: build an `AckedFn` from a finite association list -/

/-- Build an `AckedFn` from a list of `(voter_id, acked_index)` pairs.
    Missing entries default to `0`, mirroring Rust's `l.acked_index(*v).unwrap_or_default()`. -/
private def makeAcked (pairs : List (Nat × Nat)) : AckedFn :=
  fun v => ((pairs.find? fun p => p.1 == v).map Prod.snd).getD 0

/-! ## Sanity checks for `makeAcked` -/

-- voter 1 → 5
#guard makeAcked [(1,5),(2,3)] 1 == 5
-- voter 2 → 3
#guard makeAcked [(1,5),(2,3)] 2 == 3
-- voter 3 not in list → default 0
#guard makeAcked [(1,5),(2,3)] 3 == 0

/-! ## Case 1: Single voter, acked=5 → 5

    voters=[1], acked={1→5}
    sortedAcked=[5], majority(1)=1, result=sorted[0]=5 -/

#guard committedIndex [1] (makeAcked [(1,5)]) == 5

/-! ## Case 2: Two voters, acked={1→5, 2→3} → 3

    sortedAcked=[5,3], majority(2)=2, result=sorted[1]=3 -/

#guard committedIndex [1,2] (makeAcked [(1,5),(2,3)]) == 3

/-! ## Case 3: Three voters, acked={1→2, 2→4, 3→6} → 4

    sortedAcked=[6,4,2], majority(3)=2, result=sorted[1]=4 -/

#guard committedIndex [1,2,3] (makeAcked [(1,2),(2,4),(3,6)]) == 4

/-! ## Case 4: Three voters, all acked=2 → 2

    sortedAcked=[2,2,2], majority(3)=2, result=sorted[1]=2 -/

#guard committedIndex [1,2,3] (makeAcked [(1,2),(2,2),(3,2)]) == 2

/-! ## Case 5: Three voters, all acked=0 → 0

    sortedAcked=[0,0,0], majority(3)=2, result=sorted[1]=0 -/

#guard committedIndex [1,2,3] (makeAcked [(1,0),(2,0),(3,0)]) == 0

/-! ## Case 6: Five voters, acked={1→1,2→2,3→3,4→4,5→5} → 3

    sortedAcked=[5,4,3,2,1], majority(5)=3, result=sorted[2]=3 -/

#guard committedIndex [1,2,3,4,5] (makeAcked [(1,1),(2,2),(3,3),(4,4),(5,5)]) == 3

/-! ## Case 7: Two voters, voter 2 missing from acked map → 0

    voters=[1,2], acked={1→10}; voter 2 defaults to 0
    sortedAcked=[10,0], majority(2)=2, result=sorted[1]=0 -/

#guard committedIndex [1,2] (makeAcked [(1,10)]) == 0

/-! ## Case 8: Three voters, all acked=10 → 10

    sortedAcked=[10,10,10], majority(3)=2, result=sorted[1]=10 -/

#guard committedIndex [1,2,3] (makeAcked [(1,10),(2,10),(3,10)]) == 10

end FVSquad.CommittedIndexCorrespondence
