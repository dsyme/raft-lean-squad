import FVSquad.JointVote

/-!
# JointVote Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `Configuration::vote_result`
in `src/quorum/joint.rs` (the joint-quorum vote combinator).  Each `#guard` assertion
runs the Lean model (`jointVoteResult`) on a concrete test case and verifies the
result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/joint_vote/cases.json` are
mirrored both here (Lean model side) and in
`src/quorum/joint.rs::test_joint_vote_result_correspondence`
(Rust source side).  Both sides must produce the same `expected` VoteResult on the same
`(incoming_voters, outgoing_voters, yes_ids, no_ids)` input.

- **Lean side**: `#guard` evaluates
  `jointVoteResult incoming outgoing (checkFn yes_ids no_ids) == expected`
  at lake-build time.  A compile error means the Lean model gives a different answer.
- **Rust side**: `assert_eq!` in the test function verifies the same expected values at
  `cargo test` time.

Together they demonstrate that the Lean `jointVoteResult` model and the Rust
`Configuration::vote_result` agree on all 15 correspondence cases covering all 9
combinations of the two constituent majority-quorum sub-results.

## Coverage

All 9 combinations of incoming × outgoing VoteResult:

| incoming \ outgoing | Won | Lost | Pending |
|---------------------|-----|------|---------|
| **Won**             | ✅ Case 1 | ✅ Case 2 | ✅ Case 3 |
| **Lost**            | ✅ Case 4 | ✅ Case 5 | ✅ Case 6 |
| **Pending**         | ✅ Case 7 | ✅ Case 8 | ✅ Case 9 |

Plus non-joint / degenerate cases:

| Case | Notes |
|------|-------|
| 10 | Empty incoming (convention: Won), outgoing Won → Won |
| 11 | Non-joint: non-empty incoming Won, empty outgoing (convention: Won) → Won |
| 12 | Non-joint: incoming Lost, empty outgoing → Lost |
| 13 | Non-joint: incoming Pending, empty outgoing → Pending |
| 14 | Even-sized quorums (2+2) both Win → Won |
| 15 | 5-voter incoming Won, 4-voter outgoing Lost → Lost |

## Correspondence level: **exact**

`jointVoteResult` directly mirrors the Rust `Configuration::vote_result`: it calls
`voteResult` (= `MajorityConfig::vote_result`) on each half and combines via the same
match table.  No abstraction or approximation is needed.

## Source

- Lean model: `FVSquad/JointVote.lean` — `jointVoteResult`, `combineVotes`
- Rust source: `src/quorum/joint.rs` — `Configuration::vote_result`
- Informal spec: `formal-verification/specs/joint_vote_informal.md`
-/

namespace FVSquad.JointVoteCorrespondence

/-! ## Helper: build a check function from yes/no ID lists -/

/-- Build a check function from lists of yes-voter and no-voter IDs.
    Voters not in either list return `none` (not yet voted / missing). -/
private def checkFn (yes_ids no_ids : List Nat) : Nat → Option Bool :=
  fun v =>
    if yes_ids.contains v then some true
    else if no_ids.contains v then some false
    else none

-- Sanity checks for checkFn
#guard checkFn [1,2] [3] 1 == some true
#guard checkFn [1,2] [3] 3 == some false
#guard checkFn [1,2] [3] 9 == none

/-!
## Cases 1–9: all 9 combinations of (incoming result) × (outgoing result)

Sub-quorum setup (majority n = n/2 + 1):
- `[1,2,3]`: majority=2.  Won if ≥2 yes; Pending if yes<2 and yes+missing≥2; Lost otherwise.
- `[4,5]`:   majority=2.  Won if both yes; Pending if one yes+one missing; Lost if both no.

*Important*: `checkFn yes_ids no_ids` is applied globally to all voter IDs across both
sub-quorums, so IDs are chosen carefully to produce the intended per-sub-quorum result.
-/

/-! ### Case 1: incoming=Won, outgoing=Won → joint=Won -/

-- incoming: [1,2,3] with yes={1,2,3} → Won (3≥majority(3)=2)
-- outgoing: [4,5]   with yes={4,5}   → Won (2≥majority(2)=2)
-- yes_ids = {1,2,3,4,5} so all voters across both quorums vote yes
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [1,2,3,4,5] [])
    == VoteResult.Won

/-! ### Case 2: incoming=Won, outgoing=Lost → joint=Lost -/

-- incoming: [1,2,3] with yes={1,2},missing={3}  → Won (2≥majority(3)=2)
-- outgoing: [4,5]   with no={4,5}               → Lost (0+0=0 < majority(2)=2)
-- yes_ids = {1,2}, no_ids = {4,5}
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [1,2] [4,5])
    == VoteResult.Lost

/-! ### Case 3: incoming=Won, outgoing=Pending → joint=Pending -/

-- incoming: [1,2,3] with yes={1,2},missing={3}  → Won (2≥2)
-- outgoing: [4,5]   with yes={4},missing={5}    → Pending (1<2 but 1+1=2≥2)
-- yes_ids = {1,2,4}, no_ids = {} (voters 3 and 5 are missing)
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [1,2,4] [])
    == VoteResult.Pending

/-! ### Case 4: incoming=Lost, outgoing=Won → joint=Lost -/

-- incoming: [1,2,3] with no={1,2,3} → Lost (0+0<2)
-- outgoing: [4,5]   with yes={4,5}  → Won
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [4,5] [1,2,3])
    == VoteResult.Lost

/-! ### Case 5: incoming=Lost, outgoing=Lost → joint=Lost -/

-- incoming: [1,2,3] with no={1,2,3} → Lost
-- outgoing: [4,5]   with no={4,5}   → Lost
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [] [1,2,3,4,5])
    == VoteResult.Lost

/-! ### Case 6: incoming=Lost, outgoing=Pending → joint=Lost -/

-- incoming: [1,2,3] with no={1,2,3} → Lost
-- outgoing: [4,5]   with yes={4},missing={5} → Pending
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [4] [1,2,3])
    == VoteResult.Lost

/-! ### Case 7: incoming=Pending, outgoing=Won → joint=Pending -/

-- incoming: [1,2,3] with yes={1},missing={2},no={3} → Pending (1<2 but 1+1=2≥2)
-- outgoing: [4,5]   with yes={4,5} → Won
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [1,4,5] [3])
    == VoteResult.Pending

/-! ### Case 8: incoming=Pending, outgoing=Lost → joint=Lost -/

-- incoming: [1,2,3] with yes={1},missing={2},no={3} → Pending
-- outgoing: [4,5]   with no={4,5} → Lost
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [1] [3,4,5])
    == VoteResult.Lost

/-! ### Case 9: incoming=Pending, outgoing=Pending → joint=Pending -/

-- incoming: [1,2,3] with yes={1},missing={2},no={3} → Pending
-- outgoing: [4,5]   with yes={4},missing={5} → Pending
#guard jointVoteResult [1,2,3] [4,5]
    (checkFn [1,4] [3])
    == VoteResult.Pending

/-!
## Cases 10–13: non-joint / degenerate configurations
-/

/-! ### Case 10: empty incoming (convention Won), outgoing Won → Won -/

-- incoming: [] → voteResult [] _ = Won (empty-config convention)
-- outgoing: [4,5] with yes={4,5} → Won
#guard jointVoteResult [] [4,5]
    (checkFn [4,5] [])
    == VoteResult.Won

/-! ### Case 11: non-joint (empty outgoing), incoming Won → Won -/

-- incoming: [1] with yes={1} → Won
-- outgoing: [] → Won (convention)
#guard jointVoteResult [1] []
    (checkFn [1] [])
    == VoteResult.Won

/-! ### Case 12: non-joint (empty outgoing), incoming Lost → Lost -/

-- incoming: [1] with no={1} → Lost
-- outgoing: [] → Won (convention)
-- combineVotes Lost Won = Lost
#guard jointVoteResult [1] []
    (checkFn [] [1])
    == VoteResult.Lost

/-! ### Case 13: non-joint (empty outgoing), incoming Pending → Pending -/

-- incoming: [1] with missing={1} → Pending (0 yes + 1 missing = 1 ≥ majority(1)=1)
-- outgoing: [] → Won (convention)
-- combineVotes Pending Won = Pending
#guard jointVoteResult [1] []
    (checkFn [] [])
    == VoteResult.Pending

/-!
## Cases 14–15: larger quorums
-/

/-! ### Case 14: 2-voter + 2-voter, both Win → Won -/

-- incoming: [1,2] with yes={1,2} → Won (2≥majority(2)=2)
-- outgoing: [3,4] with yes={3,4} → Won
#guard jointVoteResult [1,2] [3,4]
    (checkFn [1,2,3,4] [])
    == VoteResult.Won

/-! ### Case 15: 5-voter incoming Won, 4-voter outgoing Lost → Lost -/

-- incoming: [1,2,3,4,5] with yes={1,2,3} → Won (3≥majority(5)=3)
-- outgoing: [6,7,8,9]   with no={6,7,8,9} → Lost (0+0<majority(4)=3)
#guard jointVoteResult [1,2,3,4,5] [6,7,8,9]
    (checkFn [1,2,3] [6,7,8,9])
    == VoteResult.Lost

end FVSquad.JointVoteCorrespondence
