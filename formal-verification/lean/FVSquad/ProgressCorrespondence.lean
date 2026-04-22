import FVSquad.Progress

/-!
# ProgressCorrespondence — Lean 4 Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Runtime correspondence tests (`#guard`) that verify the Lean model of
`Progress` agrees with the expected output of the Rust implementation
on representative inputs.

Source: `src/tracker/progress.rs`
Lean model: `FVSquad/Progress.lean`

## Methodology

Each `#guard` test encodes a concrete input and expected output drawn from
the Rust implementation's behaviour on the same values.  The Lean model is
evaluated at compile time via `#guard`; agreement confirms that the
functional model and the Rust code produce the same result on those inputs.

## Test fixtures

Tests cover:
- `maybeUpdate` (PR14–PR17, PR20): forward-progress on matched index
- `maybeDecrTo` in Replicate state (PR27–PR28): stale / non-stale
- `maybeDecrTo` in Probe/Snapshot state (PR31–PR33): stale / decrement paths
- `optimisticUpdate` (PR34–PR35): pessimistic next_idx advance
- `becomeProbe` / `becomeReplicate` (PR1–PR9): state transitions

Correspondence level: **abstraction** — the Lean model abstracts away
the `Inflights` ring buffer (replaced by `ins_full : Bool`) and overflow.

Invariant checks use `Nat.ble (matched + 1) next_idx` rather than
`decide (Progress.wf ...)` because `Progress.wf` is not marked `@[reducible]`.
-/

open FVSquad.Progress

namespace FVSquad.ProgressCorrespondence

-- ---------------------------------------------------------------------------
-- Helper instances for #guard tests
-- ---------------------------------------------------------------------------

instance : BEq ProgressState where
  beq a b := match a, b with
    | .Probe, .Probe | .Replicate, .Replicate | .Snapshot, .Snapshot => true
    | _, _ => false

instance : BEq Progress where
  beq a b :=
    a.matched == b.matched &&
    a.next_idx == b.next_idx &&
    a.state == b.state &&
    a.paused == b.paused &&
    a.pending_snapshot == b.pending_snapshot &&
    a.pending_request_snapshot == b.pending_request_snapshot &&
    a.recent_active == b.recent_active &&
    a.ins_full == b.ins_full

-- ---------------------------------------------------------------------------
-- Test fixtures
-- ---------------------------------------------------------------------------

/-- A Progress in Replicate state with matched=5, next_idx=6. -/
private def pReplicate : Progress :=
  { matched := 5, next_idx := 6, state := ProgressState.Replicate,
    paused := false, pending_snapshot := 0, pending_request_snapshot := 0,
    recent_active := true, ins_full := false }

/-- A Progress in Probe state with matched=3, next_idx=7. -/
private def pProbe : Progress :=
  { matched := 3, next_idx := 7, state := ProgressState.Probe,
    paused := false, pending_snapshot := 0, pending_request_snapshot := 0,
    recent_active := true, ins_full := false }

/-- A Progress in Snapshot state with matched=2, next_idx=3, pending_snapshot=10. -/
private def pSnapshot : Progress :=
  { matched := 2, next_idx := 3, state := ProgressState.Snapshot,
    paused := false, pending_snapshot := 10, pending_request_snapshot := 0,
    recent_active := true, ins_full := false }

-- wf helper: checks matched + 1 ≤ next_idx as a Bool
private def checkWf (p : Progress) : Bool := Nat.ble (p.matched + 1) p.next_idx

-- ---------------------------------------------------------------------------
-- maybeUpdate tests (PR14–PR17, PR20)
-- ---------------------------------------------------------------------------

-- n > matched: matched advances to n, returns true
#guard (pReplicate.maybeUpdate 8).2 == true
#guard (pReplicate.maybeUpdate 8).1.matched == 8
-- next_idx advances to max(6, 9) = 9
#guard (pReplicate.maybeUpdate 8).1.next_idx == 9
-- paused is cleared when matched advances
#guard (pReplicate.maybeUpdate 8).1.paused == false
-- wf preserved: matched + 1 = 9 ≤ 9 = next_idx
#guard checkWf (pReplicate.maybeUpdate 8).1

-- n ≤ matched: no change, returns false
#guard (pReplicate.maybeUpdate 5).2 == false
#guard (pReplicate.maybeUpdate 5).1.matched == 5
#guard (pReplicate.maybeUpdate 3).2 == false

-- For pProbe: matched=3, next_idx=7. n=10 > matched=3.
-- next_idx = max(7, 11) = 11
#guard (pProbe.maybeUpdate 10).1.next_idx == 11
-- n=4 > matched=3 but next_idx stays 7 (max(7,5)=7)
#guard (pProbe.maybeUpdate 4).1.next_idx == 7
-- wf preserved
#guard checkWf (pProbe.maybeUpdate 10).1

-- ---------------------------------------------------------------------------
-- maybeDecrTo in Replicate state (PR27–PR28)
-- ---------------------------------------------------------------------------

-- Stale: rejected < matched (rejected=4 < matched=5)
#guard (pReplicate.maybeDecrTo 4 3 INVALID_INDEX).2 == false
#guard (pReplicate.maybeDecrTo 4 3 INVALID_INDEX).1 == pReplicate

-- Stale: rejected = matched, no snapshot request
#guard (pReplicate.maybeDecrTo 5 4 INVALID_INDEX).2 == false
#guard (pReplicate.maybeDecrTo 5 4 INVALID_INDEX).1 == pReplicate

-- Non-stale: rejected > matched, no snapshot — next_idx := matched + 1 = 6
#guard (pReplicate.maybeDecrTo 7 3 INVALID_INDEX).2 == true
#guard (pReplicate.maybeDecrTo 7 3 INVALID_INDEX).1.next_idx == 6
-- wf preserved: matched=5, next_idx=6
#guard checkWf (pReplicate.maybeDecrTo 7 3 INVALID_INDEX).1

-- Non-stale with snapshot request: sets pending_request_snapshot
#guard (pReplicate.maybeDecrTo 5 0 1).2 == true
#guard (pReplicate.maybeDecrTo 5 0 1).1.pending_request_snapshot == 1

-- ---------------------------------------------------------------------------
-- maybeDecrTo in Probe state (PR31–PR32, PR33)
-- ---------------------------------------------------------------------------

-- Stale: next_idx (7) ≠ rejected + 1 (6) → no change
#guard (pProbe.maybeDecrTo 5 3 INVALID_INDEX).2 == false  -- 7 ≠ 5+1=6
#guard (pProbe.maybeDecrTo 5 3 INVALID_INDEX).1 == pProbe

-- Also stale when rejected + 1 > next_idx
#guard (pProbe.maybeDecrTo 9 3 INVALID_INDEX).2 == false  -- 7 ≠ 9+1=10

-- Fresh: next_idx (7) = rejected + 1 (6+1=7)
-- ni = min(6, match_hint+1) = min(6, 3+1) = min(6,4) = 4
-- ni' = max(4, matched+1) = max(4, 4) = 4
#guard (pProbe.maybeDecrTo 6 3 INVALID_INDEX).2 == true
#guard (pProbe.maybeDecrTo 6 3 INVALID_INDEX).1.next_idx == 4
#guard (pProbe.maybeDecrTo 6 3 INVALID_INDEX).1.paused == false
-- wf preserved: matched=3, next_idx=4
#guard checkWf (pProbe.maybeDecrTo 6 3 INVALID_INDEX).1

-- Fresh with large match_hint: ni = min(6, 10) = 6, ni' = max(6, 4) = 6
#guard (pProbe.maybeDecrTo 6 9 INVALID_INDEX).1.next_idx == 6

-- Fresh with match_hint = 0: ni = min(6,1) = 1, ni' = max(1,4) = 4 (clamped to matched+1)
#guard (pProbe.maybeDecrTo 6 0 INVALID_INDEX).1.next_idx == 4

-- ---------------------------------------------------------------------------
-- maybeDecrTo in Snapshot state (PR33 — snapshot handling)
-- ---------------------------------------------------------------------------

-- Stale in snapshot state: next_idx (3) ≠ rejected + 1 (5)
#guard (pSnapshot.maybeDecrTo 4 2 INVALID_INDEX).2 == false  -- 3 ≠ 4+1=5

-- Snapshot request sets pending_request_snapshot (when not already set)
#guard (pSnapshot.maybeDecrTo 4 2 7).2 == true
#guard (pSnapshot.maybeDecrTo 4 2 7).1.pending_request_snapshot == 7
-- wf preserved
#guard checkWf (pSnapshot.maybeDecrTo 4 2 7).1

-- ---------------------------------------------------------------------------
-- optimisticUpdate (PR34–PR35)
-- ---------------------------------------------------------------------------

-- next_idx := n + 1
#guard (pReplicate.optimisticUpdate 8).next_idx == 9
#guard (pProbe.optimisticUpdate 4).next_idx == 5
-- other fields unchanged
#guard (pReplicate.optimisticUpdate 8).matched == pReplicate.matched
#guard (pReplicate.optimisticUpdate 8).state == pReplicate.state
-- wf when n ≥ matched: matched=5, next_idx=6 ✓
#guard checkWf (pReplicate.optimisticUpdate 5)
-- matched=3, next_idx=4 ✓
#guard checkWf (pProbe.optimisticUpdate 3)

-- ---------------------------------------------------------------------------
-- State transition tests (PR1–PR9)
-- ---------------------------------------------------------------------------

-- becomeReplicate from Probe
#guard pProbe.becomeReplicate.state == ProgressState.Replicate
#guard pProbe.becomeReplicate.next_idx == pProbe.matched + 1  -- matched + 1 = 4
#guard checkWf pProbe.becomeReplicate

-- becomeProbe from Replicate
#guard pReplicate.becomeProbe.state == ProgressState.Probe
#guard pReplicate.becomeProbe.next_idx == pReplicate.matched + 1  -- 6
#guard checkWf pReplicate.becomeProbe

-- becomeProbe from Snapshot (next_idx = max(matched+1, pending_snapshot+1))
#guard pSnapshot.becomeProbe.state == ProgressState.Probe
-- matched=2, pending_snapshot=10: max(3, 11) = 11
#guard pSnapshot.becomeProbe.next_idx == 11
#guard checkWf pSnapshot.becomeProbe

-- becomeSnapshot sets pending_snapshot and state
#guard (pProbe.becomeSnapshot 15).state == ProgressState.Snapshot
#guard (pProbe.becomeSnapshot 15).pending_snapshot == 15
#guard checkWf (pProbe.becomeSnapshot 15)

end FVSquad.ProgressCorrespondence
