import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# RaftLog Term Dispatch — Lean 4 Specification

Formal specification of `RaftLog::term` and `RaftLog::match_term`
from `raft-rs` (`src/raft_log.rs`).

## Model scope and approximations

* **Types**: All indices and terms are `Nat` (Rust uses `u64`; u64 overflow not modelled).
* **Log abstraction**: The log is abstracted via `logTerm : Nat → Option Nat`, a combined
  partial function representing the composition of `unstable.maybe_term` (checked first)
  and `store.term` (fallback).  `none` models a compacted/unavailable store entry.
* **Out-of-range sentinel**: the Rust code returns `Ok(0)` for indices outside
  `[dummyIdx, lastIndex]`.  The Lean model returns `some 0` for such indices.
* **Dummy entry**: `dummyIdx = firstIndex - 1` is the Raft dummy entry (last compacted).
  It is in-range; its term comes from `logTerm` (typically `some 0` for a fresh log).
* **Panic paths**: the `fatal!` call for unexpected store errors is not modelled — we
  assume `logTerm` is well-behaved (no unexpected errors).
* **Error propagation**: `store.term` returning `Err(Compacted)` or `Err(Unavailable)`
  is modelled as `logTerm idx = none`.  `match_term` returns `false` in this case.
* **`firstIndex ≥ 1`**: required so `dummyIdx = firstIndex - 1` is a valid `Nat`.

🔬 *Lean Squad — auto-generated formal specification.*
-/

namespace FVSquad.RaftLogTerm

/-! ## Abstract log model -/

/-- Abstract model of a `RaftLog`.

    Fields:
    - `firstIndex` — result of `first_index()` (always ≥ 1 by invariant).
    - `lastIndex`  — result of `last_index()`.
    - `logTerm`    — combined term lookup: `unstable.maybe_term` shadowing `store.term`.
      `none` = compacted or unavailable; `some t` = term `t` at that index. -/
structure RaftLog where
  firstIndex : Nat
  lastIndex  : Nat
  logTerm    : Nat → Option Nat

/-- The Raft dummy entry index: `first_index() - 1`. -/
def dummyIdx (log : RaftLog) : Nat := log.firstIndex - 1

/-- Well-formedness: `firstIndex ≥ 1` (so `dummyIdx` is a valid `Nat`) and
    `lastIndex ≥ dummyIdx` (non-empty log). -/
def wf (log : RaftLog) : Prop :=
  log.firstIndex ≥ 1 ∧ log.lastIndex ≥ dummyIdx log

/-! ## `term` model -/

/-- `raftlogTerm log idx` — functional model of `RaftLog::term(idx)`.

    - If `idx < dummyIdx log` or `idx > log.lastIndex`: returns `some 0` (the sentinel).
    - Otherwise: delegates to `log.logTerm idx`
      (`some t` for a valid term, `none` for compacted/unavailable). -/
def raftlogTerm (log : RaftLog) (idx : Nat) : Option Nat :=
  if idx < dummyIdx log ∨ idx > log.lastIndex then some 0
  else log.logTerm idx

/-- `matchTerm log idx t` — functional model of `RaftLog::match_term(idx, t)`.

    Returns `true` iff `raftlogTerm log idx = some t`.
    (The Rust implementation: `self.term(idx).map(|s| s == t).unwrap_or(false)`.) -/
def matchTerm (log : RaftLog) (idx : Nat) (t : Nat) : Bool :=
  raftlogTerm log idx == some t

/-! ## Sanity checks -/

-- A concrete log: firstIndex = 5, lastIndex = 10, entries 5..10 have term 3,
-- dummy entry (4) has term 0, entries 0..3 compacted.
private def exLog : RaftLog :=
  { firstIndex := 5
    lastIndex  := 10
    logTerm    := fun i =>
      if i == 4 then some 0       -- dummy entry
      else if i ≥ 5 && i ≤ 10 then some 3
      else none }                  -- compacted

#eval raftlogTerm exLog 3   -- some 0  (below dummyIdx = 4)
#eval raftlogTerm exLog 4   -- some 0  (dummy entry, logTerm = some 0)
#eval raftlogTerm exLog 7   -- some 3  (in-range)
#eval raftlogTerm exLog 11  -- some 0  (above lastIndex = 10)

#eval matchTerm exLog 3 0   -- true   (out-of-range sentinel)
#eval matchTerm exLog 3 1   -- false  (out-of-range, t ≠ 0)
#eval matchTerm exLog 7 3   -- true
#eval matchTerm exLog 7 2   -- false

/-! ## PROP-1 through PROP-17: core theorems -/

/-! ### Boundary conditions for `raftlogTerm` -/

/-- **PROP-1**: Indices strictly below `dummyIdx` return the sentinel `some 0`. -/
theorem raftlogTerm_below_dummy (log : RaftLog) (idx : Nat)
    (h : idx < dummyIdx log) :
    raftlogTerm log idx = some 0 := by
  simp [raftlogTerm, h, Or.inl]

/-- **PROP-2**: Indices strictly above `lastIndex` return the sentinel `some 0`. -/
theorem raftlogTerm_above_last (log : RaftLog) (idx : Nat)
    (h : idx > log.lastIndex) :
    raftlogTerm log idx = some 0 := by
  simp [raftlogTerm]
  omega

/-- **PROP-3**: Indices in `[dummyIdx, lastIndex]` delegate to `logTerm`. -/
theorem raftlogTerm_in_range (log : RaftLog) (idx : Nat)
    (hlo : idx ≥ dummyIdx log) (hhi : idx ≤ log.lastIndex) :
    raftlogTerm log idx = log.logTerm idx := by
  simp [raftlogTerm]
  omega

/-- **PROP-4**: `raftlogTerm` always returns `some _` for out-of-range indices,
    never `none`. -/
theorem raftlogTerm_out_of_range_not_none (log : RaftLog) (idx : Nat)
    (h : idx < dummyIdx log ∨ idx > log.lastIndex) :
    raftlogTerm log idx ≠ none := by
  simp [raftlogTerm, h]

/-! ### `matchTerm` characterisation -/

/-- **PROP-5**: `matchTerm` is the Boolean test `raftlogTerm log idx = some t`. -/
theorem matchTerm_iff (log : RaftLog) (idx t : Nat) :
    matchTerm log idx t = true ↔ raftlogTerm log idx = some t := by
  simp [matchTerm, beq_iff_eq]

/-- **PROP-6**: `matchTerm` false iff `raftlogTerm` differs or is `none`. -/
theorem matchTerm_false_iff (log : RaftLog) (idx t : Nat) :
    matchTerm log idx t = false ↔ raftlogTerm log idx ≠ some t := by
  simp [matchTerm, Bool.eq_false_iff, beq_iff_eq]

/-- **PROP-7**: Forward direction — `matchTerm` true implies `raftlogTerm = some t`. -/
theorem matchTerm_true_implies_term (log : RaftLog) (idx t : Nat)
    (h : matchTerm log idx t = true) :
    raftlogTerm log idx = some t := by
  exact (matchTerm_iff log idx t).mp h

/-- **PROP-8**: Backward direction — `raftlogTerm = some t` implies `matchTerm` true. -/
theorem term_implies_matchTerm (log : RaftLog) (idx t : Nat)
    (h : raftlogTerm log idx = some t) :
    matchTerm log idx t = true := by
  exact (matchTerm_iff log idx t).mpr h

/-- **PROP-9**: Uniqueness — at most one term can match at a given index. -/
theorem matchTerm_unique (log : RaftLog) (idx t₁ t₂ : Nat)
    (h1 : matchTerm log idx t₁ = true)
    (h2 : matchTerm log idx t₂ = true) :
    t₁ = t₂ := by
  rw [matchTerm_iff] at h1 h2
  simp_all

/-- **PROP-10**: Wrong term gives `false`. -/
theorem matchTerm_false_wrong_term (log : RaftLog) (idx t₁ t₂ : Nat)
    (hmatch : matchTerm log idx t₁ = true)
    (hne    : t₂ ≠ t₁) :
    matchTerm log idx t₂ = false := by
  rw [matchTerm_false_iff]
  rw [matchTerm_iff] at hmatch
  intro h
  simp_all

/-! ### Out-of-range behaviour of `matchTerm` -/

/-- **PROP-11**: For any non-zero term, an index below `dummyIdx` gives `false`.
    (The sentinel is `0`, not `t`.) -/
theorem matchTerm_false_below_dummy (log : RaftLog) (idx t : Nat)
    (hidx : idx < dummyIdx log)
    (ht   : t ≠ 0) :
    matchTerm log idx t = false := by
  rw [matchTerm_false_iff, raftlogTerm_below_dummy _ _ hidx]
  exact fun h => ht (by simp_all)

/-- **PROP-12**: The out-of-range sentinel matches term `0` for indices below `dummyIdx`. -/
theorem matchTerm_zero_below_dummy (log : RaftLog) (idx : Nat)
    (h : idx < dummyIdx log) :
    matchTerm log idx 0 = true := by
  rw [matchTerm_iff, raftlogTerm_below_dummy _ _ h]

/-- **PROP-13**: For any non-zero term, an index above `lastIndex` gives `false`. -/
theorem matchTerm_false_above_last (log : RaftLog) (idx t : Nat)
    (hidx : idx > log.lastIndex)
    (ht   : t ≠ 0) :
    matchTerm log idx t = false := by
  rw [matchTerm_false_iff, raftlogTerm_above_last _ _ hidx]
  exact fun h => ht (by simp_all)

/-- **PROP-14**: The out-of-range sentinel matches term `0` for indices above `lastIndex`. -/
theorem matchTerm_zero_above_last (log : RaftLog) (idx : Nat)
    (h : idx > log.lastIndex) :
    matchTerm log idx 0 = true := by
  rw [matchTerm_iff, raftlogTerm_above_last _ _ h]

/-- **PROP-15**: `matchTerm` for a non-zero term implies the index is in
    `[dummyIdx, lastIndex]`. -/
theorem matchTerm_nonzero_implies_in_range (log : RaftLog) (idx t : Nat)
    (hmatch : matchTerm log idx t = true)
    (ht     : t ≠ 0) :
    dummyIdx log ≤ idx ∧ idx ≤ log.lastIndex := by
  rw [matchTerm_iff] at hmatch
  by_contra h
  push_neg at h
  rcases h with hlo | hhi
  · rw [raftlogTerm_below_dummy _ _ hlo] at hmatch; simp_all
  · rw [raftlogTerm_above_last _ _ hhi] at hmatch; simp_all

/-! ### Error case (compacted / unavailable store) -/

/-- **PROP-16**: If `logTerm` returns `none` for an in-range index,
    `matchTerm` returns `false` for every term. -/
theorem matchTerm_false_logTerm_none (log : RaftLog) (idx t : Nat)
    (hlo  : idx ≥ dummyIdx log)
    (hhi  : idx ≤ log.lastIndex)
    (hnone : log.logTerm idx = none) :
    matchTerm log idx t = false := by
  rw [matchTerm_false_iff, raftlogTerm_in_range _ _ hlo hhi, hnone]
  exact Option.noConfusion

/-- **PROP-17**: If `logTerm` returns `none`, `raftlogTerm` is also `none`
    (for in-range indices), confirming no sentinel is injected. -/
theorem raftlogTerm_none_iff_logTerm_none (log : RaftLog) (idx : Nat)
    (hlo : idx ≥ dummyIdx log) (hhi : idx ≤ log.lastIndex) :
    raftlogTerm log idx = none ↔ log.logTerm idx = none := by
  rw [raftlogTerm_in_range _ _ hlo hhi]

/-! ## PROP-18: Dummy entry -/

/-- **PROP-18**: In a well-formed log whose dummy entry has term `0` (the normal Raft
    invariant for a freshly initialised log), `matchTerm` at the dummy index matches `0`. -/
theorem matchTerm_dummy_zero (log : RaftLog)
    (hwf   : wf log)
    (hdummy : log.logTerm (dummyIdx log) = some 0) :
    matchTerm log (dummyIdx log) 0 = true := by
  have hlo : dummyIdx log ≥ dummyIdx log := le_refl _
  have hhi : dummyIdx log ≤ log.lastIndex := hwf.2
  rw [matchTerm_iff, raftlogTerm_in_range _ _ hlo hhi, hdummy]

end FVSquad.RaftLogTerm
