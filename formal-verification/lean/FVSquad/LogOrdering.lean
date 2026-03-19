/-!
# Log Ordering — Lean 4 Specification

Formal specification of two key log ordering operations from `src/raft_log.rs`:

- `is_up_to_date`: determines if a candidate log is "at least as up-to-date" as
  the current log (Raft election safety — voters only vote for candidates whose
  log is at least as up-to-date as theirs).
- `find_conflict_by_term`: scans backward in the log to find the last position
  with term ≤ a given query term (used during log reconciliation after rejected
  AppendEntries).

## Model scope and approximations

* `IsUpToDate` is a pure predicate on `(lastIndex, lastTerm, logLastIndex, logLastTerm)`.
  All indices are modelled as `Nat` (no 64-bit overflow reasoning).
* `findConflictByTerm` is modelled as a structurally recursive function on `Nat`,
  operating on an abstract term oracle `logTerm : Nat → Option Nat`.
* Side effects (logging, panics on invalid input) are omitted.
* The `RaftLog` struct (containing both stable and unstable entries) is abstracted
  away — only the `term(idx)` lookup is needed.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace FVSquad.LogOrdering

-- ============================================================
-- Part 1: IsUpToDate
-- ============================================================

/-!
## IsUpToDate

From `src/raft_log.rs`:
```rust
pub fn is_up_to_date(&self, last_index: u64, term: u64) -> bool {
    term > self.last_term() ||
    (term == self.last_term() && last_index >= self.last_index())
}
```

A candidate log with `(lastIndex = li, lastTerm = t)` is "at least as up-to-date"
as a log with `(logLastIndex = li2, logLastTerm = t2)` iff:
- `t > t2`  (candidate has a later term), **or**
- `t = t2 ∧ li ≥ li2`  (same term but candidate's log is at least as long).

This defines a **total preorder** on `(lastIndex, lastTerm)` pairs — sometimes
called the "Raft log order" — where terms take priority over indices. The
election safety argument relies on this preorder being total and transitive.
-/

/-- `IsUpToDate li t li2 t2` holds iff the log ending at `(li, t)` is at least as
    up-to-date as the log ending at `(li2, t2)` in the Raft log order. -/
def IsUpToDate (li t li2 t2 : Nat) : Prop :=
  t2 < t ∨ (t = t2 ∧ li2 ≤ li)

instance (li t li2 t2 : Nat) : Decidable (IsUpToDate li t li2 t2) := by
  unfold IsUpToDate; infer_instance

-- ### Reflexivity: a log is always at least as up-to-date as itself.

theorem isUpToDate_refl (li t : Nat) : IsUpToDate li t li t :=
  Or.inr ⟨rfl, Nat.le_refl li⟩

-- ### Higher term always dominates.

theorem isUpToDate_higher_term (li t li2 t2 : Nat) (h : t2 < t) :
    IsUpToDate li t li2 t2 :=
  Or.inl h

-- ### A log with strictly lower term is never up-to-date.

theorem isUpToDate_lower_term (li t li2 t2 : Nat) (h : t < t2) :
    ¬ IsUpToDate li t li2 t2 := by
  unfold IsUpToDate
  omega

-- ### Same term: longer log wins.

theorem isUpToDate_same_term_ge (li li2 t : Nat) (h : li2 ≤ li) :
    IsUpToDate li t li2 t :=
  Or.inr ⟨rfl, h⟩

theorem isUpToDate_same_term_lt (li li2 t : Nat) (h : li < li2) :
    ¬ IsUpToDate li t li2 t := by
  unfold IsUpToDate
  omega

-- ### Totality: for any two pairs, at least one is up-to-date wrt the other.

theorem isUpToDate_total (li1 t1 li2 t2 : Nat) :
    IsUpToDate li1 t1 li2 t2 ∨ IsUpToDate li2 t2 li1 t1 := by
  unfold IsUpToDate
  omega

-- ### Transitivity: the preorder is transitive.

theorem isUpToDate_trans (li1 t1 li2 t2 li3 t3 : Nat)
    (h12 : IsUpToDate li1 t1 li2 t2)
    (h23 : IsUpToDate li2 t2 li3 t3) :
    IsUpToDate li1 t1 li3 t3 := by
  unfold IsUpToDate at *
  omega

-- ### Antisymmetry: mutual up-to-date-ness implies equal (term, index).

theorem isUpToDate_antisymm (li1 t1 li2 t2 : Nat)
    (h12 : IsUpToDate li1 t1 li2 t2)
    (h21 : IsUpToDate li2 t2 li1 t1) :
    t1 = t2 ∧ li1 = li2 := by
  unfold IsUpToDate at *
  omega

-- ### Raft election safety corollary:
-- If both voters/candidates satisfy mutual up-to-date-ness, they have identical
-- (lastIndex, lastTerm), which means they could not have divergent committed logs.

theorem isUpToDate_mutual_eq (li1 t1 li2 t2 : Nat)
    (h12 : IsUpToDate li1 t1 li2 t2)
    (h21 : IsUpToDate li2 t2 li1 t1) :
    (li1, t1) = (li2, t2) := by
  have := isUpToDate_antisymm li1 t1 li2 t2 h12 h21
  simp [Prod.mk.injEq]
  omega

-- ### Lexicographic order connection:
-- The Raft log order is equivalent to the lexicographic order on (term, index) pairs
-- (where term is the more significant component).

/-- The pair `(t, li)` for lexicographic comparison — term is the primary key. -/
def toPair (li t : Nat) : Nat × Nat := (t, li)

theorem isUpToDate_iff_pair_ge (li t li2 t2 : Nat) :
    IsUpToDate li t li2 t2 ↔ (t2, li2) ≤ (t, li) := by
  simp [IsUpToDate, Prod.le_def]
  omega

-- ### Decidable examples (sanity checks via #eval)
#eval decide (IsUpToDate 5 3 4 2)   -- true: term 3 > 2
#eval decide (IsUpToDate 5 2 4 3)   -- false: term 2 < 3
#eval decide (IsUpToDate 5 3 4 3)   -- true: same term, index 5 ≥ 4
#eval decide (IsUpToDate 4 3 5 3)   -- false: same term, index 4 < 5
#eval decide (IsUpToDate 5 3 5 3)   -- true: reflexive

-- ============================================================
-- Part 2: findConflictByTerm
-- ============================================================

/-!
## findConflictByTerm

From `src/raft_log.rs`:
```rust
pub fn find_conflict_by_term(&self, index: u64, term: u64) -> (u64, Option<u64>) {
    let mut conflict_index = index;
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

Starting from `index`, scans **backward** in the log until finding the largest
index `j ≤ index` where `log_term(j) ≤ queryTerm`. This is used by a follower to
efficiently find the conflict point when a leader's AppendEntries is rejected
(the follower can skip back by term rather than one-entry-at-a-time).

### Model

We abstract the `RaftLog` as a function `logTerm : Nat → Option Nat`:
- `logTerm i = some t` means index `i` has term `t`
- `logTerm i = none`  means index `i` is out of range (error case)

We model the scan as a structurally recursive function (decreasing on `idx`).
In the error case (`none`), we return the current index unchanged (matching the
Rust `Err(_) => return (conflict_index, None)` path).
-/

/-- Find the last log position at or before `idx` where the term ≤ `queryTerm`.
    Returns `idx` on an out-of-range lookup (the error path).
    Structurally recursive: decreases by peeling the successor. -/
def findConflictByTerm (logTerm : Nat → Option Nat) (queryTerm : Nat) : Nat → Nat
  | 0       => 0
  | (n + 1) =>
    match logTerm (n + 1) with
    | none   => n + 1                          -- out of range: return current idx
    | some t =>
      if t ≤ queryTerm then n + 1              -- found: term satisfies condition
      else findConflictByTerm logTerm queryTerm n  -- term too high: scan back

-- ==================
-- Equation lemmas
-- ==================

theorem findConflict_zero (logTerm : Nat → Option Nat) (qt : Nat) :
    findConflictByTerm logTerm qt 0 = 0 := rfl

theorem findConflict_none_eq (logTerm : Nat → Option Nat) (qt n : Nat)
    (h : logTerm (n + 1) = none) :
    findConflictByTerm logTerm qt (n + 1) = n + 1 := by
  simp [findConflictByTerm, h]

theorem findConflict_found_eq (logTerm : Nat → Option Nat) (qt n t : Nat)
    (ht : logTerm (n + 1) = some t) (hle : t ≤ qt) :
    findConflictByTerm logTerm qt (n + 1) = n + 1 := by
  simp [findConflictByTerm, ht, hle]

theorem findConflict_step_eq (logTerm : Nat → Option Nat) (qt n t : Nat)
    (ht : logTerm (n + 1) = some t) (hgt : qt < t) :
    findConflictByTerm logTerm qt (n + 1) = findConflictByTerm logTerm qt n := by
  simp [findConflictByTerm, ht]
  omega

-- ==================
-- Key structural theorems
-- ==================

/-- The result never exceeds the input index — we only ever scan backward. -/
theorem findConflict_le (logTerm : Nat → Option Nat) (qt idx : Nat) :
    findConflictByTerm logTerm qt idx ≤ idx := by
  induction idx with
  | zero => simp [findConflict_zero]
  | succ n ih =>
    simp only [findConflictByTerm]
    split
    · -- logTerm (n+1) = none: return n+1 ≤ n+1
      exact Nat.le_refl _
    · rename_i t ht
      split
      · -- t ≤ qt: return n+1 ≤ n+1
        exact Nat.le_refl _
      · -- t > qt: recurse to n, result ≤ n ≤ n+1
        exact Nat.le_step ih

/-- The result is always a natural number (trivially, but useful for composition). -/
theorem findConflict_nonneg (logTerm : Nat → Option Nat) (qt idx : Nat) :
    0 ≤ findConflictByTerm logTerm qt idx :=
  Nat.zero_le _

/-- When the result is found (not the error path), the term at the result is ≤ queryTerm. -/
theorem findConflict_term_le (logTerm : Nat → Option Nat) (qt : Nat) :
    ∀ idx : Nat,
    ∀ r : Nat, findConflictByTerm logTerm qt idx = r →
    ∀ t : Nat, logTerm r = some t →
    t ≤ qt ∨ r = idx := by
  intro idx
  induction idx with
  | zero =>
    intro r h t ht
    simp [findConflictByTerm] at h
    subst h; right; rfl
  | succ n ih =>
    intro r h t ht
    simp only [findConflictByTerm] at h
    split at h
    · -- logTerm (n+1) = none: r = n+1, it's the error path
      subst h; right; rfl
    · rename_i u hu
      split at h
      · -- t' ≤ qt, r = n+1
        subst h
        rw [hu] at ht
        cases ht
        left; assumption
      · -- recurse: r = findConflictByTerm logTerm qt n
        rcases ih r h t ht with hle | heq
        · left; exact hle
        · right; omega  -- heq : r = n, but r ≤ n ≤ succ n

/-- Monotonicity: scanning back from a smaller index gives a result ≤ the result
    from a larger index (for any log term oracle). -/
theorem findConflict_mono_idx (logTerm : Nat → Option Nat) (qt : Nat) :
    ∀ idx1 idx2 : Nat, idx1 ≤ idx2 →
    findConflictByTerm logTerm qt idx1 ≤ findConflictByTerm logTerm qt idx2 := by
  intro idx1 idx2 hle
  induction idx2 with
  | zero =>
    -- idx1 = 0 since idx1 ≤ 0
    simp only [Nat.le_zero] at hle
    subst hle; rfl.le
  | succ n ih =>
    by_cases h : idx1 = n + 1
    · subst h; rfl.le
    · -- idx1 ≤ n
      have hlt : idx1 ≤ n := Nat.lt_of_le_of_ne hle h |> Nat.lt_succ_iff.mp
      have := ih hlt
      simp only [findConflictByTerm]
      split
      · -- logTerm (n+1) = none: result = n+1
        -- findConflict qt idx1 ≤ idx1 ≤ n < n+1
        have hb := findConflict_le logTerm qt idx1
        omega
      · rename_i t ht
        split
        · -- found: result = n+1
          have hb := findConflict_le logTerm qt idx1
          omega
        · -- recurse: result = findConflict logTerm qt n
          exact this

-- ### Sanity check: concrete log example

/-- An example log: terms [_, 1, 2, 3, 3, 4] at indices [0, 1, 2, 3, 4, 5]. -/
def exLogTerm : Nat → Option Nat
  | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 3 | 5 => some 4 | _ => none

-- Scan from index 5 for last entry with term ≤ 3: should land at index 4 (term=3)
#eval findConflictByTerm exLogTerm 3 5   -- expected: 4
-- Scan from index 5 for last entry with term ≤ 4: should be 5 (term=4)
#eval findConflictByTerm exLogTerm 4 5   -- expected: 5
-- Scan from index 5 for last entry with term ≤ 1: should be 1 (term=1)
#eval findConflictByTerm exLogTerm 1 5   -- expected: 1
-- Scan from index 2 for last entry with term ≤ 1: should be 1
#eval findConflictByTerm exLogTerm 1 2   -- expected: 1
-- Scan from index 1 for last entry with term ≤ 0: should be 0 (none found)
#eval findConflictByTerm exLogTerm 0 1   -- expected: 0

-- ============================================================
-- Part 3: Connection — IsUpToDate and election safety sketch
-- ============================================================

/-!
## Election safety sketch

In Raft, a candidate is elected only if a quorum of nodes votes for it.
A node votes for a candidate only if the candidate's log is at least as
up-to-date as the node's own log (`is_up_to_date` returns true).

This means: if two candidates are both elected in overlapping quorums, the
candidate in the later term must have a log that is at least as up-to-date as
the previous leader's committed entries (by the quorum intersection argument).

The following theorem captures the key monotonicity property:
if A is up-to-date relative to B, and B is up-to-date relative to C, then
A is up-to-date relative to C (enabling the chain of safe elections).
-/

-- Transitivity is already proved above as `isUpToDate_trans`.
-- The following shows that the relation strictly improves as terms increase:

theorem isUpToDate_strict_later_term (li t li2 t2 : Nat) (ht : t2 < t) :
    IsUpToDate li t li2 t2 ∧ ¬ IsUpToDate li2 t2 li t := by
  constructor
  · exact isUpToDate_higher_term li t li2 t2 ht
  · exact isUpToDate_lower_term li2 t2 li t ht

end FVSquad.LogOrdering
