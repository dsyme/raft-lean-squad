/-
  UnionUtils.lean
  Formal specification and proofs for the `Union` struct and `is_continuous_ents`
  function from `src/util.rs`.

  ## Model scope and approximations
  - Node IDs: `u64` → `Nat` (overflow not modelled; all indices are finite)
  - `HashSet<u64>` → `Finset Nat` (order and allocation details not modelled)
  - `Union::iter()` not modelled (requires iterator abstraction)
  - `Union` is modelled as a pure value type (not a reference pair)
  - `is_continuous_ents`: `Message.entries` and the `ents` slice are modelled as
    `List` of `(index : Nat)` pairs; only `index` fields are relevant.

  🔬 Lean Squad — automated formal verification for `dsyme/fv-squad`.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic

-- ============================================================
-- §1  Union model
-- ============================================================

/-- Abstract model of `Union<'a>`: a pair of finite node-ID sets. -/
structure RaftUnion where
  first  : Finset Nat
  second : Finset Nat

/-- `Union::contains` — membership in either set. -/
def RaftUnion.contains (u : RaftUnion) (id : Nat) : Bool :=
  u.first.contains id || u.second.contains id

/-- `Union::is_empty` — both sets are empty. -/
def RaftUnion.isEmpty (u : RaftUnion) : Bool :=
  u.first.isEmpty && u.second.isEmpty

/-- `Union::len` — inclusion-exclusion cardinality.
    Matches Rust: `first.len() + second.len() - second.intersection(first).count()` -/
def RaftUnion.len (u : RaftUnion) : Nat :=
  u.first.card + u.second.card - (u.second ∩ u.first).card

/-- The mathematical union set. -/
def RaftUnion.asSet (u : RaftUnion) : Finset Nat :=
  u.first ∪ u.second

-- ============================================================
-- §2  Membership correctness
-- ============================================================

/-- PROP-1: `contains id` is equivalent to membership in the mathematical union. -/
theorem RaftUnion.contains_iff (u : RaftUnion) (id : Nat) :
    u.contains id = true ↔ id ∈ u.asSet := by
  simp [RaftUnion.contains, RaftUnion.asSet, Finset.contains_iff,
        Finset.mem_union, Bool.or_eq_true]

/-- PROP-1a: `contains` false iff not in either set. -/
theorem RaftUnion.not_contains_iff (u : RaftUnion) (id : Nat) :
    u.contains id = false ↔ id ∉ u.asSet := by
  simp [RaftUnion.contains_iff]

/-- Helper: if id is in first, contains returns true. -/
theorem RaftUnion.contains_of_mem_first (u : RaftUnion) (id : Nat) (h : id ∈ u.first) :
    u.contains id = true := by
  rw [RaftUnion.contains_iff]
  simp [RaftUnion.asSet, Finset.mem_union]
  exact Or.inl h

/-- Helper: if id is in second, contains returns true. -/
theorem RaftUnion.contains_of_mem_second (u : RaftUnion) (id : Nat) (h : id ∈ u.second) :
    u.contains id = true := by
  rw [RaftUnion.contains_iff]
  simp [RaftUnion.asSet, Finset.mem_union]
  exact Or.inr h

-- ============================================================
-- §3  Emptiness correctness
-- ============================================================

/-- PROP-2: `isEmpty` is equivalent to the mathematical union being empty. -/
theorem RaftUnion.isEmpty_iff (u : RaftUnion) :
    u.isEmpty = true ↔ u.asSet = ∅ := by
  simp [RaftUnion.isEmpty, RaftUnion.asSet, Bool.and_eq_true,
        Finset.isEmpty_iff_eq_empty, Finset.union_eq_empty]

/-- PROP-2a: when both sets are empty, isEmpty returns true. -/
theorem RaftUnion.isEmpty_of_both_empty (u : RaftUnion) (h1 : u.first = ∅) (h2 : u.second = ∅) :
    u.isEmpty = true := by
  rw [RaftUnion.isEmpty_iff, RaftUnion.asSet, h1, h2]
  simp

-- ============================================================
-- §4  Cardinality correctness (inclusion-exclusion)
-- ============================================================

/-- Key lemma: intersection is commutative for cardinality. -/
private lemma inter_card_comm (A B : Finset Nat) :
    (B ∩ A).card = (A ∩ B).card := by
  rw [Finset.inter_comm]

/-- Key lemma: |A ∩ B| ≤ |A| + |B| (needed for Nat subtraction soundness). -/
private lemma inter_card_le_add (A B : Finset Nat) :
    (A ∩ B).card ≤ A.card + B.card := by
  calc (A ∩ B).card ≤ A.card := Finset.card_inter_le_card_left A B
    _ ≤ A.card + B.card := Nat.le_add_right _ _

/-- PROP-3: `len` equals the cardinality of the mathematical union.
    Proves the inclusion-exclusion formula: `|A| + |B| − |A ∩ B| = |A ∪ B|`. -/
theorem RaftUnion.len_correct (u : RaftUnion) :
    u.len = u.asSet.card := by
  simp only [RaftUnion.len, RaftUnion.asSet]
  have hie := Finset.card_union_add_card_inter u.first u.second
  rw [inter_card_comm u.second u.first]
  omega

/-- PROP-3a: when second is empty, len equals first.card (degenerate case). -/
theorem RaftUnion.len_of_empty_second (u : RaftUnion) (h : u.second = ∅) :
    u.len = u.first.card := by
  rw [RaftUnion.len_correct, RaftUnion.asSet, h, Finset.union_empty]

/-- PROP-3b: when first is empty, len equals second.card. -/
theorem RaftUnion.len_of_empty_first (u : RaftUnion) (h : u.first = ∅) :
    u.len = u.second.card := by
  rw [RaftUnion.len_correct, RaftUnion.asSet, h, Finset.empty_union]

/-- PROP-3c: when first = second, len equals first.card (fully overlapping). -/
theorem RaftUnion.len_of_equal_sets (u : RaftUnion) (h : u.first = u.second) :
    u.len = u.first.card := by
  rw [RaftUnion.len_correct, RaftUnion.asSet, h, Finset.union_idempotent]

/-- PROP-3d: when disjoint, len = first.card + second.card. -/
theorem RaftUnion.len_of_disjoint (u : RaftUnion) (h : Disjoint u.first u.second) :
    u.len = u.first.card + u.second.card := by
  rw [RaftUnion.len_correct, RaftUnion.asSet]
  exact (Finset.card_union_of_disjoint h).symm

-- ============================================================
-- §5  Cardinality-emptiness agreement
-- ============================================================

/-- PROP-4: len = 0 iff isEmpty. -/
theorem RaftUnion.len_zero_iff_isEmpty (u : RaftUnion) :
    u.len = 0 ↔ u.isEmpty = true := by
  rw [RaftUnion.len_correct, RaftUnion.isEmpty_iff]
  simp [RaftUnion.asSet, Finset.card_eq_zero]

/-- PROP-4a: len > 0 iff not isEmpty. -/
theorem RaftUnion.len_pos_iff_not_isEmpty (u : RaftUnion) :
    0 < u.len ↔ u.isEmpty = false := by
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro hne
    have : ¬(u.isEmpty = true) := fun h => hne (RaftUnion.len_zero_iff_isEmpty.mpr h)
    simp [Bool.not_eq_true] at this
    exact this
  · intro hf hz
    have : u.isEmpty = true := RaftUnion.len_zero_iff_isEmpty.mp hz
    simp [this] at hf

-- ============================================================
-- §6  Membership implies non-empty
-- ============================================================

/-- PROP-5: if contains(id) then len > 0. -/
theorem RaftUnion.len_pos_of_contains (u : RaftUnion) (id : Nat) (h : u.contains id = true) :
    0 < u.len := by
  rw [RaftUnion.len_correct, RaftUnion.contains_iff] at *
  exact Finset.card_pos.mpr ⟨id, h⟩

/-- PROP-5a: if isEmpty then contains returns false for all ids. -/
theorem RaftUnion.not_contains_of_isEmpty (u : RaftUnion) (hEmpty : u.isEmpty = true) (id : Nat) :
    u.contains id = false := by
  rw [RaftUnion.contains_iff, RaftUnion.isEmpty_iff] at *
  simp [RaftUnion.asSet, hEmpty]

-- ============================================================
-- §7  Monotonicity
-- ============================================================

/-- PROP-6: len is monotone in first (enlarging first cannot decrease len). -/
theorem RaftUnion.len_mono_first (u : RaftUnion) (larger : Finset Nat) (h : u.first ⊆ larger) :
    u.len ≤ (RaftUnion.mk larger u.second).len := by
  simp only [RaftUnion.len_correct, RaftUnion.asSet]
  apply Finset.card_le_card
  exact Finset.union_subset_union_left u.second h

/-- PROP-7: len is monotone in second (enlarging second cannot decrease len). -/
theorem RaftUnion.len_mono_second (u : RaftUnion) (larger : Finset Nat) (h : u.second ⊆ larger) :
    u.len ≤ (RaftUnion.mk u.first larger).len := by
  simp only [RaftUnion.len_correct, RaftUnion.asSet]
  apply Finset.card_le_card
  exact Finset.union_subset_union_right u.first h

-- ============================================================
-- §8  `is_continuous_ents` model
-- ============================================================

/-- Abstract model of a log entry: just the index field is relevant. -/
structure LogEntry where
  index : Nat

/-- Model of `is_continuous_ents(msg, ents)`.
    Returns true when `ents` immediately follows the last entry in `msgEntries`. -/
def isContinuous (msgEntries : List LogEntry) (ents : List LogEntry) : Bool :=
  match msgEntries.getLast?, ents.head? with
  | some last, some first => (last.index + 1 == first.index)
  | _, _ => true

-- ============================================================
-- §9  Properties of `is_continuous_ents`
-- ============================================================

/-- PROP-8: empty msgEntries → always continuous. -/
theorem isContinuous_empty_left (ents : List LogEntry) :
    isContinuous [] ents = true := by
  simp [isContinuous]

/-- PROP-9: empty ents → always continuous. -/
theorem isContinuous_empty_right (msgEntries : List LogEntry) :
    isContinuous msgEntries [] = true := by
  simp [isContinuous]
  split <;> simp

/-- PROP-10: singleton msgEntries, singleton ents → checks index gap. -/
theorem isContinuous_singleton_iff (e₁ e₂ : LogEntry) :
    isContinuous [e₁] [e₂] = true ↔ e₂.index = e₁.index + 1 := by
  simp [isContinuous]

/-- PROP-11: overlap (gap = 0) is not continuous. -/
theorem isContinuous_overlap_false (e : LogEntry) :
    isContinuous [e] [e] = false := by
  simp [isContinuous]
  omega

/-- PROP-12: gap > 1 is not continuous. -/
theorem isContinuous_gap_false (e₁ e₂ : LogEntry) (h : e₂.index > e₁.index + 1) :
    isContinuous [e₁] [e₂] = false := by
  simp [isContinuous]
  omega

/-- PROP-13: isContinuous is preserved when appending a matching next entry.
    i.e. if [e₁, e₂] are consecutive and e₂.index + 1 = e₃.index,
    then [e₁, e₂] and [e₃] are continuous. -/
theorem isContinuous_extend (e₁ e₂ e₃ : LogEntry) (h : e₃.index = e₂.index + 1) :
    isContinuous [e₁, e₂] [e₃] = true := by
  simp [isContinuous, h]

-- ============================================================
-- §10  Concrete examples (validated properties)
-- ============================================================

/-- Example: Union of {1,2,3} and {3,4,5} has len = 5 (|{1,2,3,4,5}|). -/
example :
    let u : RaftUnion := ⟨{1, 2, 3}, {3, 4, 5}⟩
    u.len = 5 := by native_decide

/-- Example: Union of {1,2,3} and {} has len = 3. -/
example :
    let u : RaftUnion := ⟨{1, 2, 3}, ∅⟩
    u.len = 3 := by native_decide

/-- Example: Union of {} and {} has len = 0 and isEmpty = true. -/
example :
    let u : RaftUnion := ⟨∅, ∅⟩
    u.len = 0 ∧ u.isEmpty = true := by native_decide

/-- Example: Union of {1,2} and {1,2} (equal sets) has len = 2. -/
example :
    let u : RaftUnion := ⟨{1, 2}, {1, 2}⟩
    u.len = 2 := by native_decide

/-- Example: isContinuous with matching indices returns true. -/
example : isContinuous [⟨5⟩] [⟨6⟩] = true := by native_decide

/-- Example: isContinuous with gap 2 returns false. -/
example : isContinuous [⟨5⟩] [⟨7⟩] = false := by native_decide

/-- Example: isContinuous with gap 0 (overlap) returns false. -/
example : isContinuous [⟨5⟩] [⟨5⟩] = false := by native_decide
