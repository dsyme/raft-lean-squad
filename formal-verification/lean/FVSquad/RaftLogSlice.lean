/-
  FVSquad/RaftLogSlice.lean

  Formal specification and proofs for `RaftLog::slice` and
  `must_check_outofbounds` from `src/raft_log.rs`,
  and `Unstable::slice` / `Unstable::must_check_outofbounds` from
  `src/log_unstable.rs`.

  🔬 Lean Squad — automated formal verification for dsyme/fv-squad.

  ## What is modelled

  The Raft log is stored in two parts:
  - **Stable storage**: indices in [first_index, unstable_offset)
  - **Unstable buffer**: indices in [unstable_offset, unstable_offset + unstable_len)

  `must_check_outofbounds(low, high)` validates a requested range [low, high):
    - Panics (modelled as a precondition) if low > high or high > last_index + 1
    - Returns Compacted if low < first_index
    - Returns Ok if first_index ≤ low ≤ high ≤ last_index + 1

  `slice(low, high)` assembles entries from both parts:
    1. Reads [low, min(high, unstable_offset)) from stable storage
    2. If stable read is complete, reads [max(low, unstable_offset), high) from unstable
    3. Concatenates results; applies size limit

  ## What is NOT modelled
  - Actual entry content (bytes, terms, commands) — only index ranges
  - Storage I/O errors, logging, panics, protobuf
  - `max_size` / `limit_size` byte budget (proved separately in `LimitSize.lean`)
  - `GetEntriesContext` (pagination/priority hints)
  - Concurrent compaction (treated as atomic)
  - Partial stable reads (modelled as always returning the full requested range)
-/

import Mathlib.Tactic

/-! ## Log state -/

/-- Abstract state of a `RaftLog<T>` relevant to slice operations. -/
structure RaftLogSliceState where
  /-- Index of the first entry in the log (after any compaction). -/
  firstIndex     : ℕ
  /-- Boundary between stable storage and the unstable buffer. -/
  unstableOffset : ℕ
  /-- Number of entries in the unstable buffer. -/
  unstableLen    : ℕ
  /-- `firstIndex ≤ unstableOffset` — stable storage precedes unstable buffer. -/
  h_first_le_offset : firstIndex ≤ unstableOffset
  deriving Repr

/-- The exclusive upper bound of the log (one past the last index). -/
def logHigh (s : RaftLogSliceState) : ℕ :=
  s.unstableOffset + s.unstableLen

/-- The last valid index in the log. -/
def lastIdx (s : RaftLogSliceState) : ℕ :=
  s.unstableOffset + s.unstableLen - 1

/-! ## `must_check_outofbounds` -/

/-- Result of `RaftLog::must_check_outofbounds`. -/
inductive BoundsCheck
  | ok        : BoundsCheck   -- None in Rust: range is valid
  | compacted : BoundsCheck   -- Some(Compacted): range starts before first_index
  deriving Repr, DecidableEq

/-- Model of `RaftLog::must_check_outofbounds(low, high)`.
    Precondition (modelled as an assumption, not a panic):
      `low ≤ high` and `high ≤ logHigh s`.
    Returns `compacted` iff `low < first_index`. -/
def mustCheckOutofbounds (s : RaftLogSliceState) (low : ℕ) : BoundsCheck :=
  if s.firstIndex ≤ low then BoundsCheck.ok else BoundsCheck.compacted

/-! ### Characterisation -/

theorem mustCheckOutofbounds_ok_iff (s : RaftLogSliceState) (low : ℕ) :
    mustCheckOutofbounds s low = BoundsCheck.ok ↔ s.firstIndex ≤ low := by
  simp [mustCheckOutofbounds]

theorem mustCheckOutofbounds_compacted_iff (s : RaftLogSliceState) (low : ℕ) :
    mustCheckOutofbounds s low = BoundsCheck.compacted ↔ low < s.firstIndex := by
  simp [mustCheckOutofbounds]
  omega

theorem mustCheckOutofbounds_ok_of_firstIndex (s : RaftLogSliceState)
    (low : ℕ) (h : s.firstIndex ≤ low) :
    mustCheckOutofbounds s low = BoundsCheck.ok := by
  simp [mustCheckOutofbounds, h]

theorem mustCheckOutofbounds_compacted_of_lt (s : RaftLogSliceState)
    (low : ℕ) (h : low < s.firstIndex) :
    mustCheckOutofbounds s low = BoundsCheck.compacted := by
  simp [mustCheckOutofbounds]; omega

/-- `mustCheckOutofbounds` is determined solely by `low` and `firstIndex`. -/
theorem mustCheckOutofbounds_indep_high (s : RaftLogSliceState) (low hi1 hi2 : ℕ) :
    mustCheckOutofbounds s low = mustCheckOutofbounds s low := rfl

/-- If `low` is valid, any larger `low'` is also valid (ok propagates upward). -/
theorem mustCheckOutofbounds_ok_mono (s : RaftLogSliceState)
    (lo1 lo2 : ℕ) (h : lo1 ≤ lo2)
    (hok : mustCheckOutofbounds s lo1 = BoundsCheck.ok) :
    mustCheckOutofbounds s lo2 = BoundsCheck.ok := by
  rw [mustCheckOutofbounds_ok_iff] at *; omega

/-- If `low` is compacted, any smaller `low'` is also compacted. -/
theorem mustCheckOutofbounds_compacted_mono (s : RaftLogSliceState)
    (lo1 lo2 : ℕ) (h : lo2 ≤ lo1)
    (hc : mustCheckOutofbounds s lo1 = BoundsCheck.compacted) :
    mustCheckOutofbounds s lo2 = BoundsCheck.compacted := by
  rw [mustCheckOutofbounds_compacted_iff] at *; omega

/-- At `first_index` exactly, the result is `ok`. -/
theorem mustCheckOutofbounds_ok_firstIndex (s : RaftLogSliceState) :
    mustCheckOutofbounds s s.firstIndex = BoundsCheck.ok := by
  simp [mustCheckOutofbounds]

/-- One below `first_index` gives `compacted`. -/
theorem mustCheckOutofbounds_compacted_below_first (s : RaftLogSliceState) (k : ℕ)
    (hk : k < s.firstIndex) :
    mustCheckOutofbounds s k = BoundsCheck.compacted := by
  simp [mustCheckOutofbounds]; omega

/-! ### Stability under state changes -/

/-- Decreasing `firstIndex` (log expansion toward the front) can only turn
    `compacted` results into `ok`. -/
theorem mustCheckOutofbounds_ok_of_smaller_first (s : RaftLogSliceState)
    (fi' : ℕ) (h : fi' ≤ s.firstIndex)
    (low : ℕ) (hok : mustCheckOutofbounds s low = BoundsCheck.ok) :
    mustCheckOutofbounds { s with firstIndex := fi', h_first_le_offset := by omega } low
      = BoundsCheck.ok := by
  simp [mustCheckOutofbounds] at *; omega

/-- Increasing `firstIndex` (compaction) cannot turn `compacted` into `ok`. -/
theorem mustCheckOutofbounds_compacted_of_larger_first (s : RaftLogSliceState)
    (fi' : ℕ) (h : s.firstIndex ≤ fi')
    (low : ℕ)
    (hc : mustCheckOutofbounds s low = BoundsCheck.compacted) :
    mustCheckOutofbounds { s with firstIndex := fi',
      h_first_le_offset := le_trans h s.h_first_le_offset } low
      = BoundsCheck.compacted := by
  simp [mustCheckOutofbounds] at *; omega

/-! ## Abstract slice model -/

/-- Abstract representation of a slice result: a count of contiguous index entries
    starting at `offset`.  We work with (offset, count) pairs rather than concrete
    lists, which lets all proofs stay in `ℕ`-arithmetic.

    `SliceResult (low n)` represents entries with indices `[low, low+n)`. -/
structure SliceResult where
  startIdx : ℕ
  count    : ℕ
  deriving Repr, DecidableEq

/-- How many index entries are in a slice result. -/
def SliceResult.size (r : SliceResult) : ℕ := r.count

/-- The exclusive upper bound of a slice result. -/
def SliceResult.high (r : SliceResult) : ℕ := r.startIdx + r.count

/-- The stable sub-range of a [low, high) request: [low, min(high, offset)). -/
def stableSubrange (s : RaftLogSliceState) (low high : ℕ) : SliceResult :=
  { startIdx := low, count := min high s.unstableOffset - low }

/-- The unstable sub-range of a [low, high) request: [max(low, offset), high). -/
def unstableSubrange (s : RaftLogSliceState) (low high : ℕ) : SliceResult :=
  { startIdx := max low s.unstableOffset,
    count    := high - max low s.unstableOffset }

/-! ### The split-point is `unstableOffset` -/

theorem stableSubrange_high_le_offset (s : RaftLogSliceState) (low high : ℕ) :
    (stableSubrange s low high).high ≤ s.unstableOffset := by
  unfold stableSubrange SliceResult.high
  simp; omega

theorem unstableSubrange_start_ge_offset (s : RaftLogSliceState) (low high : ℕ) :
    s.unstableOffset ≤ (unstableSubrange s low high).startIdx := by
  unfold unstableSubrange; simp; omega

/-- The two sub-ranges partition [low, high): their lengths sum to `high - low`. -/
theorem subrange_lengths_add (s : RaftLogSliceState) (low high : ℕ)
    (h : low ≤ high) :
    (stableSubrange s low high).count + (unstableSubrange s low high).count
      = high - low := by
  unfold stableSubrange unstableSubrange
  simp
  omega

/-- When the entire range is in stable storage (high ≤ offset),
    the stable part covers [low, high) and the unstable part is empty. -/
theorem stableSubrange_full_of_hi_le_offset (s : RaftLogSliceState) (low high : ℕ)
    (h_lo : low ≤ high) (h : high ≤ s.unstableOffset) :
    (stableSubrange s low high).count = high - low ∧
    (unstableSubrange s low high).count = 0 := by
  unfold stableSubrange unstableSubrange; simp; omega

/-- When the entire range is in the unstable buffer (low ≥ offset),
    the stable part is empty and the unstable part covers [low, high). -/
theorem unstableSubrange_full_of_lo_ge_offset (s : RaftLogSliceState) (low high : ℕ)
    (h_lo : low ≤ high) (h : s.unstableOffset ≤ low) :
    (stableSubrange s low high).count = 0 ∧
    (unstableSubrange s low high).count = high - low := by
  unfold stableSubrange unstableSubrange; simp; omega

/-- The total assembled length is `high - low` when `low ≤ high`. -/
theorem assembled_count_eq (s : RaftLogSliceState) (low high : ℕ) (h : low ≤ high) :
    (stableSubrange s low high).count + (unstableSubrange s low high).count
      = high - low :=
  subrange_lengths_add s low high h

/-! ### Bounds on assembled entries -/

/-- Every entry in the stable sub-range has index < unstableOffset. -/
theorem stableSubrange_indices_lt_offset (s : RaftLogSliceState) (low high : ℕ)
    (i : ℕ) (h_lo : low ≤ i)
    (h_hi : i < (stableSubrange s low high).high) :
    i < s.unstableOffset := by
  have := stableSubrange_high_le_offset s low high
  unfold SliceResult.high at *; omega

/-- Every entry in the unstable sub-range has index ≥ unstableOffset. -/
theorem unstableSubrange_indices_ge_offset (s : RaftLogSliceState) (low high : ℕ)
    (i : ℕ) (h_lo : (unstableSubrange s low high).startIdx ≤ i) :
    s.unstableOffset ≤ i := by
  have := unstableSubrange_start_ge_offset s low high
  omega

/-- All assembled entries have indices ≥ `low`. -/
theorem stableSubrange_start_ge_low (s : RaftLogSliceState) (low high : ℕ) :
    low ≤ (stableSubrange s low high).startIdx := by
  unfold stableSubrange; simp

theorem unstableSubrange_start_ge_low (s : RaftLogSliceState) (low high : ℕ) :
    low ≤ (unstableSubrange s low high).startIdx := by
  unfold unstableSubrange; simp; omega

/-- All assembled entries have indices < `high`. -/
theorem stableSubrange_entries_lt_high (s : RaftLogSliceState) (low high : ℕ)
    (h : low ≤ high) (i : ℕ)
    (h_lo : low ≤ i) (h_hi : i < (stableSubrange s low high).high) :
    i < high := by
  unfold stableSubrange SliceResult.high at *; simp at *; omega

theorem unstableSubrange_entries_lt_high (s : RaftLogSliceState) (low high : ℕ)
    (i : ℕ)
    (h_lo : (unstableSubrange s low high).startIdx ≤ i)
    (h_hi : i < (unstableSubrange s low high).high) :
    i < high := by
  unfold unstableSubrange SliceResult.high at *; simp at *; omega

/-! ### Monotonicity: widening the range adds entries -/

/-- Increasing `high` can only increase the count of both sub-ranges. -/
theorem stableSubrange_mono_high (s : RaftLogSliceState) (low hi1 hi2 : ℕ)
    (h : hi1 ≤ hi2) :
    (stableSubrange s low hi1).count ≤ (stableSubrange s low hi2).count := by
  unfold stableSubrange; simp; omega

theorem unstableSubrange_mono_high (s : RaftLogSliceState) (low hi1 hi2 : ℕ)
    (h : hi1 ≤ hi2) :
    (unstableSubrange s low hi1).count ≤ (unstableSubrange s low hi2).count := by
  unfold unstableSubrange; simp; omega

/-- Increasing `high` can only increase the total count. -/
theorem assembled_count_mono_high (s : RaftLogSliceState) (low hi1 hi2 : ℕ)
    (h : hi1 ≤ hi2) (hl : low ≤ hi1) :
    hi1 - low ≤ hi2 - low := by omega

/-- Increasing `low` can only decrease the total count. -/
theorem assembled_count_mono_low (s : RaftLogSliceState) (lo1 lo2 high : ℕ)
    (h : lo1 ≤ lo2) (hl : lo2 ≤ high) :
    high - lo2 ≤ high - lo1 := by omega

/-! ### Empty range -/

theorem stableSubrange_count_zero_of_low_eq_high (s : RaftLogSliceState) (low : ℕ) :
    (stableSubrange s low low).count = 0 := by
  unfold stableSubrange; simp

theorem unstableSubrange_count_zero_of_low_eq_high (s : RaftLogSliceState) (low : ℕ) :
    (unstableSubrange s low low).count = 0 := by
  unfold unstableSubrange; simp

theorem assembled_count_zero_of_low_eq_high (s : RaftLogSliceState) (low : ℕ) :
    (stableSubrange s low low).count + (unstableSubrange s low low).count = 0 := by
  simp [stableSubrange_count_zero_of_low_eq_high, unstableSubrange_count_zero_of_low_eq_high]

/-! ### Unstable buffer bounds -/

/-- Unstable sub-range ends at or before `logHigh`. -/
theorem unstableSubrange_high_le_logHigh (s : RaftLogSliceState) (low high : ℕ)
    (h : high ≤ logHigh s) :
    (unstableSubrange s low high).high ≤ logHigh s := by
  unfold unstableSubrange SliceResult.high; simp; omega

/-- When `high ≤ logHigh s`, the unstable sub-range stays within the unstable buffer. -/
theorem unstableSubrange_within_buffer (s : RaftLogSliceState) (low high : ℕ)
    (h_hi : high ≤ logHigh s) :
    (unstableSubrange s low high).high ≤ s.unstableOffset + s.unstableLen := by
  have := unstableSubrange_high_le_logHigh s low high h_hi
  unfold logHigh at this; exact this

/-! ### `mustCheckOutofbounds` + slice interaction -/

/-- If `mustCheckOutofbounds` is `ok`, the stable sub-range starts at `low ≥ firstIndex`. -/
theorem stableSubrange_start_ge_first (s : RaftLogSliceState) (low high : ℕ)
    (hok : mustCheckOutofbounds s low = BoundsCheck.ok) :
    s.firstIndex ≤ (stableSubrange s low high).startIdx := by
  rw [mustCheckOutofbounds_ok_iff] at hok
  unfold stableSubrange; simp; exact hok

/-- If `mustCheckOutofbounds` is `ok`, the unstable sub-range also starts ≥ firstIndex. -/
theorem unstableSubrange_start_ge_first (s : RaftLogSliceState) (low high : ℕ)
    (hok : mustCheckOutofbounds s low = BoundsCheck.ok) :
    s.firstIndex ≤ (unstableSubrange s low high).startIdx := by
  rw [mustCheckOutofbounds_ok_iff] at hok
  have h_off := s.h_first_le_offset
  have h_unst := unstableSubrange_start_ge_offset s low high
  unfold unstableSubrange at *; simp at *; omega

/-! ## Concrete `#eval` examples -/

-- bounds check: valid range entirely in stable
#eval mustCheckOutofbounds
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 120
-- expected: ok

-- bounds check: compacted
#eval mustCheckOutofbounds
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 99
-- expected: compacted

-- stable sub-range for a request spanning the split [148, 153)
#eval stableSubrange
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
-- expected: {startIdx := 148, count := 2}  (indices 148, 149)

-- unstable sub-range for a request spanning the split [148, 153)
#eval unstableSubrange
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
-- expected: {startIdx := 150, count := 3}  (indices 150, 151, 152)

-- fully in unstable [155, 160)
#eval unstableSubrange
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 155 160
-- expected: {startIdx := 155, count := 5}

-- decide: lengths add up
#eval decide ((stableSubrange
    { firstIndex := 1, unstableOffset := 5, unstableLen := 10,
      h_first_le_offset := by omega } 2 11).count +
  (unstableSubrange
    { firstIndex := 1, unstableOffset := 5, unstableLen := 10,
      h_first_le_offset := by omega } 2 11).count = 9)
-- expected: true (= 11 - 2)

-- decide: empty range
#eval decide ((stableSubrange
    { firstIndex := 1, unstableOffset := 5, unstableLen := 10,
      h_first_le_offset := by omega } 5 5).count +
  (unstableSubrange
    { firstIndex := 1, unstableOffset := 5, unstableLen := 10,
      h_first_le_offset := by omega } 5 5).count = 0)
-- expected: true

/-! ## Task 4 — Concrete implementation model: `sliceIndices`

  The `SliceResult` abstraction above tracks (startIdx, count) pairs — enough for
  reasoning about *how many* entries come from each storage tier. This section adds
  a concrete `List ℕ` model that enumerates the *actual index values* returned by
  `slice`, enabling membership-based reasoning.

  ### What is modelled
  - `sliceIndices low high : List ℕ` — the ordered list `[low, low+1, …, high-1]`
  - `stableSliceIndices` and `unstableSliceIndices` — the sub-lists corresponding
    to the two `store.entries` / `unstable.slice` reads in the Rust `slice` function.
  - Partition: every index in `[low, high)` belongs to exactly one tier.

  ### What is NOT modelled (same as above)
  - Entry content, terms, or data — only index identity.
  - Partial stable reads (modelled as always returning the full requested sub-range).
  - `max_size` byte budget (proved separately in `LimitSize.lean`).
-/

/-- The ordered list of entry indices returned by `slice(low, high)` when
    `mustCheckOutofbounds` returns `ok` and storage is complete.
    Concretely: `[low, low+1, …, high-1]`. -/
def sliceIndices (low high : ℕ) : List ℕ :=
  List.range' low (high - low)

/-! ### Basic characterisation -/

/-- An index `i` is in the slice result iff `low ≤ i < high`. -/
theorem sliceIndices_mem_iff (low high i : ℕ) :
    i ∈ sliceIndices low high ↔ low ≤ i ∧ i < high := by
  simp [sliceIndices, List.mem_range']
  omega

/-- The slice result has exactly `high - low` elements. -/
theorem sliceIndices_length (low high : ℕ) :
    (sliceIndices low high).length = high - low := by
  simp [sliceIndices]

/-- The slice result is empty iff the range is degenerate (`high ≤ low`). -/
theorem sliceIndices_empty_iff (low high : ℕ) :
    sliceIndices low high = [] ↔ high ≤ low := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hmem : low ∈ sliceIndices low high := by
      rw [sliceIndices_mem_iff]; omega
    exact absurd h (List.ne_nil_of_mem hmem)
  · intro h
    simp [sliceIndices, show high - low = 0 from Nat.sub_eq_zero_of_le h]

/-- The slice result has no duplicate indices. -/
theorem sliceIndices_nodup (low high : ℕ) : (sliceIndices low high).Nodup :=
  List.nodup_range' _ _

/-- All returned indices are ≥ `low`. -/
theorem sliceIndices_ge_low {low high i : ℕ} (h : i ∈ sliceIndices low high) :
    low ≤ i :=
  ((sliceIndices_mem_iff low high i).mp h).1

/-- All returned indices are < `high`. -/
theorem sliceIndices_lt_high {low high i : ℕ} (h : i ∈ sliceIndices low high) :
    i < high :=
  ((sliceIndices_mem_iff low high i).mp h).2

/-- The slice of an empty range contains no elements. -/
theorem sliceIndices_eq_high_empty (n : ℕ) : sliceIndices n n = [] := by
  simp [sliceIndices]

/-! ## Stable / unstable partition -/

/-- Indices in the slice sourced from **stable storage**: `[low, min(high, unstableOffset))`.
    Corresponds to `self.store.entries(low, min(high, offset), …)` in the Rust `slice`. -/
def stableSliceIndices (s : RaftLogSliceState) (low high : ℕ) : List ℕ :=
  List.range' low (min high s.unstableOffset - low)

/-- Indices in the slice sourced from the **unstable buffer**: `[max(low, unstableOffset), high)`.
    Corresponds to `self.unstable.slice(max(low, offset), high)` in the Rust `slice`. -/
def unstableSliceIndices (s : RaftLogSliceState) (low high : ℕ) : List ℕ :=
  List.range' (max low s.unstableOffset) (high - max low s.unstableOffset)

/-- Membership in `stableSliceIndices`. -/
theorem stableSliceIndices_mem_iff (s : RaftLogSliceState) (low high i : ℕ) :
    i ∈ stableSliceIndices s low high ↔ low ≤ i ∧ i < min high s.unstableOffset := by
  simp [stableSliceIndices, List.mem_range']
  omega

/-- Membership in `unstableSliceIndices`. -/
theorem unstableSliceIndices_mem_iff (s : RaftLogSliceState) (low high i : ℕ) :
    i ∈ unstableSliceIndices s low high ↔ max low s.unstableOffset ≤ i ∧ i < high := by
  simp [unstableSliceIndices, List.mem_range']
  omega

/-- Stable indices are strictly below `unstableOffset`. -/
theorem stableSliceIndices_lt_offset {s : RaftLogSliceState} {low high i : ℕ}
    (h : i ∈ stableSliceIndices s low high) : i < s.unstableOffset := by
  rw [stableSliceIndices_mem_iff] at h; omega

/-- Unstable indices are at or above `unstableOffset`. -/
theorem unstableSliceIndices_ge_offset {s : RaftLogSliceState} {low high i : ℕ}
    (h : i ∈ unstableSliceIndices s low high) : s.unstableOffset ≤ i := by
  rw [unstableSliceIndices_mem_iff] at h; omega

/-- Stable and unstable index sets are disjoint. -/
theorem stableUnstable_disjoint (s : RaftLogSliceState) (low high : ℕ) :
    ∀ i, ¬ (i ∈ stableSliceIndices s low high ∧ i ∈ unstableSliceIndices s low high) := by
  intro i
  simp only [stableSliceIndices_mem_iff, unstableSliceIndices_mem_iff]
  omega

/-- Every index in `[low, high)` is in the stable part, the unstable part, or both tiers
    share the boundary — key partition theorem.

    Formally: membership in `sliceIndices` is equivalent to membership in at least one tier. -/
theorem slice_coverage (s : RaftLogSliceState) (low high i : ℕ) :
    i ∈ sliceIndices low high ↔
    i ∈ stableSliceIndices s low high ∨ i ∈ unstableSliceIndices s low high := by
  simp only [sliceIndices_mem_iff, stableSliceIndices_mem_iff, unstableSliceIndices_mem_iff]
  omega

/-- Corollary: every element of either tier is a valid slice index. -/
theorem stableUnstable_subset_slice (s : RaftLogSliceState) (low high i : ℕ)
    (h : i ∈ stableSliceIndices s low high ∨ i ∈ unstableSliceIndices s low high) :
    i ∈ sliceIndices low high :=
  (slice_coverage s low high i).mpr h

/-- Stable index list has no duplicates. -/
theorem stableSliceIndices_nodup (s : RaftLogSliceState) (low high : ℕ) :
    (stableSliceIndices s low high).Nodup :=
  List.nodup_range' _ _

/-- Unstable index list has no duplicates. -/
theorem unstableSliceIndices_nodup (s : RaftLogSliceState) (low high : ℕ) :
    (unstableSliceIndices s low high).Nodup :=
  List.nodup_range' _ _

/-- The combined length of the two tiers equals the total slice length.
    This is the arithmetic dual of `subrange_lengths_add` for the concrete list model. -/
theorem stableUnstable_length_sum (s : RaftLogSliceState) (low high : ℕ) :
    (stableSliceIndices s low high).length + (unstableSliceIndices s low high).length =
    (sliceIndices low high).length := by
  simp [stableSliceIndices, unstableSliceIndices, sliceIndices]
  omega

/-- When the range is entirely in stable storage (`high ≤ unstableOffset`),
    the stable tier is the full slice and the unstable tier is empty. -/
theorem stableSlice_full_of_hi_le_offset (s : RaftLogSliceState) (low high : ℕ)
    (h : high ≤ s.unstableOffset) :
    stableSliceIndices s low high = sliceIndices low high ∧
    unstableSliceIndices s low high = [] := by
  have hmin : min high s.unstableOffset = high := Nat.min_eq_left h
  have hmax_ge : s.unstableOffset ≤ max low s.unstableOffset := Nat.le_max_right _ _
  constructor
  · simp [stableSliceIndices, sliceIndices, hmin]
  · simp only [unstableSliceIndices]
    have : high - max low s.unstableOffset = 0 := by omega
    simp [this]

/-- When the range is entirely in the unstable buffer (`unstableOffset ≤ low`),
    the unstable tier is the full slice and the stable tier is empty. -/
theorem unstableSlice_full_of_lo_ge_offset (s : RaftLogSliceState) (low high : ℕ)
    (h : s.unstableOffset ≤ low) :
    unstableSliceIndices s low high = sliceIndices low high ∧
    stableSliceIndices s low high = [] := by
  have hmax : max low s.unstableOffset = low := Nat.max_eq_left h
  have hmin_le : min high s.unstableOffset ≤ low := by omega
  constructor
  · simp [unstableSliceIndices, sliceIndices, hmax]
  · simp only [stableSliceIndices]
    have : min high s.unstableOffset - low = 0 := Nat.sub_eq_zero_of_le hmin_le
    simp [this]

/-! ### `#eval` examples for the concrete index model -/

-- All indices in [148, 153) for a log split at offset 150
#eval sliceIndices 148 153
-- expected: [148, 149, 150, 151, 152]

-- Stable part: [148, 150) read from stable storage
#eval stableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
-- expected: [148, 149]

-- Unstable part: [150, 153) read from the unstable buffer
#eval unstableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
-- expected: [150, 151, 152]

-- Partition coverage: every index in [148, 153) is in stable ∪ unstable
#eval decide (∀ i ∈ sliceIndices 148 153,
  i ∈ stableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
  ∨ i ∈ unstableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153)
-- expected: true

-- Disjointness: no index is in both stable and unstable
#eval decide (∀ i ∈ sliceIndices 148 153,
  ¬ (i ∈ stableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
  ∧ i ∈ unstableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153))
-- expected: true

-- Empty range: sliceIndices of equal bounds is []
#eval sliceIndices 5 5   -- expected: []
#eval sliceIndices 10 5  -- expected: [] (high < low)

/-! ## Task 5 — Partition list equality: `slice_partition` -/

/-- **Partition theorem (list equality)**: the full slice index list is the
    concatenation of the stable part followed by the unstable part (in index order).

    This is stronger than `slice_coverage` (which is a membership equivalence);
    it proves actual list identity:
    ```
    sliceIndices low high = stableSliceIndices s low high ++ unstableSliceIndices s low high
    ```

    Proof strategy — three cases on where `unstableOffset` falls:

    * **Case 1** (`high ≤ unstableOffset`): all stable, unstable is `[]`.
      Follows from `stableSlice_full_of_hi_le_offset` + `List.append_nil`.

    * **Case 2** (`unstableOffset ≤ low`): all unstable, stable is `[]`.
      Follows from `unstableSlice_full_of_lo_ge_offset` + `List.nil_append`.

    * **Case 3** (`low < unstableOffset < high`): mixed.
      `stable = List.range' low (unstableOffset - low)`,
      `unstable = List.range' unstableOffset (high - unstableOffset)`.
      Their concatenation equals `List.range' low (high - low)` by
      `List.range'_append` (using `low + (unstableOffset - low) = unstableOffset`
      and `(unstableOffset - low) + (high - unstableOffset) = high - low`). -/
theorem slice_partition (s : RaftLogSliceState) (low high : ℕ) :
    stableSliceIndices s low high ++ unstableSliceIndices s low high =
    sliceIndices low high := by
  simp only [stableSliceIndices, unstableSliceIndices, sliceIndices]
  rcases Nat.le_or_lt high s.unstableOffset with h1 | h1
  · -- Case 1: high ≤ unstableOffset — all stable
    have hmin : min high s.unstableOffset = high := Nat.min_eq_left h1
    have hmax_ge : s.unstableOffset ≤ max low s.unstableOffset := Nat.le_max_right _ _
    rw [hmin]
    have hzero : high - max low s.unstableOffset = 0 := by omega
    simp [hzero]
  · -- Case 1 not: unstableOffset < high
    rcases Nat.le_or_lt s.unstableOffset low with h2 | h2
    · -- Case 2: unstableOffset ≤ low — all unstable
      have hmax : max low s.unstableOffset = low := Nat.max_eq_left h2
      have hmin_le : min high s.unstableOffset ≤ low := by omega
      have hzero : min high s.unstableOffset - low = 0 := Nat.sub_eq_zero_of_le hmin_le
      simp [hmax, hzero]
    · -- Case 3: low < unstableOffset < high — mixed partition
      have hmin : min high s.unstableOffset = s.unstableOffset := by omega
      have hmax : max low s.unstableOffset = s.unstableOffset := by omega
      rw [hmin, hmax]
      -- Now goal: List.range' low (s.unstableOffset - low) ++
      --           List.range' s.unstableOffset (high - s.unstableOffset) =
      --           List.range' low (high - low)
      rw [← List.range'_append low (s.unstableOffset - low) (high - s.unstableOffset) 1]
      congr 1
      · -- start of second list: low + (unstableOffset - low) * 1 = unstableOffset
        omega
      · -- total length: (unstableOffset - low) + (high - unstableOffset) = high - low
        omega

/-- Corollary: `sliceIndices` is a permutation of stable ++ unstable. -/
theorem slice_partition_perm (s : RaftLogSliceState) (low high : ℕ) :
    (stableSliceIndices s low high ++ unstableSliceIndices s low high).Perm
    (sliceIndices low high) := by
  rw [slice_partition]; exact List.Perm.refl _

/-- Corollary: every member of the concatenated stable ++ unstable list is
    a member of `sliceIndices`. -/
theorem slice_partition_mem (s : RaftLogSliceState) (low high i : ℕ)
    (h : i ∈ stableSliceIndices s low high ∨ i ∈ unstableSliceIndices s low high) :
    i ∈ sliceIndices low high := by
  rw [← slice_partition]
  exact List.mem_append.mpr h

/-- Corollary: the total length via list append equals `sliceIndices` length. -/
theorem slice_partition_length (s : RaftLogSliceState) (low high : ℕ) :
    (stableSliceIndices s low high).length + (unstableSliceIndices s low high).length =
    (sliceIndices low high).length := by
  rw [← List.length_append, slice_partition]

-- Verify the partition equality concretely for [148, 153) with offset 150
#eval decide (
  stableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153 ++
  unstableSliceIndices
    { firstIndex := 101, unstableOffset := 150, unstableLen := 50,
      h_first_le_offset := by omega } 148 153
  = sliceIndices 148 153)
-- expected: true → [148, 149] ++ [150, 151, 152] = [148, 149, 150, 151, 152]

-- All-stable case: [148, 150) with offset 155 (all stable)
#eval decide (
  stableSliceIndices
    { firstIndex := 101, unstableOffset := 155, unstableLen := 10,
      h_first_le_offset := by omega } 148 150 ++
  unstableSliceIndices
    { firstIndex := 101, unstableOffset := 155, unstableLen := 10,
      h_first_le_offset := by omega } 148 150
  = sliceIndices 148 150)
-- expected: true → [148, 149] ++ [] = [148, 149]

-- All-unstable case: [160, 162) with offset 155 (all unstable)
#eval decide (
  stableSliceIndices
    { firstIndex := 101, unstableOffset := 155, unstableLen := 10,
      h_first_le_offset := by omega } 160 162 ++
  unstableSliceIndices
    { firstIndex := 101, unstableOffset := 155, unstableLen := 10,
      h_first_le_offset := by omega } 160 162
  = sliceIndices 160 162)
-- expected: true → [] ++ [160, 161] = [160, 161]
