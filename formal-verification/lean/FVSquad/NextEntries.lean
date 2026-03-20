/-
  FVSquad/NextEntries.lean

  Formal specification and proofs for `RaftLog::next_entries_since` and
  its helper `applied_index_upper_bound` from `src/raft_log.rs`.

  🔬 Lean Squad — automated formal verification for dsyme/fv-squad.

  ## What is modelled

  `next_entries_since(since_idx, max_size)` returns the next slice of log entries
  ready to be applied to the application state machine.  The slice is bounded by:
  - `applied_index_upper_bound = min(committed, persisted + limit)` — the inclusive
    upper end of ready-to-apply entries.
  - `offset = max(since_idx + 1, first_index)` — the inclusive lower end.

  Returns `Some(entries[offset..high))` if `high > offset`, else `None`.

  ## What is NOT modelled
  - The actual entry content (bytes, terms, commands) — indices only.
  - Storage I/O, protobuf, logging.
  - `max_size` / `limit_size` byte budget (proved separately in `LimitSize.lean`).
  - Panics (modelled as precondition violations).
  - Snapshot restore interaction (treated as atomic state update).
-/

import Mathlib.Tactic

/-! ## Raft log state -/

/-- Abstract state of a `RaftLog<T>` relevant to `next_entries_since`. -/
structure RaftLogState where
  firstIndex  : ℕ
  committed   : ℕ
  persisted   : ℕ
  limit       : ℕ   -- max_apply_unpersisted_log_limit
  deriving Repr

/-! ## applied_index_upper_bound -/

/-- `applied_index_upper_bound()` in Rust.
    Defined as `min(committed, persisted + limit)`. -/
def appliedIndexUpperBound (s : RaftLogState) : ℕ :=
  min s.committed (s.persisted + s.limit)

/-! ### Bounds on `appliedIndexUpperBound` -/

theorem appliedIndexUpperBound_le_committed (s : RaftLogState) :
    appliedIndexUpperBound s ≤ s.committed := by
  unfold appliedIndexUpperBound; omega

theorem appliedIndexUpperBound_le_persisted_add (s : RaftLogState) :
    appliedIndexUpperBound s ≤ s.persisted + s.limit := by
  unfold appliedIndexUpperBound; omega

/-- `aub` is sandwiched between `min(committed, persisted+limit)` — definitional. -/
theorem appliedIndexUpperBound_eq (s : RaftLogState) :
    appliedIndexUpperBound s = min s.committed (s.persisted + s.limit) := rfl

/-! ### Monotonicity of `appliedIndexUpperBound` -/

/-- Increasing `committed` cannot decrease `aub`. Stated with explicit record update. -/
theorem appliedIndexUpperBound_mono_committed
    (s : RaftLogState) (c' : ℕ) (h : s.committed ≤ c') :
    appliedIndexUpperBound s ≤ appliedIndexUpperBound { s with committed := c' } := by
  unfold appliedIndexUpperBound
  omega

theorem aub_mono_committed (c c' p lim : ℕ) (h : c ≤ c') :
    min c (p + lim) ≤ min c' (p + lim) := by
  omega

theorem aub_mono_persisted (c p p' lim : ℕ) (h : p ≤ p') :
    min c (p + lim) ≤ min c (p' + lim) := by
  omega

theorem aub_mono_limit (c p lim lim' : ℕ) (h : lim ≤ lim') :
    min c (p + lim) ≤ min c (p + lim') := by
  omega

/-! ### Special cases -/

/-- When `limit = 0`, `aub = min(committed, persisted)`. -/
theorem aub_limit_zero (c p : ℕ) :
    min c (p + 0) = min c p := by simp

/-- When `persisted + limit ≥ committed`, `aub = committed` (no unpersisted cap). -/
theorem aub_eq_committed_of_ge (c p lim : ℕ) (h : c ≤ p + lim) :
    min c (p + lim) = c := by
  omega

/-- When `committed > persisted + limit`, `aub = persisted + limit`. -/
theorem aub_eq_persisted_add_of_lt (c p lim : ℕ) (h : p + lim < c) :
    min c (p + lim) = p + lim := by
  omega

/-! ## Window computation -/

/-- Lower bound of the window: `max(since_idx + 1, first_index)`. -/
def windowOffset (s : RaftLogState) (since : ℕ) : ℕ :=
  max (since + 1) s.firstIndex

/-- Upper bound (exclusive) of the window: `applied_index_upper_bound + 1`. -/
def windowHigh (s : RaftLogState) : ℕ :=
  appliedIndexUpperBound s + 1

/-- The window is non-empty iff `high > offset`. -/
def windowNonEmpty (s : RaftLogState) (since : ℕ) : Prop :=
  windowOffset s since < windowHigh s

/-! ### Properties of the offset -/

/-- Offset is always ≥ `first_index`. -/
theorem windowOffset_ge_first (s : RaftLogState) (since : ℕ) :
    s.firstIndex ≤ windowOffset s since := by
  unfold windowOffset; omega

/-- Offset is always ≥ `since + 1`. -/
theorem windowOffset_ge_since_succ (s : RaftLogState) (since : ℕ) :
    since + 1 ≤ windowOffset s since := by
  unfold windowOffset; omega

/-- A larger `since_idx` gives a larger offset (monotone). -/
theorem windowOffset_mono_since (s : RaftLogState) (a b : ℕ) (h : a ≤ b) :
    windowOffset s a ≤ windowOffset s b := by
  unfold windowOffset; omega

/-- Offset is strictly positive when `first_index ≥ 1`. -/
theorem windowOffset_pos_of_first_pos (s : RaftLogState) (since : ℕ)
    (hf : 1 ≤ s.firstIndex) : 1 ≤ windowOffset s since := by
  unfold windowOffset; omega

/-! ### Non-empty window characterisation -/

/-- The window is non-empty iff `aub ≥ offset`. -/
theorem windowNonEmpty_iff (s : RaftLogState) (since : ℕ) :
    windowNonEmpty s since ↔
    max (since + 1) s.firstIndex ≤ appliedIndexUpperBound s := by
  unfold windowNonEmpty windowOffset windowHigh
  omega

/-- The window is non-empty iff `aub ≥ since + 1` AND `aub ≥ first_index`. -/
theorem windowNonEmpty_iff' (s : RaftLogState) (since : ℕ) :
    windowNonEmpty s since ↔
    since + 1 ≤ appliedIndexUpperBound s ∧ s.firstIndex ≤ appliedIndexUpperBound s := by
  rw [windowNonEmpty_iff]
  omega

/-- If the window is non-empty, `aub ≥ first_index`. -/
theorem windowNonEmpty_aub_ge_first (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) : s.firstIndex ≤ appliedIndexUpperBound s := by
  rw [windowNonEmpty_iff'] at h; exact h.2

/-- If the window is non-empty, `aub > since`. -/
theorem windowNonEmpty_aub_gt_since (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) : since < appliedIndexUpperBound s := by
  rw [windowNonEmpty_iff'] at h; omega

/-! ### Window size -/

/-- Window size = `high - offset` (in ℕ subtraction, valid because `high > offset`). -/
def windowSize (s : RaftLogState) (since : ℕ) : ℕ :=
  windowHigh s - windowOffset s since

/-- When non-empty, window size ≥ 1. -/
theorem windowSize_pos_of_nonEmpty (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) : 1 ≤ windowSize s since := by
  unfold windowSize windowNonEmpty at *
  omega

/-- Window size is bounded above by `aub - first_index + 1`. -/
theorem windowSize_le_aub_minus_first (s : RaftLogState) (since : ℕ) :
    windowSize s since ≤ appliedIndexUpperBound s + 1 - s.firstIndex := by
  unfold windowSize windowHigh windowOffset
  omega

/-! ### `next_entries_since` model -/

/-- The result type: `None` if window is empty, `Some windowSize` otherwise.
    (We model the *number* of ready entries; actual content is storage-dependent.) -/
def nextEntriesSinceCount (s : RaftLogState) (since : ℕ) : Option ℕ :=
  if windowNonEmpty s since then some (windowSize s since)
  else none

/-- Returns `none` when window is empty. -/
theorem nextEntriesSinceCount_none_iff (s : RaftLogState) (since : ℕ) :
    nextEntriesSinceCount s since = none ↔ ¬ windowNonEmpty s since := by
  unfold nextEntriesSinceCount
  by_cases h : windowNonEmpty s since <;> simp [h]

/-- Returns `some` when window is non-empty. -/
theorem nextEntriesSinceCount_some_iff (s : RaftLogState) (since : ℕ) :
    (∃ n, nextEntriesSinceCount s since = some n) ↔ windowNonEmpty s since := by
  unfold nextEntriesSinceCount
  by_cases h : windowNonEmpty s since <;> simp [h]

/-- When non-empty, count ≥ 1. -/
theorem nextEntriesSinceCount_pos (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) :
    ∃ n, nextEntriesSinceCount s since = some n ∧ 1 ≤ n := by
  refine ⟨windowSize s since, ?_, windowSize_pos_of_nonEmpty s since h⟩
  simp [nextEntriesSinceCount, h]

/-! ### Bounds on returned entries -/

/-- All returned entry indices are ≤ `committed`. -/
theorem nextEntries_indices_le_committed (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) (i : ℕ)
    (hi : windowOffset s since ≤ i) (hi2 : i < windowHigh s) :
    i ≤ s.committed := by
  have hb := appliedIndexUpperBound_le_committed s
  unfold windowHigh at hi2
  omega

/-- All returned entry indices are ≥ `first_index`. -/
theorem nextEntries_indices_ge_first (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) (i : ℕ)
    (hi : windowOffset s since ≤ i) :
    s.firstIndex ≤ i := by
  have := windowOffset_ge_first s since
  omega

/-- All returned entry indices are ≤ `persisted + limit`. -/
theorem nextEntries_indices_le_persisted_add (s : RaftLogState) (since : ℕ)
    (h : windowNonEmpty s since) (i : ℕ)
    (hi : windowOffset s since ≤ i) (hi2 : i < windowHigh s) :
    i ≤ s.persisted + s.limit := by
  have hb := appliedIndexUpperBound_le_persisted_add s
  unfold windowHigh at hi2
  omega

/-! ### Monotonicity in `since_idx` -/

/-- A larger `since` never extends the window downward. -/
theorem nextEntries_since_mono (s : RaftLogState) (a b : ℕ) (h : a ≤ b) :
    windowOffset s a ≤ windowOffset s b := windowOffset_mono_since s a b h

/-- If the window is non-empty for `b`, it may be empty for `a ≤ b`. -/
theorem windowNonEmpty_of_smaller_since (s : RaftLogState) (a b : ℕ) (h : a ≤ b)
    (hb : windowNonEmpty s b) : windowNonEmpty s a := by
  rw [windowNonEmpty_iff] at *
  have := windowOffset_mono_since s a b h
  omega

/-! ### Stability: committed-only advancement -/

/-- Advancing committed (holding persisted fixed) only expands the applicable window. -/
theorem aub_expanded_by_commit (p lim c c' : ℕ) (h : c ≤ c') :
    min c (p + lim) ≤ min c' (p + lim) := aub_mono_committed c c' p lim h

/-! ## Concrete examples using `#eval` / `decide` -/

-- Example 1: normal window
#eval (
  let s : RaftLogState := { firstIndex := 1, committed := 10, persisted := 10, limit := 0 }
  nextEntriesSinceCount s 5
)  -- expected: some 5

-- Example 2: window empty (applied == committed)
#eval (
  let s : RaftLogState := { firstIndex := 1, committed := 5, persisted := 5, limit := 0 }
  nextEntriesSinceCount s 5
)  -- expected: none

-- Example 3: unpersisted cap active
#eval (
  let s : RaftLogState := { firstIndex := 1, committed := 100, persisted := 10, limit := 5 }
  nextEntriesSinceCount s 0
)  -- expected: some 15  (aub=15, offset=1, window=[1..16), size=15)

-- Example 4: log compacted ahead of since_idx
#eval (
  let s : RaftLogState := { firstIndex := 15, committed := 20, persisted := 20, limit := 0 }
  nextEntriesSinceCount s 5
)  -- expected: some 6   (aub=20, offset=max(6,15)=15, window=[15..21), size=6)

-- Decidable check: in Example 1, the window is non-empty
#eval decide (windowNonEmpty { firstIndex := 1, committed := 10, persisted := 10, limit := 0 } 5)
-- expected: true

-- Decidable check: in Example 2, the window is empty
#eval decide (¬ windowNonEmpty { firstIndex := 1, committed := 5, persisted := 5, limit := 0 } 5)
-- expected: true
