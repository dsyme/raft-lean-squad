/-
  FVSquad/RaftLogEntries.lean

  Formal specification and proofs for `RaftLog::entries` from `src/raft_log.rs`.

  🔬 Lean Squad — automated formal verification for dsyme/fv-squad.

  ## What is modelled

  `RaftLog::entries(idx, max_size, context)` returns the entries in the log at
  indices `[idx, last_index]`, subject to a byte-size limit.

  The Rust implementation (paraphrased):
  ```rust
  pub fn entries(&self, idx: u64, max_size: Option<u64>, ...) -> Result<Vec<Entry>> {
      let last = self.last_index();
      if idx > last {
          return Ok(vec![]);   // out-of-range: empty result
      }
      self.slice(idx, last + 1, max_size, context)
  }
  ```

  This is a thin wrapper around `slice`.  The spec delegates to the
  `sliceIndices` / `RaftLogSliceState` model from `RaftLogSlice.lean`.

  ## Model: index sets, not entry content

  Following the established pattern (see `RaftLogSlice.lean`, `NextEntries.lean`),
  we model the *set of indices* returned rather than actual entry bytes.
  The `max_size`/`limit_size` byte budget is proved separately in `LimitSize.lean`.

  ## Key theorems (all 0 sorry)

  ### Empty branch
  - `entries_empty_of_idx_gt_last`  — if `idx > lastIdx s`, result is `[]`
  - `entries_empty_length`          — empty result has length 0

  ### Non-empty branch
  - `entries_nonempty_of_idx_le_last` — if `idx ≤ lastIdx s`, result is non-empty
  - `entries_eq_sliceIndices`         — entries returns `sliceIndices idx (logHigh s)`
  - `entries_length`                  — length = `logHigh s - idx` when in range
  - `entries_length_le_span`          — length ≤ `lastIdx s - idx + 1`

  ### Membership
  - `entries_mem_iff`                 — index `i` is returned iff `idx ≤ i < logHigh s`
  - `entries_ge_idx`                  — every returned index ≥ `idx`
  - `entries_lt_logHigh`              — every returned index < `logHigh s`
  - `entries_ge_firstIndex`           — every returned index ≥ `firstIndex`
  - `entries_le_lastIdx`              — every returned index ≤ `lastIdx s`

  ### Structural
  - `entries_nodup`                   — result has no duplicates
  - `entries_prefix_of_idx_le`        — smaller `idx` gives a superset of results

  ## What is NOT modelled

  * Entry content (bytes, terms, commands) — only index ranges.
  * Storage I/O errors (`Result` wrapper) — modelled as always succeeding.
  * `max_size`/`limit_size` byte budget — proved separately in `LimitSize.lean`.
  * `GetEntriesContext` pagination/priority hints — irrelevant to index set.
  * Compaction races — treated as atomic.
  * Panics — modelled as preconditions.
-/

import Mathlib.Tactic
import FVSquad.RaftLogSlice

open FVSquad.RaftLogSlice

namespace FVSquad.RaftLogEntries

/-! ## Core model -/

/-- `raftLogEntries s idx` — model of `RaftLog::entries(idx, _, _)`.

    Returns the list of entry indices that would be returned:
    - `[]` if `idx > lastIdx s` (out-of-range guard)
    - `sliceIndices idx (logHigh s)` otherwise (delegate to slice)

    Mirrors the Rust implementation exactly: the `idx > last` guard maps to
    `idx > lastIdx s`; the `slice(idx, last+1, ...)` call maps to
    `sliceIndices idx (lastIdx s + 1) = sliceIndices idx (logHigh s)`. -/
def raftLogEntries (s : RaftLogSliceState) (idx : ℕ) : List ℕ :=
  if idx > lastIdx s then []
  else sliceIndices idx (logHigh s)

/-! ## Lemmas about the structure of `raftLogEntries` -/

/-- `raftLogEntries` returns `[]` on the empty-range path. -/
@[simp]
theorem raftLogEntries_gt (s : RaftLogSliceState) (idx : ℕ) (h : lastIdx s < idx) :
    raftLogEntries s idx = [] := by
  simp [raftLogEntries, h]

/-- `raftLogEntries` delegates to `sliceIndices` on the in-range path. -/
@[simp]
theorem raftLogEntries_le (s : RaftLogSliceState) (idx : ℕ) (h : idx ≤ lastIdx s) :
    raftLogEntries s idx = sliceIndices idx (logHigh s) := by
  simp [raftLogEntries, Nat.not_lt.mpr h]

/-! ## Empty-branch theorems -/

/-- ENTRIES-EMPTY-1: If `idx > lastIdx s`, `raftLogEntries` returns `[]`. -/
theorem entries_empty_of_idx_gt_last (s : RaftLogSliceState) (idx : ℕ)
    (h : lastIdx s < idx) :
    raftLogEntries s idx = [] :=
  raftLogEntries_gt s idx h

/-- ENTRIES-EMPTY-2: The empty result has length 0. -/
theorem entries_empty_length (s : RaftLogSliceState) (idx : ℕ)
    (h : lastIdx s < idx) :
    (raftLogEntries s idx).length = 0 := by
  simp [entries_empty_of_idx_gt_last s idx h]

/-! ## Non-empty-branch theorems -/

/-- ENTRIES-NE-1: If `idx ≤ lastIdx s`, the result is non-empty. -/
theorem entries_nonempty_of_idx_le_last (s : RaftLogSliceState) (idx : ℕ)
    (h : idx ≤ lastIdx s) :
    raftLogEntries s idx ≠ [] := by
  rw [raftLogEntries_le s idx h]
  rw [sliceIndices_empty_iff]
  push_neg
  -- Need `idx < logHigh s`; since `idx ≤ lastIdx s` and `logHigh s = lastIdx s + 1`:
  unfold logHigh lastIdx at *
  omega

/-- ENTRIES-NE-2: `raftLogEntries` equals `sliceIndices idx (logHigh s)` iff `idx ≤ lastIdx s`. -/
theorem entries_eq_sliceIndices (s : RaftLogSliceState) (idx : ℕ)
    (h : idx ≤ lastIdx s) :
    raftLogEntries s idx = sliceIndices idx (logHigh s) :=
  raftLogEntries_le s idx h

/-- ENTRIES-LEN: When in range, length equals `logHigh s - idx`. -/
theorem entries_length (s : RaftLogSliceState) (idx : ℕ)
    (h : idx ≤ lastIdx s) :
    (raftLogEntries s idx).length = logHigh s - idx := by
  rw [entries_eq_sliceIndices s idx h, sliceIndices_length]

/-- ENTRIES-LEN-BOUND: Length ≤ `lastIdx s - idx + 1`. -/
theorem entries_length_le_span (s : RaftLogSliceState) (idx : ℕ)
    (h : idx ≤ lastIdx s) :
    (raftLogEntries s idx).length ≤ lastIdx s - idx + 1 := by
  rw [entries_length s idx h]
  unfold logHigh lastIdx
  omega

/-! ## Membership theorems -/

/-- ENTRIES-MEM-IFF: Index `i` is in the result iff `idx ≤ i < logHigh s`
    (and we are in the non-empty branch). -/
theorem entries_mem_iff (s : RaftLogSliceState) (idx i : ℕ)
    (h : idx ≤ lastIdx s) :
    i ∈ raftLogEntries s idx ↔ idx ≤ i ∧ i < logHigh s := by
  rw [entries_eq_sliceIndices s idx h, sliceIndices_mem_iff]

/-- ENTRIES-GE-IDX: Every returned index ≥ `idx`. -/
theorem entries_ge_idx (s : RaftLogSliceState) (idx i : ℕ)
    (h : idx ≤ lastIdx s) (hmem : i ∈ raftLogEntries s idx) :
    idx ≤ i := by
  rw [entries_mem_iff s idx i h] at hmem; exact hmem.1

/-- ENTRIES-LT-LOGHIGH: Every returned index < `logHigh s`. -/
theorem entries_lt_logHigh (s : RaftLogSliceState) (idx i : ℕ)
    (h : idx ≤ lastIdx s) (hmem : i ∈ raftLogEntries s idx) :
    i < logHigh s := by
  rw [entries_mem_iff s idx i h] at hmem; exact hmem.2

/-- ENTRIES-GE-FIRST: Every returned index ≥ `s.firstIndex`.
    Follows from `idx ≥ firstIndex` (precondition on `entries`: idx is valid). -/
theorem entries_ge_firstIndex (s : RaftLogSliceState) (idx i : ℕ)
    (h : idx ≤ lastIdx s)
    (h_first : s.firstIndex ≤ idx)
    (hmem : i ∈ raftLogEntries s idx) :
    s.firstIndex ≤ i := by
  have hge := entries_ge_idx s idx i h hmem
  omega

/-- ENTRIES-LE-LAST: Every returned index ≤ `lastIdx s`. -/
theorem entries_le_lastIdx (s : RaftLogSliceState) (idx i : ℕ)
    (h : idx ≤ lastIdx s) (hmem : i ∈ raftLogEntries s idx) :
    i ≤ lastIdx s := by
  have hlt := entries_lt_logHigh s idx i h hmem
  unfold logHigh lastIdx at *
  omega

/-! ## Structural theorems -/

/-- ENTRIES-NODUP: The result list has no duplicate indices. -/
theorem entries_nodup (s : RaftLogSliceState) (idx : ℕ) :
    (raftLogEntries s idx).Nodup := by
  unfold raftLogEntries
  split_ifs with hgt
  · exact List.nodup_nil
  · exact sliceIndices_nodup idx (logHigh s)

/-- ENTRIES-MONOTONE: Decreasing `idx` expands the result list (superset of indices). -/
theorem entries_idx_mono (s : RaftLogSliceState) (idx1 idx2 : ℕ)
    (hle : idx1 ≤ idx2) (h2 : idx2 ≤ lastIdx s) (h1 : idx1 ≤ lastIdx s) :
    ∀ i, i ∈ raftLogEntries s idx2 → i ∈ raftLogEntries s idx1 := by
  intro i himem
  rw [entries_mem_iff s idx2 i h2] at himem
  rw [entries_mem_iff s idx1 i h1]
  exact ⟨le_trans hle himem.1, himem.2⟩

/-- ENTRIES-FULL: When `idx = firstIndex`, the result covers the entire log. -/
theorem entries_full (s : RaftLogSliceState) (h : s.firstIndex ≤ lastIdx s) :
    raftLogEntries s s.firstIndex = sliceIndices s.firstIndex (logHigh s) :=
  entries_eq_sliceIndices s s.firstIndex h

/-! ## Relationship to `entries` vs `slice` -/

/-- ENTRIES-SLICE-EQUIV: `raftLogEntries s idx` and
    `sliceIndices idx (logHigh s)` have the same length when in range.

    This is the quantitative form of the "entries delegates to slice" property. -/
theorem entries_slice_length_eq (s : RaftLogSliceState) (idx : ℕ)
    (h : idx ≤ lastIdx s) :
    (raftLogEntries s idx).length =
    (sliceIndices idx (logHigh s)).length := by
  rw [entries_eq_sliceIndices s idx h]

/-- ENTRIES-NONE-IFF: `raftLogEntries s idx = []` iff `lastIdx s < idx`. -/
theorem entries_none_iff (s : RaftLogSliceState) (idx : ℕ) :
    raftLogEntries s idx = [] ↔ lastIdx s < idx := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    exact entries_nonempty_of_idx_le_last s idx hle h
  · intro h
    exact entries_empty_of_idx_gt_last s idx h

/-! ## Examples -/

section Examples

/-- Log: firstIndex=1, unstableOffset=5, unstableLen=3 (logHigh=8, lastIdx=7). -/
private def exS : RaftLogSliceState :=
  { firstIndex := 1, unstableOffset := 5, unstableLen := 3,
    h_first_le_offset := by omega }

-- `entries 3` should return [3, 4, 5, 6, 7]
#eval raftLogEntries exS 3   -- expected: [3, 4, 5, 6, 7]

-- `entries 5` should return [5, 6, 7]
#eval raftLogEntries exS 5   -- expected: [5, 6, 7]

-- `entries 8` should return [] (8 > lastIdx=7)
#eval raftLogEntries exS 8   -- expected: []

-- `entries 7` (last entry only)
#eval raftLogEntries exS 7   -- expected: [7]

-- Length check: entries 3 has length 5 = logHigh - idx = 8 - 3
#eval (raftLogEntries exS 3).length  -- expected: 5

-- Membership: 5 ∈ entries 3
#eval (raftLogEntries exS 3).contains 5  -- expected: true

-- Membership: 8 ∉ entries 3
#eval (raftLogEntries exS 3).contains 8  -- expected: false

-- Boundary: entries at firstIndex
#eval raftLogEntries exS 1   -- expected: [1, 2, 3, 4, 5, 6, 7]

-- Empty log: firstIndex = unstableOffset = 1, unstableLen = 0 → lastIdx = 0 < 1
private def emptyS : RaftLogSliceState :=
  { firstIndex := 1, unstableOffset := 1, unstableLen := 0,
    h_first_le_offset := by omega }
#eval raftLogEntries emptyS 1  -- expected: [] (lastIdx = 0, idx = 1 > 0)

end Examples

/-! ## Summary

**Phase 5 — Proofs** (raftlog_entries):

Theorems in this file (all 0 sorry):

| Theorem | Description |
|---------|-------------|
| `raftLogEntries_gt`            | `[]` when `idx > lastIdx s` |
| `raftLogEntries_le`            | delegates to `sliceIndices` when `idx ≤ lastIdx s` |
| `entries_empty_of_idx_gt_last` | ENTRIES-EMPTY-1 |
| `entries_empty_length`         | ENTRIES-EMPTY-2 |
| `entries_nonempty_of_idx_le_last` | ENTRIES-NE-1: result non-empty |
| `entries_eq_sliceIndices`      | ENTRIES-NE-2: exact delegation to slice |
| `entries_length`               | ENTRIES-LEN: length = `logHigh - idx` |
| `entries_length_le_span`       | ENTRIES-LEN-BOUND: length ≤ span |
| `entries_mem_iff`              | ENTRIES-MEM-IFF: membership characterisation |
| `entries_ge_idx`               | ENTRIES-GE-IDX |
| `entries_lt_logHigh`           | ENTRIES-LT-LOGHIGH |
| `entries_ge_firstIndex`        | ENTRIES-GE-FIRST |
| `entries_le_lastIdx`           | ENTRIES-LE-LAST |
| `entries_nodup`                | ENTRIES-NODUP |
| `entries_idx_mono`             | ENTRIES-MONOTONE: smaller idx ⇒ superset |
| `entries_full`                 | ENTRIES-FULL: idx=firstIndex covers log |
| `entries_slice_length_eq`      | ENTRIES-SLICE-EQUIV |
| `entries_none_iff`             | ENTRIES-NONE-IFF: `[] ↔ lastIdx < idx` |

🔬 Lean Squad — automated formal verification.
-/

end FVSquad.RaftLogEntries
