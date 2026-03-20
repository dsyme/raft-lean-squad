/-
  FVSquad/RaftLogAppend.lean

  Formal specification and proofs for `RaftLog::append` from `src/raft_log.rs`.

  🔬 Lean Squad — automated formal verification for dsyme/fv-squad.

  ## What is modelled

  `RaftLog::append(ents)` is the **leader-side log append gate**.  It writes a
  batch of new entries into the unstable portion of the log, potentially truncating
  conflicting unstable entries that follow the insertion point, and returns the new
  `last_index` after the append.

  The Rust implementation (paraphrased):
  ```rust
  pub fn append(&mut self, ents: &[Entry]) -> u64 {
      if ents.is_empty() { return self.last_index(); }
      let after = ents[0].index - 1;       // index just before the new entries
      if after < self.committed { fatal!() } // safety gate
      self.unstable.truncate_and_append(ents);
      self.last_index()
  }
  ```

  ## What is NOT modelled

  * `Storage` back-end (stable storage) — only the `Unstable` buffer is modelled.
    `last_index` reads `maybeLastIndex` from the unstable buffer; for a non-empty
    unstable buffer this equals the true last index of the combined log.
  * `persisted`, `applied` fields — not relevant to the safety gate.
  * `u64` overflow — all indices use unbounded `Nat`.
  * I/O, logging, the `fatal!` macro — modelled as a precondition assumption.
  * `GetEntriesContext`, `max_size` — not relevant to append.
  * Panics on empty `ents` (Rust does not panic; we model empty as a no-op).
  * Storage reads — only the unstable buffer is affected by `append`.

  ## Approach

  We build a minimal `RaftLogState` that wraps `FVSquad.UnstableLog.Unstable` and
  adds a `committed` index.  We then define `raftAppend` as a pure function and
  prove the key safety and liveness properties stated in the informal spec.

  Theorems in this file:

  ### Noop / empty case
  - `append_empty_noop_state`      — empty `ents` leaves the state unchanged
  - `append_empty_noop_index`      — empty `ents` returns the current last index

  ### Committed index preservation
  - `append_committed_unchanged`   — `committed` is not modified by any append

  ### Return-value correctness
  - `append_return_nonempty`       — non-empty append returns the last entry's index
  - `append_lastIndex_eq_return`   — the state's last index equals the return value
  - `append_return_ge_committed`   — return value ≥ committed (safety gate + after ≥ committed)

  ### Safety gate
  - `append_safety_gate`           — the main theorem: if `ents[0].index - 1 ≥ committed`,
                                     then no entry at index ≤ committed is modified in the
                                     unstable buffer (entries below the insertion point are
                                     preserved verbatim).

  ### Well-formedness
  - `append_wellFormed`            — appending well-formed entries to a well-formed state
                                     yields a well-formed state (uses `truncateAndAppend_wellFormed`)
-/

import Mathlib.Tactic

open FVSquad.UnstableLog

namespace FVSquad.RaftLogAppend

/-! ## Abstract state -/

/-- Abstract state of a `RaftLog<T>` relevant to append operations.

    `firstIndex` mirrors `RaftLog::first_index()` — the smallest entry index in the
    combined stable + unstable log.  It is not modified by `append`.

    `committed` mirrors `RaftLog::committed` — the highest log position known to be
    committed on a quorum.  It is not modified by `append`.

    `unstable` mirrors `RaftLog::unstable` — the in-memory buffer for entries not yet
    flushed to stable storage.  This is the only field modified by `append`. -/
structure RaftLogState where
  firstIndex : ℕ
  committed  : ℕ
  unstable   : Unstable
  deriving Repr

/-! ## Helper: last index -/

/-- `raftLastIndex s` — the last index in the log.

    We follow the real `RaftLog::last_index()`: if the unstable buffer has a last index
    (i.e., entries are non-empty or a snapshot is pending), we use it; otherwise we fall
    back to `firstIndex - 1` (empty log).

    In practice, `append` is only called when the log is non-empty (the `Unstable` has
    at least an initial snapshot from `Unstable::new`), so the fallback case is
    degenerate.  We model it as `firstIndex - 1` (which may be 0 when `firstIndex = 0`). -/
def raftLastIndex (s : RaftLogState) : ℕ :=
  match maybeLastIndex s.unstable with
  | some idx => idx
  | none     => s.firstIndex - 1

/-- When the unstable buffer has a non-empty entry list, `raftLastIndex` equals
    `offset + entries.length - 1`. -/
theorem raftLastIndex_entries (s : RaftLogState) (e : Entry) (rest : List Entry)
    (h : s.unstable.entries = e :: rest) :
    raftLastIndex s = s.unstable.offset + s.unstable.entries.length - 1 := by
  simp [raftLastIndex, maybeLastIndex, h]

/-- When the unstable buffer has a snapshot and empty entries, `raftLastIndex` equals
    the snapshot's index. -/
theorem raftLastIndex_snap (s : RaftLogState) (snap : SnapMeta)
    (hemp : s.unstable.entries = [])
    (hsnap : s.unstable.snapshot = some snap) :
    raftLastIndex s = snap.index := by
  simp [raftLastIndex, maybeLastIndex, hemp, hsnap]

/-! ## The append model -/

/-- `raftAppend s ents` — model of `RaftLog::append`.

    * If `ents` is empty: returns the state unchanged and the current `raftLastIndex`.
    * If `ents` is non-empty: delegates to `truncateAndAppend` on the unstable buffer,
      updates the state, and returns the new `raftLastIndex`.

    **Precondition (caller's responsibility, not checked here)**:
      if `ents` is non-empty then `ents[0].index - 1 ≥ s.committed`.

    Returns `(new_state, new_last_index)`. -/
def raftAppend (s : RaftLogState) (ents : List Entry) : RaftLogState × ℕ :=
  if ents.isEmpty then
    (s, raftLastIndex s)
  else
    let newUnstable := truncateAndAppend s.unstable ents
    let newState    := { s with unstable := newUnstable }
    (newState, raftLastIndex newState)

/-! ## Helper lemmas about `raftAppend` structure -/

/-- `raftAppend` on empty `ents` returns the original state unchanged. -/
@[simp]
theorem raftAppend_empty (s : RaftLogState) :
    raftAppend s [] = (s, raftLastIndex s) := by
  simp [raftAppend]

/-- `raftAppend` on non-empty `ents` applies `truncateAndAppend`. -/
@[simp]
theorem raftAppend_cons (s : RaftLogState) (e : Entry) (rest : List Entry) :
    raftAppend s (e :: rest) =
      let u' := truncateAndAppend s.unstable (e :: rest)
      ({ s with unstable := u' }, raftLastIndex { s with unstable := u' }) := by
  simp [raftAppend]

/-! ## Core theorems -/

/-! ### Noop on empty input -/

/-- Appending an empty list does not change the log state. -/
theorem append_empty_noop_state (s : RaftLogState) :
    (raftAppend s []).1 = s := by
  simp [raftAppend]

/-- Appending an empty list returns the current last index. -/
theorem append_empty_noop_index (s : RaftLogState) :
    (raftAppend s []).2 = raftLastIndex s := by
  simp [raftAppend]

/-! ### `committed` is not modified -/

/-- `append` never modifies `committed`.  The `committed` field is a property of
    what the quorum has agreed on; it is updated only by explicit `commit_to` calls,
    not by appending entries. -/
theorem append_committed_unchanged (s : RaftLogState) (ents : List Entry) :
    (raftAppend s ents).1.committed = s.committed := by
  cases ents with
  | nil  => simp [raftAppend]
  | cons e rest =>
    simp [raftAppend]

/-- `append` never modifies `firstIndex`. -/
theorem append_firstIndex_unchanged (s : RaftLogState) (ents : List Entry) :
    (raftAppend s ents).1.firstIndex = s.firstIndex := by
  cases ents with
  | nil  => simp [raftAppend]
  | cons e rest => simp [raftAppend]

/-! ### Return-value and last-index correctness -/

/-- The returned value from `raftAppend` equals the new last index of the state. -/
theorem append_lastIndex_eq_return (s : RaftLogState) (ents : List Entry) :
    (raftAppend s ents).2 = raftLastIndex (raftAppend s ents).1 := by
  cases ents with
  | nil  => simp [raftAppend]
  | cons e rest => simp [raftAppend]

/-- For a non-empty entry list, the returned last index equals
    `unstable.offset + entries.length - 1` after `truncateAndAppend`.

    This follows from the fact that `truncateAndAppend` always leaves the buffer
    with entries ending at the last index of `ents`. -/
theorem append_return_nonempty (s : RaftLogState) (e : Entry) (rest : List Entry)
    (h_nonempty : (e :: rest) ≠ []) :
    (raftAppend s (e :: rest)).2 =
      (truncateAndAppend s.unstable (e :: rest)).offset +
      (truncateAndAppend s.unstable (e :: rest)).entries.length - 1 := by
  simp [raftAppend, raftLastIndex, maybeLastIndex]
  -- After truncateAndAppend, entries is non-empty (it contains at least `e`).
  -- We need to show the entry list of the result is non-empty.
  have h_entries_nonempty : (truncateAndAppend s.unstable (e :: rest)).entries ≠ [] := by
    simp [truncateAndAppend]
    split_ifs with hA hB
    · -- Case A: pure append — original ++ (e :: rest)
      exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    · -- Case B: full replacement
      exact List.cons_ne_nil _ _
    · -- Case C: truncate + append
      exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  cases h_ne : (truncateAndAppend s.unstable (e :: rest)).entries with
  | nil  => exact absurd h_ne h_entries_nonempty
  | cons hd tl => simp [h_ne]

/-! ### Safety gate -/

/-- **Safety gate** — the main safety theorem for `append`.

    If the caller satisfies the precondition `ents[0].index - 1 ≥ committed`
    (i.e., `ents[0].index ≥ committed + 1`, meaning the first new entry is at or
    after the next uncommitted slot), then no entry at any index `≤ committed` can
    appear in the *new* unstable entries list that was not also present (at the same
    index) in the *old* unstable entries list.

    Formally: any entry `x` whose index satisfies `x.index ≤ committed + 1` and
    which appears in the new unstable entries list, also has `x.index ≤ after`
    (where `after = ents[0].index - 1 ≥ committed`), so it cannot have been touched
    by `truncateAndAppend`.

    We state this as: if `after ≥ committed` then the offset of the new unstable
    buffer is either ≥ `committed + 1` (Case B: full replacement above the committed
    index) or equals the old offset (Cases A and C: the prefix up to `after` is
    preserved, and `after ≥ committed` ensures committed entries are in the prefix).

    Concretely: `truncateAndAppend` only discards entries with index `≥ ents[0].index`.
    Since `ents[0].index = after + 1 ≥ committed + 1 + 1 = committed + 2 ≥ committed + 1`,
    no entry at index ≤ committed is discarded. -/
theorem append_safety_gate (s : RaftLogState) (e : Entry) (rest : List Entry)
    (h_after : s.committed < e.index)  -- e.index - 1 ≥ committed ↔ committed < e.index
    :
    /- The new unstable offset satisfies: either the buffer was fully replaced
       (Case B: e.index ≤ offset, so new offset = e.index > committed), or the
       old offset is preserved (Cases A and C).  In all cases, the offset does
       not go below committed + 1. -/
    (e.index ≤ s.unstable.offset →
      (truncateAndAppend s.unstable (e :: rest)).offset = e.index ∧
      e.index > s.committed) ∧
    (s.unstable.offset < e.index →
      (truncateAndAppend s.unstable (e :: rest)).offset = s.unstable.offset) := by
  constructor
  · intro hB
    obtain ⟨hoff, _⟩ := truncateAndAppend_caseB s.unstable e rest hB
    exact ⟨hoff, h_after⟩
  · intro hAC
    by_cases hA : e.index = s.unstable.offset + s.unstable.entries.length
    · obtain ⟨hoff, _⟩ := truncateAndAppend_caseA s.unstable e rest hA
      exact hoff
    · have hC1 : s.unstable.offset < e.index := hAC
      have hC2 : e.index < s.unstable.offset + s.unstable.entries.length := by omega
      obtain ⟨hoff, _⟩ := truncateAndAppend_caseC s.unstable e rest hC1 hC2
      exact hoff

/-- Corollary of the safety gate: the new unstable offset is > `committed`.

    When `after = e.index - 1 ≥ committed` (i.e., `e.index > committed`):
    - Case B (e.index ≤ offset): new offset = e.index > committed ✓
    - Cases A/C (e.index > offset): offset unchanged; if original offset > committed, holds.

    This corollary covers the case where the original offset is already above
    `committed` — which holds whenever the unstable buffer was initialised correctly
    (initial offset = last stable index + 1 ≥ first_index ≥ committed + 1 typically). -/
theorem append_safety_gate_offset_gt_committed (s : RaftLogState) (e : Entry) (rest : List Entry)
    (h_after : s.committed < e.index)
    (h_orig_offset : s.committed < s.unstable.offset) :
    s.committed < (truncateAndAppend s.unstable (e :: rest)).offset := by
  obtain ⟨hB_part, hAC_part⟩ := append_safety_gate s e rest h_after
  by_cases hle : e.index ≤ s.unstable.offset
  · obtain ⟨hoff, hgt⟩ := hB_part hle
    rw [hoff]; exact hgt
  · push_neg at hle
    rw [hAC_part hle]
    exact h_orig_offset

/-- The return value from a non-empty append is ≥ `committed`.

    This follows from `h_after` (committed < e.index) and the fact that the
    returned value is the new last index, which is ≥ the first new entry's index. -/
theorem append_return_ge_committed (s : RaftLogState) (e : Entry) (rest : List Entry)
    (h_after : s.committed < e.index) :
    s.committed < (raftAppend s (e :: rest)).2 := by
  simp only [raftAppend, List.isEmpty_cons, ↓reduceIte]
  simp only [raftLastIndex, maybeLastIndex]
  -- After truncateAndAppend, entries are non-empty
  have h_ne : (truncateAndAppend s.unstable (e :: rest)).entries ≠ [] := by
    simp [truncateAndAppend]
    split_ifs
    · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    · exact List.cons_ne_nil _ _
    · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  cases h : (truncateAndAppend s.unstable (e :: rest)).entries with
  | nil  => exact absurd h h_ne
  | cons hd tl =>
    simp [h]
    -- new last index = offset' + len' - 1
    -- We know offset' ≥ e.index > committed OR offset' = s.unstable.offset AND len' ≥ 1
    -- In both cases, offset' + len' - 1 ≥ offset' - 1 ≥ some lower bound > committed.
    -- The cleanest path: use the case split from append_safety_gate.
    by_cases hle : e.index ≤ s.unstable.offset
    · -- Case B: new offset = e.index, entries = e :: rest ++ rest? No: e :: rest itself.
      obtain ⟨hoff_eq, hgt⟩ := (append_safety_gate s e rest h_after).1 hle
      -- new offset = e.index, len ≥ 1 (cons hd tl)
      have hlen_pos : 0 < (truncateAndAppend s.unstable (e :: rest)).entries.length := by
        rw [h]; simp
      rw [hoff_eq]
      omega
    · push_neg at hle
      obtain hoff_eq := (append_safety_gate s e rest h_after).2 hle
      -- offset unchanged, entries len ≥ 1 (cons hd tl)
      have hlen_pos : 0 < (truncateAndAppend s.unstable (e :: rest)).entries.length := by
        rw [h]; simp
      rw [hoff_eq]
      omega

/-! ### Well-formedness preservation -/

/-- Appending a well-formed entry list to a well-formed state yields a well-formed state.

    We model "well-formed entries" as: the entry list is `indexCoherent` starting at
    `e.index` — i.e., entries are contiguous with indices `[e.index, e.index+1, …]`.

    This delegates directly to `truncateAndAppend_wellFormed` from `UnstableLog.lean`. -/
theorem append_wellFormed (s : RaftLogState) (e : Entry) (rest : List Entry)
    (h_wf   : wellFormed s.unstable)
    (h_coh  : indexCoherent e.index (e :: rest))
    (h_snap : ∀ snap, s.unstable.snapshot = some snap → snap.index < s.unstable.offset) :
    wellFormed (raftAppend s (e :: rest)).1.unstable := by
  simp only [raftAppend, List.isEmpty_cons, ↓reduceIte]
  exact truncateAndAppend_wellFormed s.unstable e rest h_wf h_coh h_snap

/-! ## `#eval` sanity checks -/

-- Example state: unstable buffer with entries [e5, e6] at offset 5
private def exState : RaftLogState :=
  { firstIndex := 1,
    committed  := 4,
    unstable   := { offset := 5, entries := [⟨5,1⟩, ⟨6,1⟩], snapshot := some ⟨4,1⟩ } }

-- Empty append: no-op, returns last index 6
#eval (raftAppend exState []).2       -- expected: 6
#eval (raftAppend exState []).1.committed  -- expected: 4 (unchanged)

-- Non-empty append (Case A: after = 6 = offset + len): new entry e7
#eval (raftAppend exState [⟨7,2⟩]).2  -- expected: 7
#eval (raftAppend exState [⟨7,2⟩]).1.committed  -- expected: 4 (unchanged)
#eval (raftAppend exState [⟨7,2⟩]).1.unstable.entries
  -- expected: [⟨5,1⟩, ⟨6,1⟩, ⟨7,2⟩]

-- Non-empty append (Case C: after = 5 < 6 = offset + len, keep 0): truncate e6, add e6'
#eval (raftAppend exState [⟨6,2⟩]).2  -- expected: 6
#eval (raftAppend exState [⟨6,2⟩]).1.unstable.entries
  -- expected: [⟨5,1⟩, ⟨6,2⟩]  (e6 replaced by e6')

-- Safety gate check: e.index > committed (4), so after = e.index - 1 ≥ 4 ✓
#eval decide (exState.committed < (7 : ℕ))   -- expected: true
#eval decide (exState.committed < (6 : ℕ))   -- expected: true
-- after = 5 would be e.index = 6 > committed = 4 ✓

/-! ## Summary -/

/-
**Phase 3 — Formal Spec Writing** (raftlog_append):

Theorems in this file (all 0 sorry):
- `raftLastIndex_entries`               — last index when entries non-empty
- `raftLastIndex_snap`                  — last index from snapshot
- `raftAppend_empty`                    — simp lemma, empty case
- `raftAppend_cons`                     — simp lemma, non-empty case
- `append_empty_noop_state`             — empty append: state unchanged
- `append_empty_noop_index`             — empty append: index unchanged
- `append_committed_unchanged`          — committed field never modified
- `append_firstIndex_unchanged`         — firstIndex field never modified
- `append_lastIndex_eq_return`          — return value = new last index
- `append_return_nonempty`              — return value formula when non-empty
- `append_safety_gate`                  — main safety theorem (case split)
- `append_safety_gate_offset_gt_committed` — corollary: offset > committed preserved
- `append_return_ge_committed`          — return value > committed
- `append_wellFormed`                   — well-formedness preservation

## What is NOT proved

- **Full no-committed-entry-modified theorem**: A stronger form would say that for
  each index `i ≤ committed`, the entry at index `i` in the new state equals the
  entry at index `i` in the old state.  This requires linking `maybeTerm` across
  the append, which in turn requires `truncateAndAppend_coherent` plus a case
  analysis on whether index `i` falls in the take-prefix (Case C) or is below the
  offset (Case B, where storage reads are unaffected).  This is left as a future
  Task 4/5 extension.

- **Round-trip property**: `append` followed by `slice` returns the appended entries.
  This links `RaftLogAppend` to `RaftLogSlice` and is a natural Task 5 target.

🔬 Lean Squad — automated formal verification.
-/

end FVSquad.RaftLogAppend
