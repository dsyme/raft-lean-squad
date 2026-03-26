import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# RestoreNode — Lean 4 Specification, Implementation, and Proofs

Models `Raft::restore` in `src/raft.rs` (lines ≈ 2618–2719):
the snapshot restore entry-point that reinstalls cluster state from a Raft snapshot.

## Relevant Rust code (condensed)

```rust
pub fn restore(&mut self, snap: Snapshot) -> bool {
    // Path A: stale snapshot
    if snap.get_metadata().index < self.raft_log.committed { return false; }
    // Path B: non-follower defense
    if self.state != StateRole::Follower {
        self.become_follower(self.term + 1, INVALID_INDEX);
        return false;
    }
    // Path C: node not in config
    let cs = meta.get_conf_state();
    if cs.voters().chain(learners()).chain(voters_outgoing()).all(|id| id != self.id) {
        return false;
    }
    // Path D: fast-forward (snapshot already present in log)
    if self.pending_request_snapshot == INVALID_INDEX
        && self.raft_log.match_term(meta.index, meta.term)
    {
        self.raft_log.commit_to(meta.index);
        return false;
    }
    // Path E: full restore
    self.raft_log.restore(snap);
    confchange::restore(&mut self.prs, last_index, cs)?;
    self.post_conf_change();   // updates self.promotable
    let pr = self.prs.get_mut(self.id).unwrap();
    pr.maybe_update(pr.next_idx - 1);
    self.pending_request_snapshot = INVALID_INDEX;
    true
}
```

## Model scope and approximations

* **Indices and terms**: `Nat` (Rust `u64`; no overflow modelling).
* **`StateRole`**: full four-case enum (Follower / Candidate / Leader / PreCandidate).
* **`RaftState`** is reduced to the fields relevant to `restore`:
  `id`, `state`, `term`, `committed`, `pendingReqSnap`, `selfMatchedIdx`,
  `termAtIdx` (log term function), `isInConfig`, `isMatch`.
* **`raft_log.restore`**: modelled as advancing `committed` to `snap.index` and
  setting `lastIndex = snap.index` (the full model is in `RaftLogRestore.lean`).
* **`confchange::restore`**: modelled as a Boolean success flag; we assume it
  succeeds (the Rust code fatals on failure, which we treat as out-of-scope).
* **`post_conf_change`**: modelled by updating `promotable` based on `isInConfig`.
* **`maybe_update(next_idx - 1)`**: modelled as setting `selfMatchedIdx = snap.index`.
* **`become_follower(term+1, INVALID_ID)`**: modelled as incrementing `term` and
  setting `state = Follower`.
* **I/O, logging, error paths, `Inflights`**: omitted.
* **Config membership check**: abstracted as a Boolean `isInConfig` field on the snapshot.

🔬 *Lean Squad — auto-generated formal specification, implementation model, and proofs.*
-/

namespace FVSquad.RestoreNode

/-! ## Types -/

abbrev NodeId := Nat
abbrev Term   := Nat
abbrev Index  := Nat

/-- `INVALID_INDEX = 0`: sentinel for "no pending request". -/
def INVALID_INDEX : Index := 0

/-- Role states a Raft node can be in. -/
inductive StateRole where
  | Follower
  | Candidate
  | Leader
  | PreCandidate
  deriving Repr, DecidableEq

/-- A snapshot is abstracted by its index, term, and two derived properties
    relevant to `restore`'s control flow. -/
structure SnapMeta where
  /-- `snap.get_metadata().index` -/
  index        : Index
  /-- `snap.get_metadata().term` -/
  term         : Term
  /-- Whether `self.id` appears in `cs.voters ∪ cs.learners ∪ cs.voters_outgoing`.
      Abstraction of the membership check in Path C. -/
  selfInConfig : Bool

/-- The portion of Raft node state relevant to `restore`. -/
structure RaftState where
  /-- `self.id` -/
  id               : NodeId
  /-- `self.state` -/
  state            : StateRole
  /-- `self.term` -/
  term             : Term
  /-- `self.raft_log.committed` -/
  committed        : Index
  /-- `self.pending_request_snapshot` (0 = INVALID_INDEX = none pending) -/
  pendingReqSnap   : Index
  /-- `self.raft_log.match_term(index, term)`: True when the log at `index` has `term`.
      Abstracted as a field for a specific `(index, term)` pair in `restore`. -/
  matchesTerm      : Bool
  /-- `self.raft_log.last_index()` after a full restore = snap.index. -/
  lastIndex        : Index
  /-- `self.promotable`: updated in `post_conf_change` -/
  promotable       : Bool
  /-- `pr.next_idx` for self's progress entry after `confchange::restore`.
      In the full restore path, `confchange::restore` sets next_idx = last_index + 1,
      so `maybe_update(next_idx - 1)` sets `matched = last_index`. -/
  selfMatchedIdx   : Index

/-! ## Implementation model -/

/-- The four possible outcomes of `restore`. -/
inductive RestoreResult where
  | StaleSnapshot   -- Path A: snap.index < committed, no change
  | NonFollower     -- Path B: node is not a follower; demoted + term incremented
  | NotInConfig     -- Path C: node not in snapshot's config
  | FastForward     -- Path D: snap already in log; commit advanced
  | FullRestore     -- Path E: full snapshot restore
  deriving Repr, DecidableEq

/-- `restoreClassify s snap`: classify which path `restore` will take. -/
def restoreClassify (s : RaftState) (snap : SnapMeta) : RestoreResult :=
  if snap.index < s.committed then
    RestoreResult.StaleSnapshot
  else if s.state ≠ StateRole.Follower then
    RestoreResult.NonFollower
  else if !snap.selfInConfig then
    RestoreResult.NotInConfig
  else if s.pendingReqSnap == INVALID_INDEX && s.matchesTerm then
    RestoreResult.FastForward
  else
    RestoreResult.FullRestore

/-- `restore s snap`: functional model of `Raft::restore`.
    Returns `(s', returned)` where `s'` is the new state and `returned : Bool`
    mirrors the Rust `return false` / `return true`. -/
def restore (s : RaftState) (snap : SnapMeta) : RaftState × Bool :=
  match restoreClassify s snap with
  | RestoreResult.StaleSnapshot =>
    -- Path A: no state mutation, return false
    (s, false)
  | RestoreResult.NonFollower =>
    -- Path B: become_follower(term+1, INVALID_ID), return false
    ({ s with state := StateRole.Follower, term := s.term + 1 }, false)
  | RestoreResult.NotInConfig =>
    -- Path C: no state mutation, return false
    (s, false)
  | RestoreResult.FastForward =>
    -- Path D: commit_to(snap.index), return false
    ({ s with committed := snap.index }, false)
  | RestoreResult.FullRestore =>
    -- Path E: full restore — log, config, progress, pendingReqSnap
    ({ s with
        committed      := snap.index
        lastIndex      := snap.index   -- raft_log.restore sets last_index = snap.index
        promotable     := snap.selfInConfig  -- post_conf_change updates this
        selfMatchedIdx := snap.index   -- maybe_update(next_idx-1) with next_idx = snap.index+1
        pendingReqSnap := INVALID_INDEX }, true)

/-! ## Key Properties -/

-- ---------------------------------------------------------------------------
-- Path A: stale snapshot
-- ---------------------------------------------------------------------------

/-- **P1**: On a stale snapshot, the state is unchanged. -/
theorem stale_no_change (s : RaftState) (snap : SnapMeta)
    (hA : snap.index < s.committed) :
    (restore s snap).1 = s := by
  simp [restore, restoreClassify, INVALID_INDEX, hA]

/-- **P2**: A stale snapshot returns `false`. -/
theorem stale_returns_false (s : RaftState) (snap : SnapMeta)
    (hA : snap.index < s.committed) :
    (restore s snap).2 = false := by
  simp [restore, restoreClassify, hA]

-- ---------------------------------------------------------------------------
-- Path B: non-follower defense
-- ---------------------------------------------------------------------------

/-- **P3**: On path B, the node becomes a Follower. -/
theorem nonfollower_becomes_follower (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state ≠ StateRole.Follower) :
    (restore s snap).1.state = StateRole.Follower := by
  simp [restore, restoreClassify, hA, hB]

/-- **P4**: On path B, the term is incremented by 1. -/
theorem nonfollower_term_incremented (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state ≠ StateRole.Follower) :
    (restore s snap).1.term = s.term + 1 := by
  simp [restore, restoreClassify, hA, hB]

/-- **P5**: Path B returns `false`. -/
theorem nonfollower_returns_false (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state ≠ StateRole.Follower) :
    (restore s snap).2 = false := by
  simp [restore, restoreClassify, hA, hB]

-- ---------------------------------------------------------------------------
-- Path C: not in config
-- ---------------------------------------------------------------------------

/-- **P6**: When the node is not in the snapshot config, the state is unchanged. -/
theorem notInConfig_no_change (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state = StateRole.Follower)
    (hC : snap.selfInConfig = false) :
    (restore s snap).1 = s := by
  simp [restore, restoreClassify, hA, hB, hC]

/-- **P7**: Path C returns `false`. -/
theorem notInConfig_returns_false (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state = StateRole.Follower)
    (hC : snap.selfInConfig = false) :
    (restore s snap).2 = false := by
  simp [restore, restoreClassify, hA, hB, hC]

-- ---------------------------------------------------------------------------
-- Path D: fast-forward
-- ---------------------------------------------------------------------------

/-- **P8**: On fast-forward, committed advances to `snap.index`. -/
theorem fastforward_commits (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state = StateRole.Follower)
    (hC : snap.selfInConfig = true)
    (hD1 : s.pendingReqSnap = INVALID_INDEX)
    (hD2 : s.matchesTerm = true) :
    (restore s snap).1.committed = snap.index := by
  simp [restore, restoreClassify, hA, hB, hC, hD1, hD2, INVALID_INDEX]

/-- **P9**: Fast-forward returns `false` (no full structural log change needed). -/
theorem fastforward_returns_false (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state = StateRole.Follower)
    (hC : snap.selfInConfig = true)
    (hD1 : s.pendingReqSnap = INVALID_INDEX)
    (hD2 : s.matchesTerm = true) :
    (restore s snap).2 = false := by
  simp [restore, restoreClassify, hA, hB, hC, hD1, hD2, INVALID_INDEX]

/-- **P10**: Fast-forward commit is monotone (committed doesn't decrease). -/
theorem fastforward_commit_monotone (s : RaftState) (snap : SnapMeta)
    (hA : ¬ (snap.index < s.committed))
    (hB : s.state = StateRole.Follower)
    (hC : snap.selfInConfig = true)
    (hD1 : s.pendingReqSnap = INVALID_INDEX)
    (hD2 : s.matchesTerm = true) :
    (restore s snap).1.committed ≥ s.committed := by
  simp [restore, restoreClassify, hA, hB, hC, hD1, hD2, INVALID_INDEX]
  omega

-- ---------------------------------------------------------------------------
-- Path E: full restore
-- ---------------------------------------------------------------------------

/-- Conditions that select Path E. -/
def isFullRestorePath (s : RaftState) (snap : SnapMeta) : Prop :=
  ¬ (snap.index < s.committed) ∧
  s.state = StateRole.Follower ∧
  snap.selfInConfig = true ∧
  ¬ (s.pendingReqSnap = INVALID_INDEX ∧ s.matchesTerm = true)

/-- **P11**: Full restore returns `true`. -/
theorem fullRestore_returns_true (s : RaftState) (snap : SnapMeta)
    (h : isFullRestorePath s snap) :
    (restore s snap).2 = true := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  simp [restore, restoreClassify, hA, hB, hC, INVALID_INDEX]
  push_neg at hD
  rcases hD with hD1 | hD2
  · simp [hD1]
  · simp [hD2]

/-- **P12**: After full restore, `committed` equals `snap.index`. -/
theorem fullRestore_committed (s : RaftState) (snap : SnapMeta)
    (h : isFullRestorePath s snap) :
    (restore s snap).1.committed = snap.index := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  push_neg at hD
  simp [restore, restoreClassify, hA, hB, hC, INVALID_INDEX]
  rcases hD with hD1 | hD2
  · simp [hD1]
  · simp [hD2]

/-- **P13**: After full restore, `lastIndex` equals `snap.index`. -/
theorem fullRestore_lastIndex (s : RaftState) (snap : SnapMeta)
    (h : isFullRestorePath s snap) :
    (restore s snap).1.lastIndex = snap.index := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  push_neg at hD
  simp [restore, restoreClassify, hA, hB, hC, INVALID_INDEX]
  rcases hD with hD1 | hD2
  · simp [hD1]
  · simp [hD2]

/-- **P14**: After full restore, `pendingReqSnap` is `INVALID_INDEX`. -/
theorem fullRestore_pendingReqSnap_cleared (s : RaftState) (snap : SnapMeta)
    (h : isFullRestorePath s snap) :
    (restore s snap).1.pendingReqSnap = INVALID_INDEX := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  push_neg at hD
  simp [restore, restoreClassify, hA, hB, hC, INVALID_INDEX]
  rcases hD with hD1 | hD2
  · simp [hD1]
  · simp [hD2]

/-- **P15**: After full restore, `selfMatchedIdx` equals `snap.index`
    (from `maybe_update(next_idx - 1)` with `next_idx = snap.index + 1`). -/
theorem fullRestore_selfMatched (s : RaftState) (snap : SnapMeta)
    (h : isFullRestorePath s snap) :
    (restore s snap).1.selfMatchedIdx = snap.index := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  push_neg at hD
  simp [restore, restoreClassify, hA, hB, hC, INVALID_INDEX]
  rcases hD with hD1 | hD2
  · simp [hD1]
  · simp [hD2]

/-- **P16**: Committed index never decreases under `restore`, on any path. -/
theorem committed_monotone (s : RaftState) (snap : SnapMeta) :
    (restore s snap).1.committed ≥ s.committed := by
  simp only [restore, restoreClassify, INVALID_INDEX]
  split_ifs with hA hB hC hD
  · -- Path A
    simp
  · -- Path B
    simp
  · -- Path C
    simp
  · -- Path D
    simp; omega
  · -- Path E
    simp; omega

/-- **P17**: If the node is already a Follower, `restore` never increases its term
    (Paths C, D, E all require `state = Follower` to reach, and none bump the term). -/
theorem follower_term_unchanged (s : RaftState) (snap : SnapMeta)
    (hFollower : s.state = StateRole.Follower) :
    (restore s snap).1.term = s.term := by
  simp only [restore, restoreClassify, INVALID_INDEX]
  split_ifs with hA hB hC hD
  · simp
  · -- Path B can't happen since state = Follower
    exfalso; exact hB (by rw [hFollower])
  · simp
  · simp
  · simp

/-- **P18**: Full restore preserves the `state` field as `Follower`.
    (Path E doesn't modify `state`.) -/
theorem fullRestore_state_follower (s : RaftState) (snap : SnapMeta)
    (h : isFullRestorePath s snap) :
    (restore s snap).1.state = StateRole.Follower := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  push_neg at hD
  simp [restore, restoreClassify, hA, hB, hC, INVALID_INDEX]
  rcases hD with hD1 | hD2
  · simp [hD1, hB]
  · simp [hD2, hB]

/-- **P19**: `restore` returns `true` if and only if it took the full-restore path. -/
theorem returns_true_iff_fullRestore (s : RaftState) (snap : SnapMeta) :
    (restore s snap).2 = true ↔ restoreClassify s snap = RestoreResult.FullRestore := by
  simp only [restore, restoreClassify, INVALID_INDEX]
  split_ifs <;> simp_all

/-- **P20**: The node's `id` field is never modified by `restore`. -/
theorem id_unchanged (s : RaftState) (snap : SnapMeta) :
    (restore s snap).1.id = s.id := by
  simp only [restore, restoreClassify, INVALID_INDEX]
  split_ifs <;> simp

/-! ## Concrete examples (sanity checks) -/

-- Example 1: Stale snapshot (Path A)
#eval
  let s : RaftState := { id := 1, state := .Follower, term := 5, committed := 100,
      pendingReqSnap := 0, matchesTerm := false, lastIndex := 100,
      promotable := true, selfMatchedIdx := 99 }
  let snap : SnapMeta := { index := 99, term := 4, selfInConfig := true }
  restore s snap
  -- Expected: (s unchanged, false)

-- Example 2: Non-follower (Path B)
#eval
  let s : RaftState := { id := 1, state := .Leader, term := 5, committed := 100,
      pendingReqSnap := 0, matchesTerm := false, lastIndex := 105,
      promotable := true, selfMatchedIdx := 104 }
  let snap : SnapMeta := { index := 200, term := 6, selfInConfig := true }
  restore s snap
  -- Expected: (state=Follower, term=6, rest unchanged), false

-- Example 3: Fast-forward (Path D)
#eval
  let s : RaftState := { id := 1, state := .Follower, term := 5, committed := 100,
      pendingReqSnap := 0, matchesTerm := true, lastIndex := 200,
      promotable := true, selfMatchedIdx := 199 }
  let snap : SnapMeta := { index := 200, term := 5, selfInConfig := true }
  restore s snap
  -- Expected: (committed=200, rest unchanged), false

-- Example 4: Full restore (Path E)
#eval
  let s : RaftState := { id := 1, state := .Follower, term := 5, committed := 100,
      pendingReqSnap := 0, matchesTerm := false, lastIndex := 105,
      promotable := true, selfMatchedIdx := 104 }
  let snap : SnapMeta := { index := 200, term := 5, selfInConfig := true }
  restore s snap
  -- Expected: (committed=200, lastIndex=200, pendingReqSnap=0, selfMatchedIdx=200,
  --            promotable=true, state=Follower, term=5), true

-- Example 5: Full restore with pending request snapshot (Path E, not D)
-- When pendingReqSnap != INVALID_INDEX, fast-forward is bypassed even if term matches
#eval
  let s : RaftState := { id := 1, state := .Follower, term := 5, committed := 100,
      pendingReqSnap := 150, matchesTerm := true, lastIndex := 200,
      promotable := true, selfMatchedIdx := 199 }
  let snap : SnapMeta := { index := 200, term := 5, selfInConfig := true }
  restore s snap
  -- Expected: full restore, pendingReqSnap cleared, return true

-- Verify P16 (monotone) on all examples
example : (restore
    { id := 1, state := .Follower, term := 5, committed := 100,
      pendingReqSnap := 0, matchesTerm := false, lastIndex := 100,
      promotable := true, selfMatchedIdx := 99 }
    { index := 99, term := 4, selfInConfig := true }).1.committed ≥ 100 := by native_decide

example : (restore
    { id := 1, state := .Follower, term := 5, committed := 100,
      pendingReqSnap := 0, matchesTerm := false, lastIndex := 105,
      promotable := true, selfMatchedIdx := 104 }
    { index := 200, term := 5, selfInConfig := true }).1.committed ≥ 100 := by native_decide

end FVSquad.RestoreNode
