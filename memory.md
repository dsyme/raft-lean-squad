# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 126 — 2026-04-27 17:50 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.28.0, lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 79 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~711 (0 sorry)
- **CI**: `.github/workflows/lean-ci.yml`

## Status Issue
- Issue #139 — `[Lean Squad] Formal Verification Status` (open)

## Completed Targets (Phase 5, all proved, 0 sorry)
limit_size, config_validate, vote_result, committed_index, find_conflict, find_conflict_by_term,
maybe_append, joint_vote_result, joint_committed_index, inflights, progress, is_up_to_date,
log_unstable, tally_votes, has_quorum, quorum_recently_active, safety_composition, joint_tally,
joint_safety_composition, raft_protocol, raft_trace, progress_tracker, configuration_invariants,
multistep_reachability, election_model (RaftElection.lean), AEBroadcastInvariant, BroadcastLifecycle,
ElectionBroadcastChain, ConcreteProtocolStep, ElectionConcreteModel, CommitRule, HasNextEntries,
NextEntries, MaybeCommit, MaybePersist, MaybePersistFUI, RaftLogAppend, ReadOnly, UncommittedState,
UnstablePersistBridge, LeaderCompleteness (partial), ProgressTracker (PT1-PT26),
progress_set (PS1-PS8), MemStorage (MS1-MS14),
**is_continuous_ents (ICE1-ICE8, Run 126)** — IsContinuousEnts.lean (8T, 0 sorry)

## Correspondence Tests
- MemStorageCorrespondence.lean: 18 #guard (Lean side)
- tests/mem_storage/: 15 Rust assertions in test_mem_storage_correspondence (Run 126)
  - **Known divergence**: compact-entire-log case excluded — Rust does not update
    snapshot_metadata.index when draining all entries; Lean model tracks snapshotIndex
    consistently. Only affects edge case where compactIndex = lastIndex+1.

## Active Gaps (from CRITIQUE.md Run 119 + updates)
1. **HLogConsistency full discharge**: connect AEBroadcastInvariant to RaftReachable
2. **ProgressTracker integration**: all_wf in RaftReachable state
3. **Term-indexed safety**: MC4 → RSS6/RSS8
4. **Paper/Report**: needs update for Runs 122-126
5. **CORRESPONDENCE.md**: needs MemStorage section (compact divergence documented)

## Key Files
- `formal-verification/TARGETS.md` — prioritised target list
- `formal-verification/CORRESPONDENCE.md` — correspondence map
- `formal-verification/CRITIQUE.md` — proof utility critique
- `formal-verification/REPORT.md` — project report
- `formal-verification/paper/paper.tex` — conference paper
- `formal-verification/lean/FVSquad/IsContinuousEnts.lean` — ICE1-ICE8 (Run 126)
- `formal-verification/tests/mem_storage/` — MemStorage correspondence harness (Run 126)

## Run History (recent)
- Run 125: Task 3+5: MemStorage MS9-14, MemStorageCorrespondence.lean (18 #guard)
- Run 126: Task 3+8: IsContinuousEnts.lean (ICE1-ICE8) + MemStorage Rust correspondence tests
