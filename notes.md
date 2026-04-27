# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 127 — 2026-04-27 18:22 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.28.0, lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 79 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~711 (0 sorry)
- **CI**: `.github/workflows/lean-ci.yml`

## Status Issue
- Issue #139 — `[Lean Squad] Formal Verification Status` (open)

## Critical Gap Status (Run 127 Assessment)
- **4/5 hypotheses FULLY discharged** from concrete protocol definitions
- **1 hypothesis (hqc_preserved) CONDITIONALLY discharged** — needs A7
- **A7 (ElectionLifecycle bridge)**: ~20-40 theorems, estimated 2-4 runs
  - All prerequisites exist: RE5, ABI8, EBC6, CPS13, BL1-BL3
  - Needs: ElectionEpoch structure, prevLogIndex=0 proof, leader-log axiom
  - Phase advanced from 1 to 3 (research → formal spec writing)
- **After A7**: fully unconditional machine-checked Raft cluster safety proof

## Completed Targets (Phase 5, all proved, 0 sorry)
limit_size, config_validate, vote_result, committed_index, find_conflict, find_conflict_by_term,
maybe_append, joint_vote_result, joint_committed_index, inflights, progress, is_up_to_date,
log_unstable, tally_votes, has_quorum, quorum_recently_active, safety_composition, joint_tally,
joint_safety_composition, raft_protocol, raft_trace, progress_tracker, configuration_invariants,
multistep_reachability, election_model, AEBroadcastInvariant, BroadcastLifecycle,
ElectionBroadcastChain, ConcreteProtocolStep, ElectionConcreteModel, CommitRule, HasNextEntries,
NextEntries, MaybeCommit, MaybePersist, MaybePersistFUI, RaftLogAppend, ReadOnly, UncommittedState,
UnstablePersistBridge, LeaderCompleteness, ProgressTracker, progress_set, MemStorage,
IsContinuousEnts

## Run History (recent)
- Run 125: MemStorage MS9-14, MemStorageCorrespondence.lean (18 #guard)
- Run 126: IsContinuousEnts (ICE1-ICE8) + MemStorage Rust correspondence tests
- Run 127: Composition assessment — updated REPORT.md and TARGETS.md with Critical Gap analysis

## Next Steps (Priority Order)
1. **A7 (ElectionLifecycle)**: THE priority — define ElectionEpoch, prove broadcast preconditions
2. Task 7: Update CRITIQUE.md with Runs 122-127
3. Task 10/11: Update REPORT.md theorem counts and paper.tex
4. Task 6: Update CORRESPONDENCE.md with MemStorage section
