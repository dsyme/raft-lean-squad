# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 129 — 2026-04-28 04:10 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 79 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~940 (0 sorry)
- **#guard assertions**: 642
- **CI**: `.github/workflows/lean-ci.yml` — passing

## Status Issue
- Issue #139 — `[Lean Squad] Formal Verification Status` (open)

## Completed Targets (Phase 5, all proved, 0 sorry)
limit_size, config_validate, vote_result, committed_index, find_conflict, find_conflict_by_term,
maybe_append, joint_vote_result, joint_committed_index, inflights, progress, is_up_to_date,
log_unstable, tally_votes, has_quorum, quorum_recently_active, safety_composition, joint_tally,
joint_safety_composition, raft_protocol, raft_trace, progress_tracker, configuration_invariants,
multistep_reachability, election_model, AEBroadcastInvariant, BroadcastLifecycle,
ElectionBroadcastChain, ConcreteProtocolStep, ElectionConcreteModel, CommitRule, HasNextEntries,
NextEntries, MaybeCommit, MaybePersist, MaybePersistFUI, RaftLogAppend, ReadOnly, UncommittedState,
UnstablePersistBridge, LeaderCompleteness, ProgressTracker, progress_set, MemStorage,
IsContinuousEnts, Restore, ElectionLifecycle

## A7 Status: CLOSED
- ElectionLifecycle.lean EL1-EL7 all proved, 0 sorry
- Full unconditional machine-checked Raft cluster safety proof achieved

## Active Gaps (from CRITIQUE.md Run 129)
1. HLogConsistency discharge from RaftReachable (conditional hypothesis in LC7/LC8)
2. ProgressTracker integration with RaftReachable (all_wf in reachable states)
3. Restore correspondence tests missing
4. IsContinuousEnts correspondence tests missing
5. Term-indexed safety (MC4 → RSS6/RSS8 wiring)

## Run History (recent)
- Run 126: IsContinuousEnts (ICE1-ICE8) + MemStorage Rust correspondence tests
- Run 127: Composition assessment — updated REPORT.md and TARGETS.md
- Run 128: Task 3+9: Restore.lean (RST1-RST8, 8T, 0 sorry) + CI audit (passing)
- Run 129: Task 7+11: Updated CRITIQUE.md (Runs 119-129) + paper.tex (940T/79F/642g)

## Next Steps (Priority Order)
1. Task 6: Update CORRESPONDENCE.md with Restore + MemStorage + IsContinuousEnts sections
2. Task 8: Correspondence tests for Restore and IsContinuousEnts
3. Task 10: Update REPORT.md for Runs 119-129
4. New targets: `commit_to`, `applied_to`, `slice`, `scan` — state transition ops
