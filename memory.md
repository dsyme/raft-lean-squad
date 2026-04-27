# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 128 — 2026-04-27 20:13 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.28.0, lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 81 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~718 (0 sorry)
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
IsContinuousEnts, **Restore (RST1-RST8, Run 128)**

## A7 Status: CLOSED
- ElectionLifecycle.lean EL1-EL7 all proved, 0 sorry
- Full unconditional machine-checked Raft cluster safety proof achieved

## Active Gaps (from CRITIQUE.md)
1. Paper/Report: needs update for recent runs
2. CORRESPONDENCE.md: needs Restore section
3. CRITIQUE.md: needs update for Runs 122-128

## Run History (recent)
- Run 126: IsContinuousEnts (ICE1-ICE8) + MemStorage Rust correspondence tests
- Run 127: Composition assessment — updated REPORT.md and TARGETS.md
- Run 128: Task 3+9: Restore.lean (RST1-RST8, 8T, 0 sorry) + CI audit (passing)

## Next Steps (Priority Order)
1. Task 7: Update CRITIQUE.md with Runs 122-128
2. Task 10/11: Update REPORT.md and paper.tex
3. Task 6: Update CORRESPONDENCE.md with Restore + MemStorage sections
4. New targets: `commit_to`, `applied_to`, `slice`, `scan` — state transition ops
