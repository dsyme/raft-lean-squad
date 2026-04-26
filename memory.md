# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 115 — 2026-04-26 04:00 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.28.0, lakefile.toml with Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: ~72 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~673 (0 sorry across most files; some sorry in advanced protocol files)
- **CI**: `.github/workflows/lean-ci.yml` — builds Lean + runs Rust correspondence tests

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
UnstablePersistBridge, LeaderCompleteness (partial), ProgressTracker (PT1-PT26)

## Correspondence Tests (26 total Rust tests)
All correspondence targets in `formal-verification/tests/` have Rust tests.
- **Run 115 NEW**: `progress` — 55 Rust assertions for Progress state machine
  (`test_progress_correspondence` in `src/tracker/progress.rs`)
  Fixtures: pReplicate(5,6), pProbe(3,7), pSnapshot(2,3,snap=10)
  Groups: maybeUpdate, maybeDecrTo×3, optimisticUpdate, transitions, isPaused
  Result: 55 pass, no mismatches
- **Note**: ins_size=256 needed for pReplicate (ins_size=0 makes full()=true)

## CI Status (Run 115 audit)
- `lean-ci.yml`: healthy. Threshold updated 20→26 correspondence tests.
- lean-toolchain: v4.28.0 ✅, lake-manifest.json ✅, globs ✅

## Active Gaps (from CRITIQUE.md Run 105)
1. **LeaderCompleteness full chain**: `HLogConsistency` still hypothetical; highest priority
2. **Term-indexed safety**: connecting MaybeCommit MC4 to top-level proof
3. **ProgressTracker integration**: PT1-PT26 per-op but no RaftReachable connection
4. **Paper**: last updated Run 108 (647T/66F/524g/12-layer)

## Key Files
- `formal-verification/TARGETS.md` — prioritised target list
- `formal-verification/CORRESPONDENCE.md` — correspondence map (updated Run 115)
- `formal-verification/CRITIQUE.md` — proof utility critique (Run 110)
- `formal-verification/REPORT.md` — project report
- `formal-verification/paper/paper.tex` — conference paper (Run 108)

## Notes
- PR workflow: all Lean Squad PRs labeled `lean-squad`; merge open PRs at start of each run
- Status issue #139 updated each run with run history entry
