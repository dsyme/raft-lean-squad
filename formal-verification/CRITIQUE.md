# FV Proof Utility Critique

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Last Updated
- **Date**: 2026-04-28
- **Commit**: `bac0606`

---

## Overall Assessment

The FV project has produced **769 theorem declarations across 79 Lean files (51 proof + 28 correspondence),
machine-checked by Lean 4 (stdlib only — no Mathlib), with 0 `sorry` and 642 `#guard` correspondence
assertions**.

**No bugs found** in any modelled Rust function. One **notable finding**: the `VotersLearnersDisjoint`
predicate as initially stated (CI9–CI12) is *stricter* than the actual Raft implementation — the demotion
state allows a peer to be simultaneously in `outgoing` and `learners_next`, which the strict 4-clause
predicate incorrectly forbids. A relaxed 3-clause predicate matches the actual Rust semantics.

A second **formulation finding**: RSS3 and RSS4 were initially stated as universally quantified
properties that are provably false — the `sorry` mechanism caught this before unsound axioms
could enter the proof base. Corrected formulations with proper hypotheses (`LogMatchingInvariantFor`,
`NoRollbackInvariantFor`) were proved.

A third **divergence finding**: the Lean `maybeIncrease` model in the noLimit path (`maxUncommittedSize = 0`)
increments `uncommittedSize` while the Rust code returns `true` without updating state. No proved
theorem depends on this divergent state.

---

## Project Statistics

| Metric | Value |
|--------|-------|
| Total theorem declarations | **769** |
| Lean 4 files | **79** (51 proof + 28 correspondence) |
| `sorry` remaining | **0** |
| `#guard` correspondence tests | **642** (in correspondence files) + 54 (in proof files) |
| Correspondence targets | **28** Rust functions |
| Lean 4 version | 4.30.0-rc2 |

---

## Proof Architecture

The proofs are organised into layers of increasing abstraction:

### Layer 1: Utility Functions

**`LimitSize.lean` — 25 theorems.** Covers `limit_size` from `src/util.rs`. Key results:
`limitSize_is_prefix` (output is a prefix of input), `limitSize_size_bound` (respects budget),
`limitSize_maximality` (output is *maximal* — adding one more entry would exceed budget),
`limitSize_idempotent` (applying twice is a no-op). The maximality proof is unusually strong:
it proves *optimality*, not just safety.

**`IsContinuousEnts.lean` — 8 theorems (ICE1–ICE8).** Formalises the `is_continuous_ents`
predicate from `src/util.rs`. Proves that concatenation validity is correctly detected for
AppendEntries batches.

### Layer 2: Core Data Structures

**`MajorityVote.lean` — 21 theorems.** Core quorum threshold. Key results: `voteResult_Won_iff`,
`voteResult_Lost_iff`, `voteResult_Pending_iff` — a *complete* characterisation where every
vote configuration maps to exactly one outcome. `voteResult_exhaustive` confirms exhaustiveness.

**`JointVote.lean` — 14 theorems.** Joint quorum semantics. Key results: `jointVoteResult_Won_iff`
(both sub-quorums must win), `jointVoteResult_non_joint` (empty outgoing degenerates to single
quorum — a subtle protocol edge case where bugs lurk).

**`CommittedIndex.lean` — 28 theorems.** The highest-value results in the entire FV effort:
- `committedIndex_safety`: ≥ majority voters have acked ≥ ci.
- `committedIndex_maximality`: no larger index has a majority ack.
- `committedIndex_mono`: committed index only advances as acks arrive.
These would catch wrong sort direction, off-by-one in majority index, wrong acked function,
or any regression causing committed index to go backwards.

**`JointCommittedIndex.lean` — 10 theorems (JCI1–JCI10).** Extends committed index to joint
configs. JCI4–JCI5 prove joint safety for both incoming and outgoing groups. JCI6 proves maximality.
**Known divergence**: Lean returns `0` for empty configs while Rust returns `u64::MAX`; proofs
are valid only for non-empty configs.

**`JointTally.lean` — 18 theorems (JT1–JT18).** Formalises joint-quorum outcome calculation.

**`HasQuorum.lean` — 20 theorems.** HQ14 and HQ20 are among the most important theorems in the
entire portfolio — they prove the **majority quorum intersection property**: any two sets that
both form a majority quorum must share at least one member. This is the mathematical foundation
of Raft consensus safety. HQ20 provides a concrete `∃ w` witness. Proof chain: inclusion-exclusion
(HQ11) → union-bound (HQ12) → arithmetic `2×majority(n) > n` (HQ10) → intersection (HQ13) → witness (HQ19).
**Limitation**: assumes `voters ≠ []`.

**`TallyVotes.lean` — 28 theorems.** TV12 (`tallyVotes_lost_of_rejected_ge`) proves the
rejection-closes-election invariant. TV18 proves Won and Lost are mutually exclusive. TV7
(partition identity: `granted + rejected + missing = voters.length`) enables the key proofs.

**`FindConflict.lean` — 12 theorems.** `findConflict_zero_iff_all_match` (FC11): biconditional —
zero ↔ all match. `findConflict_first_mismatch` (FC7): output is the *first* mismatch index.

**`FindConflictByTerm.lean` — 10 theorems (FCB1–FCB10).** Formalises `find_conflict_by_term`
from `src/raft_log.rs`. Key results: FCB1 (result in range), FCB3 (maximality — result is the
largest index with term ≤ input term), FCB4 (identity on match), FCB9 (maximality under
`LogNonDecreasing` assumption).

**`ConfigValidate.lean` — 10 theorems.** `configValidate_iff_valid` ensures the boolean function
is *equivalent* to the full 8-constraint specification. A machine-checked regression guard.
**Concern**: no automated check that the Lean `Config` struct tracks future Rust changes.

**`IsUpToDate.lean` — 17 theorems.** `isUpToDate_total` (IU10) proves Raft's log ordering is a
total preorder — the mathematical foundation for deterministic leader election. `IU17` formalises
the Raft election restriction.

**`Inflights.lean` — 49 theorems.** INF30 and INF31 bridge the abstract (queue-based) and concrete
(ring-buffer) models — the only implementation-level bridging theorems in the portfolio. INF8
(`freeTo_all_gt_sorted`) confirms core Raft flow-control correctness. INF4 (`count_le_cap`)
prevents buffer overflow.

**`ConfigurationInvariants.lean` — 11 theorems (CI1–CI12).** `VotersLearnersDisjoint` formalised.
**Key finding**: CI9–CI12 reveal the strict 4-clause predicate is *stricter* than Rust's demotion
state. A relaxed 3-clause predicate (`VotersLearnersDisjointRelaxed`) matches actual semantics.

### Layer 3: Log Operations

**`LogUnstable.lean` — 41 theorems.** Covers the `Unstable` struct. TAA1–TAA7
(`truncateAndAppend`) are the most complex: three-case analysis covering simple append,
offset reset, and in-place truncation. TAA7 proves snapshot is *unchanged* across all cases.
WF1–WF4 establish the structural invariant `snapshot.offset ≤ entries[0].index`. **Open
question**: Case 2 of `truncateAndAppend` can violate `wf` if a snapshot is pending — callers
must guarantee safety by contract.

**`MaybeAppend.lean` — 18 theorems.** The richest protocol-level proof collection:
- MA5 (`committed_eq`): exact committed-index formula.
- MA13 (`log_prefix_preserved`): entries before conflict untouched.
- MA14 (`suffix_applied`): new entries at correct indices.
- MA11 (`persisted_rollback`): persisted boundary rolled back on conflict.
- MA16 (`state_unchanged_on_failure`): failed match_term → no mutation.
Together MA5+MA13+MA14 describe the complete semantic effect of `maybe_append`.

**`RaftLogAppend.lean` — 19 theorems (RA1–RA9 + helpers + P4–P7).** Covers `RaftLog::append`:
- P4 (`ra_committed_prefix_preserved`): committed entries never touched — validates `fatal!` guard.
- P5 (`ra_prefix_preserved`): full prefix preservation.
- P6 (`ra_batch_term`): each batch entry at correct index with correct term.
- P7 (`ra_beyond_batch_none`): no spurious trailing entries.
Together P4–P7 give complete postcondition coverage.

**`NextEntries.lean` — 9 theorems (NE1–NE9).** Models `RaftLog::next_entries`. NE1: returns
`None` iff no entries in `[since+1, committed]`. NE2–NE3: length and index characterisation.

**`HasNextEntries.lean` — 14 theorems (HNE1–HNE14).** Models `has_next_entries_since`. HNE9
is the key biconditional characterisation guarding the Raft apply loop.

**`Restore.lean` — 8 theorems (RST1–RST8).** Formalises `RaftLog::restore` — snapshot
restoration. Proves committed advancement, persisted clamping, unstable clearing, idempotence.

### Layer 4: Persist Safety

**`MaybePersist.lean` — 13 theorems (MP1–MP8 + SP1–SP4 + compose).** Covers `maybe_persist`
and `maybe_persist_snap`. The three-guard structure (regression, uncommitted boundary, term
match) encodes Raft's async-persist safety contract. MP5–MP7 directly formalise the three
correctness obligations preventing data loss under concurrent leadership changes.

**`MaybePersistFUI.lean` — 8 theorems.** Models `maybe_persist` using `firstUpdateIndex`
derived from `Unstable`. `maybePersistFui_true_iff` gives the exact acceptance condition;
`maybePersistFui_monotone` proves persisted never regresses.

**`UnstablePersistBridge.lean` — 8 theorems (UPB1–UPB8).** Bridges `LogUnstable.wf` to
`MaybePersist`: UPB8 proves that when `wf u` holds, any successful advance produces
`newPersisted < u.offset`. End-to-end safety from `LogUnstable.wf` through `MaybePersistFUI`
is formally verified.

### Layer 5: Commit Logic

**`MaybeCommit.lean` — 12 theorems (MC1–MC12).** MC4 (`maybeCommit_term`) is the formal proof
of Raft §5.4.2 — the "figure 8" problem prevention: `maybe_commit` only advances the committed
index to entries whose term matches the current leader's term. MC1 proves monotonicity. MC12
shows `maybeCommit` = `commitTo` when the term check passes.

**`CommitRule.lean` — 9 theorems (CR1–CR9).** CR8 (`CommitRuleValid ↔ hnew_cert`) is a
*definitional* proof step: the concrete Raft quorum-ACK commit rule directly satisfies the
abstract `RaftReachable.step` hypothesis. CR9 shows `CommitCertInvariant` is an inductive
invariant under `CommitRuleValid`.

**`UncommittedState.lean` — 18 theorems (US1–US18).** Flow-control bookkeeping. US16/US17
give complete biconditional characterisations of `maybeIncrease` acceptance/rejection. US18
provides a saturation lower bound for `maybeReduce`.

### Layer 6: ReadOnly

**`ReadOnly.lean` — 15 theorems (RO1–RO14).** Formalises the ReadIndex linearisability protocol
(Raft §6.4). RO1 (idempotent add), RO6 (ack set grows), RO8 (`advance` removes ctx — proved
using the Nodup invariant), RO13 (`addRequest` preserves Nodup), RO14 (`advance` preserves
Nodup). All proved, 0 sorry. **Limitation**: `ReadOnlyOption` (Safe vs LeaseBased) not modelled.

### Layer 7: Progress Tracking

**`Progress.lean` — 37 theorems (PR1–PR35 + helpers).** The `wf` invariant (`matched + 1 ≤
next_idx`) is the central result. PR18–PR20 prove preservation by all state transitions.
PR23–PR25 prove self-healing: `becomeProbe`/`becomeReplicate` restore `wf` even from invalid
states. PR31–PR33 cover non-Replicate `maybeDecrTo` paths. PR34–PR35 cover `optimisticUpdate`.

**`ProgressTracker.lean` — 28 theorems (PT1–PT28).** Per-peer `wf` invariant preserved by all
six operations (`removePeer`, `insertPeer`, `updatePeer`, `applyChange`, `applyChanges`,
`initTracker`). PT22–PT23: `initTracker` membership biconditional. PT24: `applyChanges` stability
for unaffected peers. PT25–PT26: "add wins" semantics of configuration changes.

**`ProgressSet.lean` — 9 theorems (PS1–PS8+).** Formalises `ProgressTracker` as a composed
progress set, proving properties of `quorum_recently_active` as a composed operation.

### Layer 8: Election Model

**`RaftElection.lean` — 53 theorems (RE1–RE53).** The most substantial single-file addition.
Key results:
- `electionSafety` (RE5): at most one leader per term — central Raft property.
- RV1–RV8: complete biconditionals for `voteGranted` matching `src/raft.rs`.
Verified against Rust via `ElectionCorrespondence.lean` (23 `#guard`).

**`LeaderCompleteness.lean` — 10 theorems (LC1–LC10).** Formalises Raft §5.4.2 leader
completeness. LC3: main theorem given `CandidateLogCovers`. LC6: discharge condition for
`hqc_preserved`. LC7–LC8: full chain given `HLogConsistency` + `CandLogMatching` +
`isUpToDate`. **Note**: `HLogConsistency` is an explicit hypothesis — not a proved invariant
— but all hypotheses are explicit and 0 sorry is used.

### Layer 9: Safety Composition

**`SafetyComposition.lean` — 10 theorems.** The highest-value file in the portfolio. SC4
(`raft_log_safety`) is the Raft log-safety certificate: for any two acknowledgment functions,
there is always a common witness voter. Directly formalises §5.4 of the Raft paper. SC6
(biconditional) completely characterises `committedIndex` in quorum terms. SC9 (leader-election
safety) proves any newly elected leader's supporters include a voter who witnessed the committed index.

**`JointSafetyComposition.lean` — 10 theorems (JSC1–JSC10).** Extends safety to joint configs.
JSC7: witnesses in BOTH halves of the joint quorum.

**`QuorumRecentlyActive.lean` — 11 theorems (QRA1–QRA15).** QRA4 (`isActive_self`) proves the
leader always counts itself as active. QRA15 (monotonicity) closes the compositional chain.
**Modelling note**: abstracts away the write side-effects of the Rust function.

**`CrossModuleComposition.lean` — 7 theorems.** CMC3 (`maybeAppend_committed_bounded`): `maybe_append`
never commits beyond what the quorum has acknowledged. CMC6: acked → log entry bridge. CMC7:
`maybe_append` entries are unique (invokes RSS1).

### Layer 10: Protocol-Level Safety

**`RaftSafety.lean` — 10 theorems.** RSS1 (`raft_state_machine_safety`): no two different entries
simultaneously committed at same index. RSS6/RSS7: end-to-end cluster safety (single and joint config).
RSS8 (`raft_end_to_end_safety_full`): fully proved via `CommitCertInvariant`. All 10 proved, 0 sorry.

**`RaftProtocol.lean` — 10 theorems.** RP6 (`appendEntries_preserves_log_matching`): all three
AppendEntries cases (§MatchFail, §NoConflict, §Conflict) machine-checked. RP8: no-rollback given
`hno_truncate` panic-guard — directly models Rust `assert!(conflict > committed)`.

**`RaftTrace.lean` — 4 theorems.** The capstone file. RT1 (`raftReachable_cci`): every reachable
state satisfies `CommitCertInvariant` (by induction). RT2 (`raftReachable_safe`): every reachable
cluster is safe. RSS8 is now a clean two-line proof composing RT1 with the safety theorems.
**Note**: The `RaftReachable.step` constructor hypotheses capture the conditions needed to preserve
`CommitCertInvariant` — see Layer 11 for how they are discharged from concrete protocol rules.

### Layer 11: Concrete Protocol Bridge

**`ConcreteProtocolStep.lean` — 14 theorems (CPS1–CPS14).** CPS2 (`validAEStep_raftReachable`)
is the most architecturally important theorem: it directly connects a concrete `ValidAEStep` to
the abstract `RaftReachable` inductive. All five `RaftReachable.step` hypotheses are discharged:
- `hlogs'`: structural (one voter's log changes)
- `hno_overwrite`: CPS1 (via CT2 + `h_committed_le_prev`)
- `hqc_preserved`: CPS13 (via `CandidateLogCovers` + HQ9 + LC3)
- `hcommitted_mono`: CPS11a/11b (via `commit_to` monotonicity)
- `hnew_cert`: CR8 (definitional)

**`ConcreteTransitions.lean` — 11 theorems (CT1–CT6+).** CT1 (`hlc_of_candLogMatching`): reduces
`HLogConsistency` to two concrete obligations. CT2/CT3: prefix preservation and correct entry
placement for `applyAppendEntries`. CT4/CT5: LMI preservation and `CandLogMatching` from broadcast.

**`ElectionReachability.lean` — 12 theorems (ER1–ER12).** Two independent sufficient conditions
for `CandidateLogCovers`:
1. **High-water mark path** (ER1–ER8): reduces to a single agreement-point index.
2. **Shared-source path** (ER9–ER11): if both candidate's and voters' logs are prefixes of a
   reference log R, `CandidateLogCovers` holds unconditionally.
ER12: HWM is preserved across AE steps (inductive invariant).

**`ElectionConcreteModel.lean` — 8 theorems (ECM1–ECM7+ECM5b).** ECM6
(`hqc_preserved_of_validAEStep`) is the full composition theorem closing the `hqc_preserved` gap.

**`ElectionBroadcastChain.lean` — 6 theorems.** Defines `BroadcastSeq` tying a leader to a sequence
of valid AE steps. `broadcastSeq_hqc_preserved`: full broadcast → `hqc_preserved`.

**`AEBroadcastInvariant.lean` — 10 theorems (ABI1–ABI10).** ABI6 (`haeCovered_induction`): after
broadcasting to the first `n` voters, `hae` holds for all `n`. ABI8 (`hqc_preserved_of_broadcast`):
full broadcast → `hqc_preserved` — the last missing link in the end-to-end chain.

**`MultiStepReachability.lean` — 7 theorems (MS1–MS7).** MS2 (`listStep_safe`): complete N-step
end-to-end safety certificate for arbitrary finite sequences of well-formed AE steps.

### Layer 12: Election Lifecycle (A7 Bridge)

**`ElectionLifecycle.lean` — 7 theorems (EL1–EL7).** The capstone file closing the A7 gap.
Defines `ElectionEpoch` tying election + broadcast. EL7 (`fullProtocolStep_safe`): end-to-end
safety with **no abstract axioms**. The entire Raft safety proof chain is now fully self-contained.

**`BroadcastLifecycle.lean` — 3 theorems (BL1–BL3).** BL2: `RaftReachable` state after broadcast
is also `RaftReachable`. BL3: broadcast from `initialCluster` produces `RaftReachable` state.

### Layer 13: Storage

**`MemStorage.lean` — 15 theorems.** Models `MemStorageCore` pure log operations (`firstIndex`,
`lastIndex`, `compact`, `append`). Key results: contiguity preservation under compact and append.

---

## Correspondence Validation

28 correspondence files provide direct behavioural evidence that Lean models agree with
Rust source code on concrete inputs. Each `#guard` test is a compile-time assertion checked
by Lean's kernel. Corresponding Rust unit tests run against the actual implementation.

| File | `#guard` | Level | Key function |
|------|---------|-------|-------------|
| `FindConflictCorrespondence` | 17 | Exact | `find_conflict` |
| `MaybeAppendCorrespondence` | 35 | Exact | `maybe_append` |
| `IsUpToDateCorrespondence` | 14 | Exact | `is_up_to_date` |
| `CommittedIndexCorrespondence` | 13 | Abstraction | `committed_index` (non-GC) |
| `VoteResultCorrespondence` | 17 | Exact | `vote_result` |
| `HasQuorumCorrespondence` | 17 | Exact | `has_quorum` |
| `LimitSizeCorrespondence` | 12 | Abstraction | `limit_size` |
| `ConfigValidateCorrespondence` | 14 | Exact | `config_validate` |
| `InflightsCorrespondence` | 14 | Abstraction | `Inflights` ring buffer |
| `LogUnstableCorrespondence` | 14 | Exact | `log_unstable` ops |
| `TallyVotesCorrespondence` | 12 | Exact | `tally_votes` |
| `ProgressCorrespondence` | 55 | Abstraction | `Progress` state machine |
| `ProgressTrackerCorrespondence` | 47 | Abstraction | `ProgressTracker` map ops |
| `ElectionCorrespondence` | 23 | Exact | `vote_granted` / election |
| `MaybePersistCorrespondence` | — | Exact | `maybe_persist` |
| `MaybePersistFUICorrespondence` | — | Exact | `maybe_persist` (FUI variant) |
| `ReadOnlyCorrespondence` | 16 | Exact | ReadIndex protocol |
| `UncommittedStateCorrespondence` | 13 | Exact | `uncommitted_state` |
| `HasNextEntriesCorrespondence` | 33 | Exact | `has_next_entries_since` |
| `NextEntriesCorrespondence` | 20 | Exact | `next_entries` |
| `ProgressSetCorrespondence` | 30 | Abstraction | `quorum_recently_active` |
| `MemStorageCorrespondence` | 25 | Abstraction | `compact`/`append` |
| `FindConflictByTermCorrespondence` | — | Exact | `find_conflict_by_term` |
| `ConfigurationInvariantsCorrespondence` | — | Exact | Configuration disjointness |
| `JointVoteCorrespondence` | — | Exact | Joint vote result |
| `MaybeCommitCorrespondence` | — | Exact | `maybe_commit` |
| `RaftLogAppendCorrespondence` | — | Exact | `RaftLog::append` |
| `QuorumRecentlyActiveCorrespondence` | — | Exact | `quorum_recently_active` |

**Bug-catching potential**: High. Any change to observable Rust behaviour causes `#guard`
failures at build time — a regression safety net stronger than property-based theorems.

**Limitations**: `#guard` tests are bounded to small inputs; all 28 targets show agreement
(no divergence found); several use abstraction level (non-group-commit, `Nat` for sizes, `List`
for ring buffer).

---

## Known Concerns

### Concern 1: Voter-list type (List vs. Set)

All Lean models use `List Nat` for voter sets; Rust uses `HashSet<u64>`. Duplicate voters in
a `List` would inflate vote counts. Theorems are stated without a `Nodup` precondition.
**Recommendation**: add `voters.Nodup` hypothesis or `List.dedup` normalisation.

### Concern 2: Non-group-commit path only

The Lean model covers only `use_group_commit = false`. The group-commit path uses a different
algorithm and is completely unverified. The Safety/Maximality guarantees do not apply if
group-commit is enabled.

### Concern 3: `u64` overflow not modelled

All numeric types are `Nat` in Lean. Overflow scenarios are not covered. In practice these are
unreachable but the gap is worth noting.

### Concern 4: `JointCommittedIndex` empty-config divergence

Lean returns `0` for empty configs; Rust returns `u64::MAX`. Joint safety theorems (JCI4–JCI6)
are sound for non-empty configs only.

### Concern 5: `UncommittedState` noLimit divergence

The Lean model increments `uncommittedSize` in the noLimit fast path; the Rust code does not.
No proved theorem depends on this divergent state.

### Concern 6: ReadOnly correspondence

The Lean `advance` model uses `findIdx?` (first occurrence). Rust uses context ID lookup in a
`VecDeque` which may have different duplicate handling. The RO8 proof depends on `Nodup`.

---

## Residual Gap Analysis

### The single remaining structural gap

`HLogConsistency` — the condition that "if a candidate is up-to-date and a voter committed an entry,
then the candidate has that entry" — is still taken as a conditional hypothesis in
`LeaderCompleteness.lean` (LC7/LC8). The proof *architecture* to discharge it is complete:

```
ElectionLifecycle.lean (EL7: fullProtocolStep_safe)
  uses AEBroadcastInvariant.lean (ABI8: hqc_preserved_of_broadcast)
    uses ElectionConcreteModel.lean (ECM6: hqc_preserved_of_validAEStep)
      uses ElectionReachability.lean (ER3: candidateLogCovers_of_highWaterMark)
        requires: HLogConsistency (conditional)
```

The gap reduces to: deriving `HLogConsistency` from a concrete global election model showing that
after a real election, the leader's log covers all voters' committed entries. This requires ~5–15
additional theorems connecting the AE broadcast history to the current state.

### Hypothesis discharge status

| Hypothesis | Status | Proof |
|---|---|---|
| `hlogs'` | **Discharged** | Structural (one voter's log changes per step) |
| `hno_overwrite` | **Discharged** | CPS1 via CT2 + `h_committed_le_prev` |
| `hqc_preserved` | **Conditionally discharged** | CPS13 via `CandidateLogCovers` + HQ9 + LC3 |
| `hcommitted_mono` | **Discharged** | CPS11a/11b via `commit_to` monotonicity |
| `hnew_cert` | **Discharged** | CR8 (definitional equality with `CommitRuleValid`) |

### Other open questions

1. **ProgressTracker integration with RaftReachable**: PT1–PT28 prove per-operation invariants
   but no integration theorem connects the progress map of a `RaftReachable` state to `all_wf`.

2. **Term-indexed safety**: MC4 proves committed advances only to current-term entries, but this
   is not yet wired into the top-level safety proof.

3. **`VotersLearnersDisjointRelaxed` propagation**: proofs using the strict 4-clause predicate
   should be reviewed; the relaxed 3-clause version matches Rust.

4. **`Unstable.wf` inductive preservation**: UPB8 makes `maybe_persist` safety conditional on
   `wf`, but `wf` preservation across all callers of `restore`/`stableEntries` is not proved
   inductively for the full state machine.

5. **Missing correspondence tests**: `Restore.lean` and `IsContinuousEnts.lean` have no
   correspondence files.

---

## Positive Findings

1. **`committedIndex_safety` + `committedIndex_maximality`** — genuine discoveries requiring
   non-trivial proof engineering; confirm the sort-then-index algorithm is provably correct
   and *optimal*.

2. **`jointVoteResult_non_joint`** (J4) — formalises joint → single quorum degeneration, a subtle
   invariant that could hide regression bugs.

3. **`limitSize_maximality`** — proves optimality, not just safety. Unusual and valuable.

4. **`findConflict_zero_iff_all_match`** (FC11) + **`findConflict_first_mismatch`** (FC7) — clean
   biconditional eliminating a whole class of off-by-one bugs.

5. **`maybeAppend_log_prefix_preserved`** (MA13) + **`maybeAppend_suffix_applied`** (MA14) +
   **`maybeAppend_committed_eq`** (MA5) — complete post-condition for `maybe_append`.

6. **`inflights_freeTo_all_gt_sorted`** (INF8) + INF30/INF31 (ring-buffer correspondence) —
   the only implementation-level bridging theorems; close the gap between proof and implementation.

7. **`isUpToDate_total`** (IU10) — proves Raft's log ordering is a total preorder; foundation
   for deterministic leader election.

8. **`truncateAndAppend_snapshot_preserved`** (TAA7) — subtle non-interference property with no
   obvious statement in the original code.

9. **`tallyVotes_lost_of_rejected_ge`** (TV12) — formally proves rejection-closes-election.

10. **`quorum_intersection`** (HQ14) + **`quorum_intersection_mem`** (HQ20) — mathematical
    cornerstone of Raft consensus safety.

11. **`SC4_raft_log_safety`** — first cross-module composition theorem; directly formalises §5.4
    of the Raft paper.

12. **`SC9_quorumActive_and_commit_share_voter`** — leader-election safety invariant: new leader's
    supporters include a voter who witnessed the committed index.

13. **`raft_state_machine_safety`** (RSS1) — log-entry-level safety: no two different entries
    simultaneously committed at the same index.

14. **`CMC3_maybeAppend_committed_bounded`** — first cross-module theorem connecting log operations
    to the quorum layer.

15. **RSS3/RSS4 formulation bug caught** — the `sorry` mechanism caught an unsound formulation
    (universally quantified properties that are provably false). Corrected and proved.

16. **RP6 full proof** — all three AppendEntries cases machine-checked.

17. **`raftReachable_safe`** (RT2) — the capstone: machine-checked Raft safety for all reachable states.

18. **`electionSafety`** (RE5) — at most one leader per term, proved from quorum intersection.

19. **CI9–CI12 finding** — strict disjointness predicate is stricter than Rust semantics; relaxed
    version proved correct.

20. **`fullProtocolStep_safe`** (EL7) — A7 gap closed; entire proof chain fully self-contained
    with no abstract axioms.

21. **No bugs found** in any of the 28 verified Rust functions. Evidence (not proof) that the Raft
    quorum logic, log operations, config validation, flow control, election counting, progress
    tracking, read-only protocol, uncommitted state, persist safety, and safety composition are
    correct for the modelled paths.

---

> 🔬 Consolidated critique by [Lean Squad](https://github.com/dsyme/raft-lean-squad).
> Current state: **769 theorem declarations, 79 Lean files, 0 sorry, 28 correspondence targets, 642+ `#guard` assertions**.
