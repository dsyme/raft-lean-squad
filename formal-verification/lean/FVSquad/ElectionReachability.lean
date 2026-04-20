import FVSquad.ConcreteProtocolStep

/-!
# ElectionReachability — Bridging CandLogMatching to CandidateLogCovers

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file advances the proof toward closing the remaining gap in `RaftTrace.lean`:
proving that the `hqc_preserved` condition holds for concrete Raft protocol steps.

## Background

The residual gap (see `ConcreteProtocolStep.lean` and `LeaderCompleteness.lean`) is:

```
RaftReachable.step ← requires hqc_preserved
hqc_preserved      ← CPS13 ← CandidateLogCovers
CandidateLogCovers ← LC3   ← CandLogMatching + CandLogCoversLastIndex  (via CT1 + LC7)
CandLogCoversLastIndex = ???  ← this file provides sufficient conditions
```

This file provides:

1. **The high-water mark reduction** (ER1–ER4): reduces `CandLogCoversLastIndex` (and
   hence the full `CandidateLogCovers` chain) to a *high-water mark* condition: for every
   voter `w`, there exists an index `j ≥ (voterLog w).index` at which the candidate's log
   and voter `w`'s log agree.  This is the cleanest abstract formulation of what the AE
   mechanism ensures.

2. **The extended-LMI bridge** (ER5–ER8): proves that the global `LogMatchingInvariantFor`
   (extended to treat the candidate as an extra "voter") implies `CandLogMatching`, and
   that a global agreement point gives the high-water mark condition.  This connects the
   standard Raft inductive invariant to the candidate-specific conditions.

3. **The shared-source theorem** (ER9–ER10): a clean end-to-end theorem showing that if
   there is a common reference log `R` from which both the candidate and all voters
   received their entries (the "common history" condition, satisfied after each AE round
   from a single leader), then `CandidateLogCovers` holds.

## Theorem table

| ID   | Name                                        | Status    | Description                                              |
|------|---------------------------------------------|-----------|----------------------------------------------------------|
| ER1  | `candLogCoversLastIndex_of_highWaterMark`   | ✅ proved  | HWM + CandLogMatching → CandLogCoversLastIndex           |
| ER2  | `hlogConsistency_of_highWaterMark`          | ✅ proved  | HWM + CandLogMatching → HLogConsistency                  |
| ER3  | `candidateLogCovers_of_highWaterMark`       | ✅ proved  | HWM + VRC + voterIdx → CandidateLogCovers                |
| ER4  | `leaderCompleteness_of_highWaterMark`       | ✅ proved  | Full chain: HWM → leaderCompleteness                     |
| ER5  | `candLogMatching_of_extendedLMI`            | ✅ proved  | Extended LMI + cand_eq (with candidate as voter) → CandLogMatching |
| ER6  | `hwm_of_shared_entry`                       | ✅ proved  | Shared entry at j ≥ voterIdx → high-water mark holds     |
| ER7  | `hwm_of_lmi_and_candEntry`                  | ✅ proved  | LMI + voter entry + cand entry at same j → HWM           |
| ER8  | `candidateLogCovers_of_extendedLMI`         | ✅ proved  | Extended LMI + hcand_eq + VRC + HWM → CandidateLogCovers |
| ER9  | `candLogCoversLastIndex_of_sharedSource`    | ✅ proved  | Shared source log R → CandLogCoversLastIndex             |
| ER10 | `candidateLogCovers_of_sharedSource`        | ✅ proved  | Shared source → CandidateLogCovers (full chain)          |
| ER11 | `leaderCompleteness_of_sharedSource`        | ✅ proved  | Shared source → leaderCompleteness (full end-to-end)     |
| ER12 | `hwm_of_ae_prefix`                          | ✅ proved  | AE prefix preservation: prior agreements survive AE step |

## Relationship to the Remaining Gap

After this file, the concrete proof obligation reduces to establishing the high-water
mark for a concrete Raft election + AE history.  The most natural sufficient condition
(`candLogCoversLastIndex_of_sharedSource`, ER9) says:

> "If both the candidate's log and every voter's log are prefixes of some reference log R,
> then `CandLogCoversLastIndex` holds."

In a concrete Raft protocol: after the leader sends AE messages that are accepted by a
quorum, both the leader's log and the accepting voters' logs are prefixes of the leader's
log R. So ER9 applies directly, reducing the remaining obligation to: prove that after
an election, there exists such a reference log.

**Remark on voterLog.index semantics**: throughout this file, `(voterLog w).index` is
treated as the index of the last entry in voter `w`'s log.  The condition
`hvoter_idx : ∀ w k e, logs w k = some e → k ≤ (voterLog w).index` encodes this.
-/

namespace FVSquad.ElectionReachability

open FVSquad.RaftSafety
open FVSquad.LeaderCompleteness
open FVSquad.ConcreteTransitions
open FVSquad.RaftElection

/-! ## ER1: High-water mark gives CandLogCoversLastIndex -/

/-- **ER1** — `CandLogCoversLastIndex` follows from `CandLogMatching` and a
    *high-water mark* condition: for each voter `w`, there exists some index `j ≥ (voterLog w).index`
    at which the candidate's log and voter `w`'s log agree.

    **Proof**: apply `CandLogMatching` at `j` (with `hagree : candLog j = logs w j`) to
    propagate agreement down to `(voterLog w).index ≤ j`.

    **Significance**: this reduces the abstract obligation `CandLogCoversLastIndex` to
    the existence of a single "high-water mark" agreement point for each voter.  In a
    concrete protocol, this point is provided by the AE mechanism:  after the leader
    sends AE up to index `j`, the voter's log agrees with the leader's at `j`. -/
theorem candLogCoversLastIndex_of_highWaterMark (E : Type)
    (voterLog : Nat → LogId)
    (logs : VoterLogs E) (candLog : Nat → Option E)
    (hclm : CandLogMatching E logs candLog)
    (hwm : ∀ w, ∃ j, (voterLog w).index ≤ j ∧ candLog j = logs w j) :
    CandLogCoversLastIndex E voterLog logs candLog := by
  intro w
  obtain ⟨j, hj, hagree⟩ := hwm w
  exact hclm w j hagree (voterLog w).index hj

/-! ## ER2: High-water mark gives HLogConsistency -/

/-- **ER2** — `HLogConsistency` follows from `CandLogMatching` and the high-water mark.

    **Proof**: ER1 gives `CandLogCoversLastIndex`; CT1 (`hlc_of_candLogMatching`) gives
    `HLogConsistency`.

    **What this unlocks**: `HLogConsistency` is the key hypothesis for LC7
    (`candidateLog_of_logMatchingAndUpToDate`), which produces `CandidateLogCovers`.
    So the remaining obligation is entirely in establishing `CandLogMatching` and `hwm`. -/
theorem hlogConsistency_of_highWaterMark (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E)
    (candLastTerm candLastIndex : Nat → Nat) (candLog : Nat → Option E)
    (hclm : CandLogMatching E logs candLog)
    (hwm : ∀ w, ∃ j, (voterLog w).index ≤ j ∧ candLog j = logs w j) :
    HLogConsistency E voterLog logs candLastTerm candLastIndex candLog :=
  hlc_of_candLogMatching E voterLog logs candLastTerm candLastIndex candLog hclm
    (candLogCoversLastIndex_of_highWaterMark E voterLog logs candLog hclm hwm)

/-! ## ER3: Full chain from high-water mark to CandidateLogCovers -/

/-- **ER3** — `CandidateLogCovers` follows from `CandLogMatching`, the high-water mark,
    `VoteRecordConsistency`, and the voter-index domination condition.

    **Proof chain**: ER2 → `HLogConsistency`; LC7 → `CandidateLogCovers`.

    This is the full bridge from the abstract invariants to the election-safety
    hypothesis used in `leaderCompleteness` (LC3). -/
theorem candidateLogCovers_of_highWaterMark (E : Type)
    (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat)
    (hclm : CandLogMatching E logs candLog)
    (hwm : ∀ w, ∃ j, (voterLog w).index ≤ j ∧ candLog j = logs w j)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hvoter_idx : ∀ w k e, w ∈ (hd :: tl) → logs w k = some e → k ≤ (voterLog w).index) :
    CandidateLogCovers E (hd :: tl) record term cand logs candLog :=
  candidateLog_of_logMatchingAndUpToDate hd tl record voterLog candLastTerm candLastIndex
    logs candLog term cand hconsist
    (hlogConsistency_of_highWaterMark E voterLog logs candLastTerm candLastIndex candLog
      hclm hwm)
    hvoter_idx

/-! ## ER4: Full chain from high-water mark to leaderCompleteness -/

/-- **ER4** — Leader completeness follows from `CandLogMatching`, the high-water mark,
    `VoteRecordConsistency`, the voter-index condition, and the election win.

    **Proof**: ER3 → `CandidateLogCovers`; LC3 → leader has the committed entry.

    **End-to-end significance**: this theorem shows that the abstract safety argument
    bottoms out at two conditions:
    - `CandLogMatching`: the candidate's log matches each voter's at all shared indices.
    - The high-water mark `hwm`: for each voter, there exists some agreement point above
      the voter's last index.
    Both conditions hold trivially after the AE broadcast that follows a new leader
    election (since AE copies the leader's log to each follower). -/
theorem leaderCompleteness_of_highWaterMark [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat) (k : Nat) (e : E)
    (hwin    : wonInTerm (hd :: tl) record term cand = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e)
    (hclm    : CandLogMatching E logs candLog)
    (hwm     : ∀ w, ∃ j, (voterLog w).index ≤ j ∧ candLog j = logs w j)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hvoter_idx : ∀ w k' e', w ∈ (hd :: tl) → logs w k' = some e' → k' ≤ (voterLog w).index) :
    candLog k = some e :=
  leaderCompleteness hd tl record term cand logs candLog k e hwin hcommit
    (candidateLogCovers_of_highWaterMark E hd tl record voterLog candLastTerm candLastIndex
      logs candLog term cand hclm hwm hconsist hvoter_idx)

/-! ## ER5: Extended LMI implies CandLogMatching -/

/-- **ER5** — If the *extended* `LogMatchingInvariantFor` holds — treating the candidate
    as an additional "voter" with identifier `cand` — and the candidate's log agrees with
    voter `cand`'s log (i.e., the candidate IS voter `cand`), then `CandLogMatching` holds.

    The extended log map is:
    ```
    extLogs w = if w = cand then candLog else logs w
    ```
    `LogMatchingInvariantFor E extLogs` states that any two logs in `extLogs` that agree
    at `k` agree at all `j ≤ k`.  By instantiating with voter `cand` and any voter `v ≠ cand`,
    we obtain `CandLogMatching E logs candLog`.

    **Hypothesis `hcand_eq`**: if the candidate is also a voter in `logs` (which is typical
    in Raft — the leader has both a "voter log" and acts as a candidate), then
    `hcand_eq : ∀ k, candLog k = logs cand k` ensures consistency for the `v = cand` case.

    **Significance**: this connects the *global* `LogMatchingInvariantFor` to the
    *candidate-specific* `CandLogMatching` condition. -/
theorem candLogMatching_of_extendedLMI (E : Type)
    (logs : VoterLogs E) (candLog : Nat → Option E) (cand : Nat)
    (hcand_eq : ∀ k, candLog k = logs cand k)
    (hext : LogMatchingInvariantFor E (fun w k => if w = cand then candLog k else logs w k)) :
    CandLogMatching E logs candLog := by
  intro v k hagree j hj
  by_cases hvc : v = cand
  · -- v = cand: candLog j = logs cand j, which is hcand_eq j
    subst hvc
    exact hcand_eq j
  · -- v ≠ cand: use extended LMI with v1 = cand, v2 = v
    have h_ext_agree : (fun w k => if w = cand then candLog k else logs w k) cand k =
                       (fun w k => if w = cand then candLog k else logs w k) v k := by
      simp only [ite_true, if_neg hvc]
      exact hagree
    have hlmi := hext cand v k h_ext_agree j hj
    simp only [ite_true, if_neg hvc] at hlmi
    exact hlmi

/-! ## ER6: Simple sufficient condition for high-water mark -/

/-- **ER6** — If the candidate's log and voter `w`'s log share a common entry at some
    index `j ≥ (voterLog w).index`, then the high-water mark condition holds for `w`.

    **Proof**: immediate — the witness is `j` itself.

    **Usage**: this is the building block for establishing `hwm` in concrete scenarios.
    For example, after a complete AE broadcast, the leader and each follower share the
    leader's entry at index `prevLogIndex + len(entries) ≥ (voterLog w).index`. -/
theorem hwm_of_shared_entry (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E) (candLog : Nat → Option E)
    (w j : Nat) (e : E)
    (hj     : (voterLog w).index ≤ j)
    (hcand  : candLog j = some e)
    (hvoter : logs w j = some e) :
    ∃ j', (voterLog w).index ≤ j' ∧ candLog j' = logs w j' :=
  ⟨j, hj, by rw [hcand, hvoter]⟩

/-! ## ER7: LMI + candidate entry at voter's index gives HWM -/

/-- **ER7** — If the extended `LogMatchingInvariantFor` holds and the candidate has some
    entry at voter `w`'s last index that matches voter `w`'s entry there, then the high-
    water mark holds for voter `w` (with witness `j = (voterLog w).index` itself).

    **Proof**: `hwm_of_shared_entry` with `j = (voterLog w).index`.

    **Usage**: if `CandLogCoversLastIndex` is known directly (e.g., from the AE step), the
    high-water mark holds with `j = (voterLog w).index`. -/
theorem hwm_of_lmi_and_candEntry (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E) (candLog : Nat → Option E)
    (w : Nat) (e : E)
    (hagree : candLog (voterLog w).index = logs w (voterLog w).index)
    (hentry : logs w (voterLog w).index = some e) :
    ∃ j, (voterLog w).index ≤ j ∧ candLog j = logs w j :=
  ⟨(voterLog w).index, Nat.le_refl _, hagree⟩

/-! ## ER8: Extended LMI + HWM witnesses → CandidateLogCovers -/

/-- **ER8** — `CandidateLogCovers` follows from the extended `LogMatchingInvariantFor`
    combined with the high-water mark condition.

    This combines ER5 (extended LMI + `hcand_eq` → `CandLogMatching`) with ER3 (CandLogMatching +
    HWM → `CandidateLogCovers`).

    **What this needs from the protocol**: one needs to show:
    1. The candidate is included in the global LMI (as the leader, it is always).
    2. `hcand_eq`: the candidate's log agrees with voter `cand`'s log (same node).
    3. For each voter `w`, there exists `j ≥ (voterLog w).index` where the candidate
       and voter agree.  After a complete AE broadcast, this holds at `j = voterLog.index`. -/
theorem candidateLogCovers_of_extendedLMI (E : Type)
    (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat)
    (hcand_eq : ∀ k, candLog k = logs cand k)
    (hext : LogMatchingInvariantFor E (fun w k => if w = cand then candLog k else logs w k))
    (hwm : ∀ w, ∃ j, (voterLog w).index ≤ j ∧ candLog j = logs w j)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hvoter_idx : ∀ w k e, w ∈ (hd :: tl) → logs w k = some e → k ≤ (voterLog w).index) :
    CandidateLogCovers E (hd :: tl) record term cand logs candLog :=
  candidateLogCovers_of_highWaterMark E hd tl record voterLog candLastTerm candLastIndex
    logs candLog term cand
    (candLogMatching_of_extendedLMI E logs candLog cand hcand_eq hext)
    hwm hconsist hvoter_idx

/-! ## ER9: Shared source log → CandLogCoversLastIndex -/

/-- **ER9** — If there is a *shared source log* `R` from which both the candidate's log
    and every voter's log are drawn at every relevant index, then `CandLogCoversLastIndex`
    holds.

    **Formal statement**: given:
    - `hR_cand : ∀ w, R (voterLog w).index = candLog (voterLog w).index`
      (the candidate's log at each voter's last index agrees with `R`)
    - `hR_voter : ∀ w, R (voterLog w).index = logs w (voterLog w).index`
      (each voter's log at their last index agrees with `R`)

    Then: `CandLogCoversLastIndex E voterLog logs candLog`.

    **Concrete interpretation**: in Raft, `R` is the leader's log at the time of the AE
    broadcast.  After all voters accept the AE, both the leader and each voter have the
    leader's entry at every index up to the AE's `prevLogIndex + len(entries)`.  If each
    voter's last index `(voterLog w).index` falls within this range, the shared source
    condition holds. -/
theorem candLogCoversLastIndex_of_sharedSource (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E) (candLog : Nat → Option E)
    (R : Nat → Option E)
    (hR_cand  : ∀ w, R (voterLog w).index = candLog (voterLog w).index)
    (hR_voter : ∀ w, R (voterLog w).index = logs w (voterLog w).index) :
    CandLogCoversLastIndex E voterLog logs candLog := by
  intro w
  rw [← hR_cand w, hR_voter w]

/-! ## ER10: Shared source → CandidateLogCovers -/

/-- **ER10** — `CandidateLogCovers` follows from the shared source condition.

    **Proof**: ER9 gives `CandLogCoversLastIndex`; CT1 gives `HLogConsistency`; LC7 gives
    `CandidateLogCovers`.

    **What this needs from the protocol** (the remaining gap): exhibit the reference log
    `R` and prove `hR_cand` and `hR_voter`.  In a concrete AE history model, `R` is the
    leader's log at the time of broadcast.  The voter's log at their last index is set by
    the AE step (see `applyAppendEntries` in `ConcreteTransitions.lean`), so `hR_voter`
    follows from the AE step definition.  `hR_cand` follows from the fact that the leader
    does not modify its own log during AE sends. -/
theorem candidateLogCovers_of_sharedSource (E : Type)
    (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat)
    (R : Nat → Option E)
    (hclm     : CandLogMatching E logs candLog)
    (hR_cand  : ∀ w, R (voterLog w).index = candLog (voterLog w).index)
    (hR_voter : ∀ w, R (voterLog w).index = logs w (voterLog w).index)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hvoter_idx : ∀ w k e, w ∈ (hd :: tl) → logs w k = some e → k ≤ (voterLog w).index) :
    CandidateLogCovers E (hd :: tl) record term cand logs candLog :=
  candidateLog_of_logMatchingAndUpToDate hd tl record voterLog candLastTerm candLastIndex
    logs candLog term cand hconsist
    (hlc_of_candLogMatching E voterLog logs candLastTerm candLastIndex candLog hclm
      (candLogCoversLastIndex_of_sharedSource E voterLog logs candLog R hR_cand hR_voter))
    hvoter_idx

/-! ## ER11: Shared source → leaderCompleteness (full end-to-end) -/

/-- **ER11** — Full end-to-end: given a shared source log `R`, leader completeness holds.

    This is the complete chain:
    ```
    sharedSource → CandLogCoversLastIndex  (ER9)
                 → HLogConsistency         (CT1)
                 → CandidateLogCovers      (LC7)
                 → candLog k = some e      (LC3)
    ```

    **Proof obligation for a concrete protocol**: the concrete derivation of `R` is the
    only remaining gap.  After a valid AE broadcast from the elected leader, both
    `hR_cand` and `hR_voter` hold for all voters who accepted the AE.  The leader's log
    is the natural `R`. -/
theorem leaderCompleteness_of_sharedSource [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat) (k : Nat) (e : E)
    (R : Nat → Option E)
    (hwin    : wonInTerm (hd :: tl) record term cand = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e)
    (hclm    : CandLogMatching E logs candLog)
    (hR_cand  : ∀ w, R (voterLog w).index = candLog (voterLog w).index)
    (hR_voter : ∀ w, R (voterLog w).index = logs w (voterLog w).index)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hvoter_idx : ∀ w k' e', w ∈ (hd :: tl) → logs w k' = some e' → k' ≤ (voterLog w).index) :
    candLog k = some e :=
  leaderCompleteness hd tl record term cand logs candLog k e hwin hcommit
    (candidateLogCovers_of_sharedSource E hd tl record voterLog candLastTerm candLastIndex
      logs candLog term cand R hclm hR_cand hR_voter hconsist hvoter_idx)

/-! ## ER12: After AE broadcast from leader, leader and voter agree -/

/-- **ER12** — After a valid AppendEntries step from the leader, the updated voter log
    agrees with the leader's log at every index `k ≤ msg.prevLogIndex` (the AE prefix).

    This is a direct consequence of `applyAE_preserves_prefix` (CT2): the AE step does
    not change any log entry below `prevLogIndex + 1`.  Since the leader's log is
    unchanged during the AE send, voter and leader agree at all prefix indices.

    **Usage for HWM**: If the leader and voter had a common entry at some index
    `j ≤ prevLogIndex` before the step, that agreement is preserved after the step.
    If additionally `j ≥ (voterLog w).index`, the high-water mark holds with witness `j`.

    **Connection to shared source (ER9)**: if the leader and voter's logs came from the
    same reference log `R` up to `prevLogIndex`, ER12 shows that agreement is preserved
    after the AE step.  Together with the new entries written by the AE step (which
    extend the shared region), the shared source condition (ER9/ER10) lifts to the full
    AE-updated cluster state. -/
theorem hwm_of_ae_prefix (E : Type)
    (candLog : Nat → Option E) (oldVLog : Nat → Option E)
    (msg : AppendEntriesMsg E)
    (w : Nat) (voterIdx : LogId)
    (hvoterIdx : voterIdx.index ≤ msg.prevLogIndex)
    (hagree : ∀ k, k ≤ msg.prevLogIndex → candLog k = oldVLog k) :
    let newVLog := applyAppendEntries E oldVLog msg
    candLog voterIdx.index = newVLog voterIdx.index := by
  simp only []
  rw [applyAE_preserves_prefix E oldVLog msg voterIdx.index hvoterIdx]
  exact hagree voterIdx.index hvoterIdx

/-! ## Evaluation: shared source in a 3-voter example -/

/-- Sanity check: if all voters and the candidate share log `R`, then
    `CandLogCoversLastIndex` holds (ER9 applied to a concrete case). -/
example : let voters := [1, 2, 3]
          let R : Nat → Option Nat := fun k => if k == 1 then some 10 else none
          let logs : Nat → Nat → Option Nat := fun _ k => R k
          let candLog : Nat → Option Nat := R
          let voterLog : Nat → LogId := fun _ => { term := 1, index := 1 }
          CandLogCoversLastIndex Nat voterLog logs candLog := by
  intro w
  simp [CandLogCoversLastIndex]

end FVSquad.ElectionReachability
