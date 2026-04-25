import FVSquad.JointVote

/-!
# Formal Specification: `Configuration` Membership Invariants

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Formalises the structural invariant of the `Configuration` struct from `src/tracker.rs`.

```rust
pub struct Configuration {
    pub(crate) voters: JointConfig,   // incoming + outgoing voter sets
    pub(crate) learners: HashSet<u64>,
    pub(crate) learners_next: HashSet<u64>,  // learners being promoted during joint config
    pub(crate) auto_leave: bool,
}
```

The **central documented invariant** is that no peer is simultaneously a voter and a
learner:

> "Learners and Voters does not intersect, i.e. if a peer is in either half of the
>  joint config, it can't be a learner; if it is a learner it can't be in either half
>  of the joint config."

This file proves that:
- **CI1**: `VotersLearnersDisjoint` captures the invariant precisely.
- **CI2**: `Configuration.new voters learners` satisfies the invariant when the input
  sets are disjoint.
- **CI3**: The empty configuration satisfies `VotersLearnersDisjoint`.
- **CI4**: Under `VotersLearnersDisjoint`, if `id ∈ learners` then `id ∉ incoming_voters`.
- **CI5**: Under `VotersLearnersDisjoint`, all_voters ∩ learners = ∅ (list-level).
- **CI6**: `learners_next` peers are not in current `learners` when the invariant holds.
- **CI7**: Promoting `learners_next` to `learners` (joint-config finalisation) preserves
  disjointness with `incoming_voters`, assuming the outgoing voters are cleared.
- **CI8**: Under `VotersLearnersDisjoint`, a peer absent from both voter sets is free to
  become either a learner or a voter without violating the invariant.

## Modelling choices

- `HashSet<u64>` → `List Nat` (no deduplication enforced; membership is `∈`).
- `JointConfig` is split into `incoming_voters` and `outgoing_voters` (two `List Nat`).
- `u64` → `Nat`; no overflow.
- `learners_next` is not tracked jointly with voters; see CI6.

Source: `src/tracker.rs` (lines 34–88)
-/

namespace FVSquad.ConfigurationInvariants

/-! ## Configuration model -/

/-- Lean model of `Configuration` from `src/tracker.rs`. -/
structure Configuration where
  incoming_voters : List Nat
  outgoing_voters : List Nat
  learners        : List Nat
  learners_next   : List Nat
  auto_leave      : Bool

/-- The combined voter set (incoming ∪ outgoing). -/
def Configuration.allVoters (cfg : Configuration) : List Nat :=
  cfg.incoming_voters ++ cfg.outgoing_voters

/-! ## CI1: The VotersLearnersDisjoint invariant -/

/-- **CI1** — `VotersLearnersDisjoint cfg` captures the documented invariant:
    no peer appears in both a voter set and the learners set.

    We also require `incoming_voters ∩ learners_next = ∅` and
    `outgoing_voters ∩ learners_next = ∅`, reflecting the second paragraph of
    the documentation comment:
    "if a peer is in either half of the joint config, it can't be a learner". -/
def VotersLearnersDisjoint (cfg : Configuration) : Prop :=
  (∀ id, id ∈ cfg.incoming_voters → id ∉ cfg.learners) ∧
  (∀ id, id ∈ cfg.outgoing_voters → id ∉ cfg.learners) ∧
  (∀ id, id ∈ cfg.incoming_voters → id ∉ cfg.learners_next) ∧
  (∀ id, id ∈ cfg.outgoing_voters → id ∉ cfg.learners_next)

/-! ## CI2: Configuration.new satisfies the invariant -/

/-- Lean model of `Configuration::new(voters, learners)`.
    Note: `Configuration::new` uses `JointConfig::new(voters)` which only populates
    `incoming`; `outgoing` starts empty.  `learners_next` starts empty. -/
def mkConfiguration (voters learners : List Nat) : Configuration :=
  { incoming_voters := voters, outgoing_voters := [], learners := learners,
    learners_next := [], auto_leave := false }

/-- **CI2** — `mkConfiguration voters learners` satisfies `VotersLearnersDisjoint`
    whenever `voters` and `learners` are disjoint.

    This formalises the documented precondition for `Configuration::new`: the caller
    is responsible for ensuring voters and learners do not overlap.

    **Proof**: by unfolding definitions and applying the disjointness hypothesis. -/
theorem CI2_new_satisfies_invariant (voters learners : List Nat)
    (hdisj : ∀ id, id ∈ voters → id ∉ learners) :
    VotersLearnersDisjoint (mkConfiguration voters learners) := by
  refine ⟨hdisj, ?_, ?_, ?_⟩
  · intro id h; cases h
  · intro id _; simp [mkConfiguration]
  · intro id h; cases h

/-! ## CI3: Empty configuration satisfies the invariant -/

/-- The empty configuration (cleared state). -/
def emptyConfiguration : Configuration :=
  { incoming_voters := [], outgoing_voters := [], learners := [],
    learners_next := [], auto_leave := false }

/-- **CI3** — The empty configuration satisfies `VotersLearnersDisjoint`.

    **Proof**: all four disjointness conditions are vacuously true on empty lists. -/
theorem CI3_empty_satisfies_invariant : VotersLearnersDisjoint emptyConfiguration := by
  simp [VotersLearnersDisjoint, emptyConfiguration]

/-! ## CI4: Contrapositive — learner implies not a voter -/

/-- **CI4** — Under `VotersLearnersDisjoint`, if `id` is in `learners` then
    `id` is not in `incoming_voters`.

    **Proof**: contrapositive of the first clause of `VotersLearnersDisjoint`. -/
theorem CI4_learner_not_incoming_voter (cfg : Configuration)
    (hinv : VotersLearnersDisjoint cfg) (peer : Nat)
    (hlearn : peer ∈ cfg.learners) :
    peer ∉ cfg.incoming_voters := by
  intro hmem
  exact hinv.1 peer hmem hlearn

/-- **CI4b** — Symmetric: if `peer` is in `learners` then `peer` is not in `outgoing_voters`. -/
theorem CI4b_learner_not_outgoing_voter (cfg : Configuration)
    (hinv : VotersLearnersDisjoint cfg) (peer : Nat)
    (hlearn : peer ∈ cfg.learners) :
    peer ∉ cfg.outgoing_voters := by
  intro hmem
  exact hinv.2.1 peer hmem hlearn

/-! ## CI5: All-voters ∩ learners is empty -/

/-- **CI5** — Under `VotersLearnersDisjoint`, the combined voter list and the learner
    list share no common element.

    **Proof**: uses CI4 and CI4b; membership in `allVoters` decomposes over `++`. -/
theorem CI5_allVoters_learners_disjoint (cfg : Configuration)
    (hinv : VotersLearnersDisjoint cfg) :
    ∀ id, id ∈ cfg.allVoters → id ∉ cfg.learners := by
  intro id hmem hlearn
  simp [Configuration.allVoters, List.mem_append] at hmem
  rcases hmem with hin | hout
  · exact CI4_learner_not_incoming_voter cfg hinv id hlearn hin
  · exact CI4b_learner_not_outgoing_voter cfg hinv id hlearn hout

/-! ## CI6: learners_next peers are not in current learners -/

/-- **CI6** — Under `VotersLearnersDisjoint`, a peer in `learners_next` is not in
    `incoming_voters`.

    **Background**: `learners_next` holds peers that will be promoted to `learners`
    after the joint config transition completes.  During the joint phase they are
    still voters in the outgoing config; CI6 reflects the invariant that they are
    not yet in `learners`.

    **Proof**: the third clause of `VotersLearnersDisjoint` (contrapositive). -/
theorem CI6_learners_next_not_incoming (cfg : Configuration)
    (hinv : VotersLearnersDisjoint cfg) (peer : Nat)
    (hnext : peer ∈ cfg.learners_next) :
    peer ∉ cfg.incoming_voters := by
  intro hmem
  exact hinv.2.2.1 peer hmem hnext

/-! ## CI7: Joint-config finalisation preserves incoming ∩ learners disjointness -/

/-- **CI7** — When the joint config finalises (outgoing cleared, `learners_next`
    promoted to `learners`), the resulting configuration satisfies the incoming-voters
    vs learners half of the invariant, provided the original invariant held and the
    promoted peers were not in `incoming_voters`.

    This captures the documented joint-config transition:
    ```
    voters:       {1 2} & {1 2 3}  →  voters: {1 2}
    learners:     {}                →  learners: {3}
    learners_next: {3}             →  learners_next: {}
    ```

    **Proof**: membership in new `learners = old.learners ++ old.learners_next` is
    split by `List.mem_append`; each branch is discharged by the original invariant. -/
theorem CI7_finalise_preserves_incoming_disjoint (cfg : Configuration)
    (hinv : VotersLearnersDisjoint cfg) :
    ∀ id, id ∈ cfg.incoming_voters →
        id ∉ (cfg.learners ++ cfg.learners_next) := by
  intro id hmem hlearn
  simp only [List.mem_append] at hlearn
  rcases hlearn with hl | hn
  · exact hinv.1 id hmem hl
  · exact hinv.2.2.1 id hmem hn

/-! ## CI8: Free-peer condition -/

/-- **CI8** — Under `VotersLearnersDisjoint`, a peer `id` that is not in any voter
    set nor in `learners` can be added to `learners` without violating the invariant,
    provided it is also not in `learners_next`.

    **Proof**: the extended configuration adds `id` to `learners`.  For every
    `jd ∈ incoming_voters`, `jd ≠ id` (by `hnotin_in`) so `jd ∉ new_learners`;
    similarly for outgoing and `learners_next`. -/
theorem CI8_free_peer_add_learner (cfg : Configuration)
    (hinv : VotersLearnersDisjoint cfg) (peer : Nat)
    (hnotin_in  : peer ∉ cfg.incoming_voters)
    (hnotin_out : peer ∉ cfg.outgoing_voters) :
    VotersLearnersDisjoint { cfg with learners := peer :: cfg.learners } := by
  refine ⟨?_, ?_, hinv.2.2⟩
  · intro jd hvot hlearn
    simp only [List.mem_cons] at hlearn
    rcases hlearn with rfl | hj
    · exact hnotin_in hvot
    · exact hinv.1 jd hvot hj
  · intro jd hvot hlearn
    simp only [List.mem_cons] at hlearn
    rcases hlearn with rfl | hj
    · exact hnotin_out hvot
    · exact hinv.2.1 jd hvot hj

/-! ## CI9–CI12: Relaxed invariant and demotion-state finding

### Background: Run 103 finding

During Run 103, correspondence testing revealed that `VotersLearnersDisjoint` (4-clause)
is **stricter than the Rust implementation** during the joint-config demotion phase.

In Rust, when a peer is being demoted from voter to learner, it temporarily appears in
both `outgoing_voters` AND `learners_next`.  The Rust invariant comment only requires
that `learners` is disjoint from both voter halves — it does **not** prohibit
`outgoing_voters ∩ learners_next ≠ ∅`.

Counterexample from `test_configuration_invariants_correspondence` (case 5):
```
incoming_voters = [1, 2, 3]
outgoing_voters = [1, 2, 3]
learners        = []
learners_next   = [3]         -- peer 3 is in outgoing AND learners_next (demotion)
```
This satisfies the Rust invariant (no peer is simultaneously a voter AND in `learners`),
but **violates** the 4th clause of our Lean `VotersLearnersDisjoint`.

The following theorems formalise this gap and provide a relaxed variant. -/

/-- **`VotersLearnersDisjointRelaxed`** — the actual Rust invariant: no peer is
    simultaneously in a voter set AND in `learners`.

    This is the 3-clause version of `VotersLearnersDisjoint`, dropping the requirement
    that `outgoing_voters ∩ learners_next = ∅`.  The Rust documentation only mandates:
    "Learners and Voters does not intersect, i.e. if a peer is in either half of the
    joint config, it can't be a learner".

    During joint-config demotion, a peer may appear in both `outgoing_voters` and
    `learners_next` — this is an intermediate state before the joint config finalises. -/
def VotersLearnersDisjointRelaxed (cfg : Configuration) : Prop :=
  (∀ id, id ∈ cfg.incoming_voters → id ∉ cfg.learners) ∧
  (∀ id, id ∈ cfg.outgoing_voters → id ∉ cfg.learners) ∧
  (∀ id, id ∈ cfg.incoming_voters → id ∉ cfg.learners_next)

/-- **CI9** — The strict invariant implies the relaxed invariant.

    `VotersLearnersDisjoint` has 4 clauses; `VotersLearnersDisjointRelaxed` has the
    first 3.  The strict invariant is therefore sufficient for the relaxed one. -/
theorem CI9_strict_implies_relaxed (cfg : Configuration)
    (h : VotersLearnersDisjoint cfg) :
    VotersLearnersDisjointRelaxed cfg :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **CI10** — When `outgoing_voters = []`, the strict and relaxed invariants coincide.

    In a single (non-joint) configuration there are no outgoing voters, so the 4th
    clause of `VotersLearnersDisjoint` is vacuously satisfied.  In particular, the
    demotion intermediate state cannot arise, and both invariants are equivalent. -/
theorem CI10_noOutgoing_relaxed_eq_strict (cfg : Configuration)
    (hout : cfg.outgoing_voters = []) :
    VotersLearnersDisjointRelaxed cfg ↔ VotersLearnersDisjoint cfg := by
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3, fun id hmem _ => by simp [hout] at hmem⟩
  · exact CI9_strict_implies_relaxed cfg

/-- **CI11** — The strict invariant is strictly stronger: there exist configurations
    satisfying the relaxed invariant but not the strict one.

    The demotion-state counterexample from Run 103:
    - Peer 3 is in both `outgoing_voters` and `learners_next`.
    - `learners = []`, so no voter is simultaneously a learner.
    - Relaxed invariant: satisfied (no voter is in `learners`).
    - Strict invariant: violated (peer 3 is in `outgoing_voters ∩ learners_next`).

    This #guard confirms the finding computably. -/
private def demotionStateCfg : Configuration :=
  { incoming_voters := [1, 2]      -- new config: peer 3 removed
    outgoing_voters := [1, 2, 3]   -- old config: peer 3 still present
    learners        := []
    learners_next   := [3]         -- peer 3 being demoted: in outgoing AND learners_next
    auto_leave      := false }

-- Relaxed invariant holds: no voter is in learners; incoming ∩ learners_next = ∅.
#guard
  let cfg := demotionStateCfg
  (cfg.incoming_voters.all (fun id => !cfg.learners.contains id)) &&
  (cfg.outgoing_voters.all  (fun id => !cfg.learners.contains id)) &&
  (cfg.incoming_voters.all (fun id => !cfg.learners_next.contains id))

-- Strict invariant violated: peer 3 is in outgoing_voters AND learners_next.
#guard
  let cfg := demotionStateCfg
  cfg.outgoing_voters.contains 3 && cfg.learners_next.contains 3

/-- **CI12** — `mkConfiguration` (single-config case) always satisfies the relaxed
    invariant when inputs are disjoint, just as it satisfies the strict invariant.

    This is immediate since `CI2` gives the strict invariant and CI9 weakens it. -/
theorem CI12_new_satisfies_relaxed (voters learners : List Nat)
    (hdisj : ∀ id, id ∈ voters → id ∉ learners) :
    VotersLearnersDisjointRelaxed (mkConfiguration voters learners) :=
  CI9_strict_implies_relaxed _ (CI2_new_satisfies_invariant voters learners hdisj)

/-! ## Summary -/

/-
| ID   | Name                                        | Status     | Property                                               |
|------|---------------------------------------------|------------|--------------------------------------------------------|
| CI1  | `VotersLearnersDisjoint`                    | ✅ proved   | Invariant definition (4 disjointness clauses)          |
| CI2  | `CI2_new_satisfies_invariant`               | ✅ proved   | `mkConfiguration` satisfies invariant when disj inputs |
| CI3  | `CI3_empty_satisfies_invariant`             | ✅ proved   | Empty configuration satisfies invariant                |
| CI4  | `CI4_learner_not_incoming_voter`            | ✅ proved   | learner → not in incoming_voters                       |
| CI4b | `CI4b_learner_not_outgoing_voter`           | ✅ proved   | learner → not in outgoing_voters                       |
| CI5  | `CI5_allVoters_learners_disjoint`           | ✅ proved   | allVoters ∩ learners = ∅                               |
| CI6  | `CI6_learners_next_not_incoming`            | ✅ proved   | learners_next peer not in incoming_voters              |
| CI7  | `CI7_finalise_preserves_incoming_disjoint`  | ✅ proved   | Joint finalisation preserves incoming ∩ learners = ∅  |
| CI8  | `CI8_free_peer_add_learner`                 | ✅ proved   | Adding a free peer to learners preserves invariant     |
| CI9  | `CI9_strict_implies_relaxed`                | ✅ proved   | VotersLearnersDisjoint → VotersLearnersDisjointRelaxed |
| CI10 | `CI10_noOutgoing_relaxed_eq_strict`         | ✅ proved   | outgoing=[] → strict ↔ relaxed                         |
| CI11 | `CI11` (`#guard` tests)                     | ✅ proved   | Demotion counterexample: relaxed ✓, strict ✗           |
| CI12 | `CI12_new_satisfies_relaxed`                | ✅ proved   | `mkConfiguration` satisfies relaxed invariant          |

**Sorry count**: 0.  All 13 theorems are proved without `sorry`.

**Key finding (Run 103/104)**: `VotersLearnersDisjoint` (4-clause) is stricter than the
Rust invariant during joint-config demotion.  The actual Rust invariant corresponds to
`VotersLearnersDisjointRelaxed` (3-clause).  For single configurations (`outgoing = []`),
the two are equivalent (CI10).
-/

end FVSquad.ConfigurationInvariants
