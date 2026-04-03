import FVSquad.MajorityVote

/-!
# Formal Specification: `ProgressTracker::has_quorum`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `ProgressTracker::has_quorum` from `src/tracker.rs:357`.

## What `has_quorum` does

```rust
pub fn has_quorum(&self, potential_quorum: &HashSet<u64>) -> bool {
    self.conf
        .voters
        .vote_result(|id| potential_quorum.get(&id).map(|_| true))
        == VoteResult::Won
}
```

Given a set of node IDs (`potential_quorum`) and the current voter list,
determines whether at least a majority of voters are present in the set.

Algorithm:
1. For each voter ID, check if it is in `potential_quorum` (→ `Some(true)`) or not (→ `None`).
2. Run `vote_result` with that check function.
3. Return `true` iff the result is `Won` (i.e., yes-count ≥ majority(voters)).
4. Special case: empty voters → always `true` (per `vote_result` convention).

## Key properties formalised

| ID  | Name                              | Description                                                 |
|-----|-----------------------------------|-------------------------------------------------------------|
| HQ1 | `hasQuorum_nil`                   | Empty voters always satisfy quorum                          |
| HQ2 | `overlapCount_le_length`          | Overlap count ≤ voter list length                           |
| HQ3 | `hasQuorum_iff_overlap`           | `hasQuorum` iff overlap ≥ majority (or empty voters)        |
| HQ4 | `overlapCount_all_in`             | All-in-set voters → overlap = length                        |
| HQ5 | `hasQuorum_true_of_all_in`        | All voters in set → quorum                                  |
| HQ6 | `overlapCount_none_in`            | No voters in set → overlap = 0                              |
| HQ7 | `hasQuorum_false_of_none_in`      | No voters in set, non-empty voters → not quorum             |
| HQ8 | `overlapCount_monotone`           | Superset in set → overlap non-decreasing                    |
| HQ9 | `hasQuorum_monotone`              | Superset of quorum-forming set also forms quorum            |
| HQ10| `two_majority_gt_length`          | 2 * majority(n) > n (key arithmetic for quorum safety)      |
| HQ11| `overlapCount_incl_excl`          | Inclusion-exclusion: ∩ + ∪ = A + B                         |
| HQ12| `overlapUnion_le_length`          | Union overlap ≤ voter list length                           |
| HQ13| `overlapIntersect_lb`             | Both quorums → intersection count ≥ 1                       |
| HQ14| `quorum_intersection`             | **Safety**: two quorums share ≥ 1 voter (non-empty voters)  |
| HQ15| `hasQuorum_singleton_self`        | Singleton voter with self in set → quorum                   |
| HQ16| `hasQuorum_singleton_absent`      | Singleton voter absent from set → not quorum                |
| HQ17| `hasQuorum_all_voters`            | Full voter set always forms quorum (non-empty list)         |
| HQ18| `overlapCount_append`             | overlapCount distributes over list append                   |
| HQ19| `overlapCount_pos_mem`            | Positive overlap implies a concrete member in the set       |
| HQ20| `quorum_intersection_mem`         | **Safety (concrete)**: produces explicit shared voter       |

## Modelling choices

- `HashSet<u64>` voters → `List Nat` (modelled as a list; uniqueness assumed where noted).
- `HashSet<u64>` potential_quorum → `Nat → Bool` (membership predicate).
- `u64` → `Nat`; no overflow modelled.
- Builds directly on `majority` and `VoteResult` from `FVSquad.MajorityVote`.
- The quorum intersection theorems (HQ14, HQ20) assume `voters ≠ []`; the empty-voters
  case is degenerate (always `Won`) and the intersection is vacuously empty.
-/

/-! ## Overlap counting -/

/-- Count voters that are members of the set given by predicate `inSet`.

    Directly implements the `potential_quorum.get(&id).map(|_| true)` part of
    `has_quorum`: counts how many voter IDs are present in `potential_quorum`. -/
def overlapCount : List Nat → (Nat → Bool) → Nat
  | [],      _ => 0
  | v :: vs, s => (if s v then 1 else 0) + overlapCount vs s

/-- Count voters in the intersection of two sets. -/
def intersectCount (voters : List Nat) (a b : Nat → Bool) : Nat :=
  overlapCount voters (fun v => a v && b v)

/-- Count voters in the union of two sets. -/
def unionCount (voters : List Nat) (a b : Nat → Bool) : Nat :=
  overlapCount voters (fun v => a v || b v)

/-! ## The pure functional model -/

/-- Determines whether `inSet` contains a majority of `voters`.

    Mirrors `ProgressTracker::has_quorum` in `src/tracker.rs:357`.
    Returns `true` iff `voters` is empty or `|voters ∩ inSet| ≥ majority(|voters|)`. -/
def hasQuorum (voters : List Nat) (inSet : Nat → Bool) : Bool :=
  match voters with
  | [] => true
  | _  => decide (overlapCount voters inSet ≥ majority voters.length)

/-! ## Evaluations -/

section Eval
-- [1, 2, 3]: majority = 2; {1, 2} present → overlap = 2 ≥ 2 → true
#eval hasQuorum [1, 2, 3] (fun v => v == 1 || v == 2)   -- true
-- [1, 2, 3]: {3} only → overlap = 1 < 2 → false
#eval hasQuorum [1, 2, 3] (fun v => v == 3)              -- false
-- Empty voters → true always
#eval hasQuorum [] (fun _ => false)                      -- true
-- Singleton [1] with {1} → overlap 1 ≥ majority 1 = 1 → true
#eval hasQuorum [1] (fun v => v == 1)                    -- true
-- Singleton [1] with {} → overlap 0 < 1 → false
#eval hasQuorum [1] (fun _ => false)                     -- false
-- [1,2,3,4]: majority = 3; {1,2,3} → overlap 3 ≥ 3 → true
#eval hasQuorum [1, 2, 3, 4] (fun v => v ≤ 3)           -- true
-- [1,2,3,4]: {1,2} → overlap 2 < 3 → false
#eval hasQuorum [1, 2, 3, 4] (fun v => v ≤ 2)           -- false
end Eval

/-! ## Basic lemmas -/

/-- HQ1: Empty voters always satisfy the quorum condition. -/
@[simp] theorem hasQuorum_nil (s : Nat → Bool) : hasQuorum [] s = true := rfl

/-- Unfolding rule for overlapCount on a non-empty list. -/
@[simp] theorem overlapCount_cons (v : Nat) (vs : List Nat) (s : Nat → Bool) :
    overlapCount (v :: vs) s = (if s v then 1 else 0) + overlapCount vs s := rfl

/-- Helper: hasQuorum on a non-empty list reduces to a decidable majority check. -/
theorem hasQuorum_cons_def (v : Nat) (vs : List Nat) (s : Nat → Bool) :
    hasQuorum (v :: vs) s =
    decide (overlapCount (v :: vs) s ≥ majority (v :: vs).length) := rfl

/-! ## Overlap count bounds -/

/-- HQ2: The overlap count is at most the number of voters. -/
theorem overlapCount_le_length (voters : List Nat) (s : Nat → Bool) :
    overlapCount voters s ≤ voters.length := by
  induction voters with
  | nil => simp [overlapCount]
  | cons v vs ih =>
    simp only [overlapCount_cons, List.length_cons]
    by_cases h : s v <;> simp [h] <;> omega

/-! ## Core characterisation -/

/-- HQ3: `hasQuorum voters s = true` iff voters is empty OR overlap ≥ majority. -/
theorem hasQuorum_iff_overlap (voters : List Nat) (s : Nat → Bool) :
    hasQuorum voters s = true ↔
    (voters = [] ∨ overlapCount voters s ≥ majority voters.length) := by
  cases voters with
  | nil => simp [hasQuorum]
  | cons v vs =>
    simp only [hasQuorum_cons_def, List.cons_ne_nil, false_or, decide_eq_true_eq]

/-! ## All-in and none-in cases -/

/-- HQ4: If all voters are in the set, the overlap count equals the voter list length. -/
theorem overlapCount_all_in (voters : List Nat) (s : Nat → Bool)
    (h : ∀ v ∈ voters, s v = true) :
    overlapCount voters s = voters.length := by
  induction voters with
  | nil => simp [overlapCount]
  | cons v vs ih =>
    simp only [overlapCount_cons, List.length_cons, List.mem_cons] at *
    have hv : s v = true := h v (Or.inl rfl)
    have hvs : ∀ w ∈ vs, s w = true := fun w hw => h w (Or.inr hw)
    rw [if_pos hv, ih hvs]
    omega

/-- HQ5: If all voters are in the set, the set forms a quorum. -/
theorem hasQuorum_true_of_all_in (voters : List Nat) (s : Nat → Bool)
    (h : ∀ v ∈ voters, s v = true) : hasQuorum voters s = true := by
  cases voters with
  | nil => rfl
  | cons v vs =>
    rw [hasQuorum_iff_overlap]
    right
    rw [overlapCount_all_in (v :: vs) s h]
    simp only [majority, List.length_cons]
    omega

/-- HQ6: If no voter is in the set, the overlap count is 0. -/
theorem overlapCount_none_in (voters : List Nat) (s : Nat → Bool)
    (h : ∀ v ∈ voters, s v = false) : overlapCount voters s = 0 := by
  induction voters with
  | nil => simp [overlapCount]
  | cons v vs ih =>
    simp only [overlapCount_cons, List.mem_cons] at *
    have hv : s v = false := h v (Or.inl rfl)
    have hvs : ∀ w ∈ vs, s w = false := fun w hw => h w (Or.inr hw)
    rw [if_neg (by simp [hv]), ih hvs]

/-- HQ7: If no voter is in the set and voters is non-empty, not a quorum. -/
theorem hasQuorum_false_of_none_in (v : Nat) (vs : List Nat) (s : Nat → Bool)
    (h : ∀ w ∈ v :: vs, s w = false) : hasQuorum (v :: vs) s = false := by
  rw [hasQuorum_cons_def, overlapCount_none_in (v :: vs) s h]
  have hm := majority_pos (v :: vs).length
  simp only [decide_eq_false_iff_not]
  omega

/-! ## Monotonicity -/

/-- HQ8: Larger (superset) set has at least as large overlap count. -/
theorem overlapCount_monotone (voters : List Nat) (s t : Nat → Bool)
    (h : ∀ v, s v = true → t v = true) :
    overlapCount voters s ≤ overlapCount voters t := by
  induction voters with
  | nil => simp [overlapCount]
  | cons v vs ih =>
    simp only [overlapCount_cons]
    by_cases hs : s v
    · have ht : t v = true := h v hs
      simp [hs, ht]; omega
    · by_cases ht : t v
      · simp [hs, ht]; omega
      · simp [hs, ht]; exact ih

/-- HQ9: If `s` forms a quorum and `t` is a superset of `s`, then `t` also forms a quorum. -/
theorem hasQuorum_monotone (voters : List Nat) (s t : Nat → Bool)
    (hsup : ∀ v, s v = true → t v = true)
    (hq : hasQuorum voters s = true) : hasQuorum voters t = true := by
  cases voters with
  | nil => rfl
  | cons v vs =>
    rw [hasQuorum_iff_overlap] at *
    rcases hq with hnil | hge
    · exact absurd hnil (List.cons_ne_nil _ _)
    · right
      exact Nat.le_trans hge (overlapCount_monotone (v :: vs) s t hsup)

/-! ## Quorum intersection arithmetic -/

/-- HQ10: For any `n`, `2 * majority(n) > n`.
    This is the key arithmetic property underlying majority-quorum safety:
    two majority quorums of the same voter set must overlap. -/
theorem two_majority_gt_length (n : Nat) : n < 2 * majority n := by
  simp only [majority]; omega

/-- HQ11: Inclusion-exclusion for overlap counts:
    intersection count + union count = A-count + B-count. -/
theorem overlapCount_incl_excl (voters : List Nat) (a b : Nat → Bool) :
    intersectCount voters a b + unionCount voters a b =
    overlapCount voters a + overlapCount voters b := by
  induction voters with
  | nil => simp [intersectCount, unionCount, overlapCount]
  | cons v vs ih =>
    simp only [intersectCount, unionCount, overlapCount_cons] at *
    by_cases ha : a v <;> by_cases hb : b v <;> simp [ha, hb] <;> omega

/-- HQ12: Union overlap ≤ voter list length. -/
theorem overlapUnion_le_length (voters : List Nat) (a b : Nat → Bool) :
    unionCount voters a b ≤ voters.length :=
  overlapCount_le_length voters (fun v => a v || b v)

/-- HQ13: If both `a` and `b` form quorums of `voters`, their intersection overlap is ≥ 1. -/
theorem overlapIntersect_lb (v : Nat) (vs : List Nat) (a b : Nat → Bool)
    (ha : overlapCount (v :: vs) a ≥ majority (v :: vs).length)
    (hb : overlapCount (v :: vs) b ≥ majority (v :: vs).length) :
    intersectCount (v :: vs) a b ≥ 1 := by
  have hlen : (v :: vs).length < 2 * majority (v :: vs).length :=
    two_majority_gt_length _
  have hsum : overlapCount (v :: vs) a + overlapCount (v :: vs) b ≥
    2 * majority (v :: vs).length := by omega
  have hincl := overlapCount_incl_excl (v :: vs) a b
  have hunion : unionCount (v :: vs) a b ≤ (v :: vs).length :=
    overlapUnion_le_length (v :: vs) a b
  omega

/-- HQ14: **Quorum Safety Property**: Any two quorums of the same non-empty voter list share
    at least one voter in common (measured by intersection count ≥ 1).

    This is the core safety property of majority quorums underlying Raft consensus:
    no two disjoint sets can simultaneously form a quorum for the same voter configuration. -/
theorem quorum_intersection (v : Nat) (vs : List Nat) (a b : Nat → Bool)
    (ha : hasQuorum (v :: vs) a = true) (hb : hasQuorum (v :: vs) b = true) :
    intersectCount (v :: vs) a b ≥ 1 := by
  rw [hasQuorum_iff_overlap] at ha hb
  simp only [List.cons_ne_nil, false_or] at ha hb
  exact overlapIntersect_lb v vs a b ha hb

/-! ## Singleton cases -/

/-- HQ15: A singleton voter list satisfies quorum iff the sole voter is in the set. -/
theorem hasQuorum_singleton_self (v : Nat) (s : Nat → Bool) (h : s v = true) :
    hasQuorum [v] s = true := by
  simp only [hasQuorum_cons_def, decide_eq_true_eq, overlapCount_cons, overlapCount,
    Nat.add_zero, List.length_cons, List.length_nil, majority, h, if_true]
  omega

/-- HQ16: A singleton voter list does not satisfy quorum if the voter is absent. -/
theorem hasQuorum_singleton_absent (v : Nat) (s : Nat → Bool) (h : s v = false) :
    hasQuorum [v] s = false := by
  have hoc : overlapCount [v] s = 0 :=
    overlapCount_none_in [v] s (fun w hw => by simp at hw; rw [hw]; exact h)
  rw [hasQuorum_cons_def, hoc, decide_eq_false_iff_not]
  simp [majority]

/-- HQ17: The predicate that is true for all voters always forms a quorum (non-empty case). -/
theorem hasQuorum_all_voters (v : Nat) (vs : List Nat) :
    hasQuorum (v :: vs) (fun _ => true) = true :=
  hasQuorum_true_of_all_in (v :: vs) (fun _ => true) (fun _ _ => rfl)

/-! ## Append decomposition -/

/-- HQ18: overlapCount distributes over list append. -/
theorem overlapCount_append (l1 l2 : List Nat) (s : Nat → Bool) :
    overlapCount (l1 ++ l2) s = overlapCount l1 s + overlapCount l2 s := by
  induction l1 with
  | nil => simp [overlapCount]
  | cons v vs ih =>
    simp only [List.cons_append, overlapCount_cons, ih]
    omega

/-! ## Quorum non-emptiness and concrete witness -/

/-- HQ19: Positive overlap count implies existence of a concrete member in the set. -/
theorem overlapCount_pos_mem (voters : List Nat) (s : Nat → Bool)
    (h : overlapCount voters s ≥ 1) : ∃ v ∈ voters, s v = true := by
  induction voters with
  | nil => simp [overlapCount] at h
  | cons v vs ih =>
    simp only [overlapCount_cons] at h
    by_cases hv : s v
    · exact ⟨v, List.mem_cons.mpr (Or.inl rfl), hv⟩
    · simp [hv] at h
      obtain ⟨w, hw, hs⟩ := ih h
      exact ⟨w, List.mem_cons.mpr (Or.inr hw), hs⟩

/-- HQ20: **Concrete Quorum Safety**: if two predicates both form quorums of a non-empty
    voter list, there exists a concrete voter ID that is a member of both sets.

    This is the fully constructive version of HQ14 — it produces an explicit witness
    for the shared voter, confirming that consensus requires at least one node that
    participates in both quorums. -/
theorem quorum_intersection_mem (v : Nat) (vs : List Nat) (a b : Nat → Bool)
    (ha : hasQuorum (v :: vs) a = true) (hb : hasQuorum (v :: vs) b = true) :
    ∃ w ∈ (v :: vs), a w = true ∧ b w = true := by
  have hge : intersectCount (v :: vs) a b ≥ 1 :=
    quorum_intersection v vs a b ha hb
  obtain ⟨w, hmem, hsw⟩ :=
    overlapCount_pos_mem (v :: vs) (fun x => a x && b x) hge
  simp only [Bool.and_eq_true] at hsw
  exact ⟨w, hmem, hsw.1, hsw.2⟩
