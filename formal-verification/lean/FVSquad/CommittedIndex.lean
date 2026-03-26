import FVSquad.MajorityVote

/-!
# CommittedIndex — Lean 4 Specification and Implementation Model

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Formal specification and implementation model of
`Configuration::committed_index` from `src/quorum/majority.rs`
(non-group-commit path).  This is one of the most safety-critical
computations in Raft: it determines the largest log index that has
been acknowledged by a majority of voters and may therefore be safely
committed.

## Algorithm

1. Collect `acked_index(v)` for every voter `v` (defaulting unknown to `0`).
2. Sort the collected indices in **descending** order.
3. Return the element at position `majority(n) − 1` (0-indexed), where
   `majority(n) = n / 2 + 1`.

Example: acked indices `[2, 2, 2, 4, 5]` sorted desc = `[5, 4, 2, 2, 2]`;
`majority(5) = 3`; result = `sorted[2] = 2`.

## Model scope and approximations

* **Non-group-commit path only**: the `use_group_commit = true` branch is not
  modelled here (requires extra group-ID bookkeeping).
* **Types**: voter IDs are `Nat` (Rust: `u64`).  Acked log indices are `Nat`.
* **`AckedFn`**: models `impl AckedIndexer` as a pure `Nat → Nat` function;
  `None` (unknown voters) is mapped to `0` via Rust's `unwrap_or_default()`.
* **Empty-config return value**: Rust returns `u64::MAX` so that
  `min(empty_result, other) = other` in joint quorums.  This model returns `0`
  to stay in `Nat`; the divergence is captured in `committedIndex_empty_contract`.
* **Voter list vs. set**: Rust uses a `HashSet<u64>`; this model uses `List Nat`
  (duplicates assumed absent where it matters).
* **Stack/heap allocation**: the Rust unsafe stack-array optimisation is a
  performance detail only; this model uses `List` throughout.
* **Omitted**: group-commit extension, concurrency, I/O, `AckedIndexer` trait
  dispatch, Rust `u64` overflow semantics, memory layout.
-/

namespace FVSquad.CommittedIndex

/-! ## Core types and helpers -/

/-- Models `impl AckedIndexer`: a pure function from voter ID to acknowledged index.
    `None` results in Rust are mapped to `0` via `unwrap_or_default()`. -/
abbrev AckedFn := Nat → Nat

/-- Sort a list of natural numbers in **descending** order.
    Mirrors the `matched.sort_by(|a, b| b.index.cmp(&a.index))` call in Rust. -/
def sortDesc (l : List Nat) : List Nat :=
  l.mergeSort (fun a b => decide (a ≥ b))

/-- `sortDesc` preserves the length. -/
theorem sortDesc_length (l : List Nat) : (sortDesc l).length = l.length :=
  List.length_mergeSort l

/-- `sortDesc` is a permutation of the input. -/
theorem sortDesc_perm (l : List Nat) : (sortDesc l).Perm l :=
  List.mergeSort_perm l (fun a b => decide (a ≥ b))

/-- The `(· ≥ ·)` predicate used by `sortDesc` is transitive. -/
private theorem ge_trans' (a b c : Nat) (h1 : decide (a ≥ b) = true) (h2 : decide (b ≥ c) = true) :
    decide (a ≥ c) = true := by
  simp [decide_eq_true_eq] at *; omega

/-- The `(· ≥ ·)` predicate used by `sortDesc` is total. -/
private theorem ge_total' (a b : Nat) : (decide (a ≥ b) || decide (b ≥ a)) = true := by
  simp [Bool.or_eq_true, decide_eq_true_eq]; omega

/-- `sortDesc` produces a **descending** (non-increasing) list. -/
theorem sortDesc_pairwise (l : List Nat) :
    (sortDesc l).Pairwise (fun a b => decide (a ≥ b) = true) :=
  List.pairwise_mergeSort ge_trans' ge_total' l

/-- The acked indices for all voters, sorted descending. -/
def sortedAcked (voters : List Nat) (acked : AckedFn) : List Nat :=
  sortDesc (voters.map acked)

/-- Length of `sortedAcked` equals the voter count. -/
theorem sortedAcked_length (voters : List Nat) (acked : AckedFn) :
    (sortedAcked voters acked).length = voters.length := by
  simp [sortedAcked, sortDesc_length, List.length_map]

/-! ## Implementation model: `committedIndex` -/

/-- **Implementation model** of `Configuration::committed_index` (non-group-commit path).

    For non-empty voter sets: sorts all acked indices descending and returns
    the element at position `majority(n) - 1` (0-indexed).

    For the empty voter set: returns `0`.  **This diverges from Rust** (which
    returns `u64::MAX` as a sentinel for joint quorums); see
    `committedIndex_empty_contract` below. -/
def committedIndex (voters : List Nat) (acked : AckedFn) : Nat :=
  (sortedAcked voters acked).getD (majority voters.length - 1) 0

/-! ## Declarative characterisation via `countGe`

    An equivalent characterisation of `committedIndex` is:
    `committedIndex = max { k | countGe voters acked k ≥ majority(n) }`.
    This form is more convenient for stating safety and maximality. -/

/-- Number of voters whose acked index is **at least** `k`. -/
def countGe (voters : List Nat) (acked : AckedFn) (k : Nat) : Nat :=
  (voters.filter (fun v => decide (k ≤ acked v))).length

/-! ## Evaluations -/

section Eval
-- Five voters with acked indices [5,3,3,2,2]; majority(5)=3; result=3.
#eval committedIndex [1,2,3,4,5] (fun v => match v with
  | 1 => 5 | 2 => 3 | 3 => 3 | 4 => 2 | _ => 2)  -- expected 3

-- Three voters with acked indices [2,2,2]; majority(3)=2; result=2.
#eval committedIndex [1,2,3] (fun _ => 2)             -- expected 2

-- Single voter with acked index 7; result=7.
#eval committedIndex [1] (fun _ => 7)                 -- expected 7

-- Empty config; result=0 (Rust returns u64::MAX).
#eval committedIndex [] (fun _ => 42)                 -- expected 0
end Eval

/-! ## Proved theorems -/

/-- **CI1** — Empty configuration returns `0`. -/
theorem committedIndex_empty (acked : AckedFn) : committedIndex [] acked = 0 := by
  simp [committedIndex, sortedAcked, sortDesc, majority]

/-- **CI1-contract** — Documents the divergence from Rust's `u64::MAX` sentinel.
    Proofs involving joint quorums should use `min(committedIndex ..., ...)` and
    treat the empty case separately, corresponding to Rust's `min(u64::MAX, x) = x`. -/
theorem committedIndex_empty_contract (acked : AckedFn) :
    committedIndex [] acked = 0 := committedIndex_empty acked

/-- **CI2** — Single voter returns that voter's acked index. -/
theorem committedIndex_singleton (v : Nat) (acked : AckedFn) :
    committedIndex [v] acked = acked v := by
  simp [committedIndex, sortedAcked, sortDesc, majority]

/-- **CI3** — `countGe voters acked 0 = voters.length` (all natural numbers are ≥ 0). -/
theorem countGe_zero (voters : List Nat) (acked : AckedFn) :
    countGe voters acked 0 = voters.length := by
  simp [countGe]

/-- **CI4** — Antitone: raising the threshold `k` cannot increase `countGe`. -/
theorem filter_ge_sublist (voters : List Nat) (acked : AckedFn) (j k : Nat) (hjk : j ≤ k) :
    (voters.filter (fun v => decide (k ≤ acked v))).Sublist
    (voters.filter (fun v => decide (j ≤ acked v))) := by
  induction voters with
  | nil => simp
  | cons v vs ih =>
    simp only [List.filter]
    by_cases hk : decide (k ≤ acked v) = true
    · have hj : decide (j ≤ acked v) = true := by
        simp [decide_eq_true_eq] at hk ⊢; omega
      simp only [hk, hj]
      exact List.Sublist.cons₂ v ih
    · simp only [Bool.not_eq_true] at hk
      simp only [hk]
      by_cases hj : decide (j ≤ acked v) = true
      · simp only [hj]; exact List.Sublist.cons v ih
      · simp only [Bool.not_eq_true] at hj
        simp only [hj]; exact ih

theorem countGe_antitone (voters : List Nat) (acked : AckedFn) (j k : Nat) (hjk : j ≤ k) :
    countGe voters acked k ≤ countGe voters acked j :=
  List.Sublist.length_le (filter_ge_sublist voters acked j k hjk)

/-- **CI5** — `countGe` is preserved by voter list permutations. -/
theorem countGe_perm (voters1 voters2 : List Nat) (acked : AckedFn) (k : Nat)
    (hperm : voters1.Perm voters2) :
    countGe voters1 acked k = countGe voters2 acked k := by
  simp only [countGe]
  exact List.Perm.length_eq (hperm.filter _)

/-- **CI6** — `sortedAcked` is a permutation of `voters.map acked`. -/
theorem sortedAcked_perm (voters : List Nat) (acked : AckedFn) :
    (sortedAcked voters acked).Perm (voters.map acked) :=
  sortDesc_perm _

/-- **CI7** — `countGe` equals the count of elements ≥ `k` in the mapped acked list.
    Key bridge: filtering voters by `acked v ≥ k` gives the same count as
    filtering mapped values by `x ≥ k`. -/
theorem countGe_eq_countGeList (voters : List Nat) (acked : AckedFn) (k : Nat) :
    countGe voters acked k =
    ((voters.map acked).filter (fun x => decide (k ≤ x))).length := by
  simp only [countGe, List.filter_map, List.length_map]
  rfl

/-- **CI8** — `committedIndex` is 0 when all acked indices are 0. -/
theorem committedIndex_all_zero (voters : List Nat) :
    committedIndex voters (fun _ => 0) = 0 := by
  simp [committedIndex, sortedAcked, sortDesc, majority]
  -- sortDesc of an all-zeros map is all-zeros; getD ... 0 = 0
  sorry

/-! ## Sorry-guarded theorems (require order-statistic reasoning) -/

/-- **CI-Safety** (sorry): at least `majority n` voters have acked ≥ `committedIndex`.

    Proof sketch:
    - `sortedAcked voters acked` is a descending-sorted list of acked values.
    - Its length is `n = voters.length` (`sortedAcked_length`).
    - `committedIndex` is the element at position `majority(n) - 1` (0-indexed).
    - By the descending sort, all elements at positions 0..majority(n)-1 are ≥ this value.
    - There are `majority(n)` such positions (when n > 0).
    - By `countGe_eq_countGeList` and `countGe_perm`, these correspond to voters.
    - Therefore `countGe voters acked (committedIndex voters acked) ≥ majority(n)`.

    Formalisation requires: list order-statistic lemmas (`l.Pairwise (· ≥ ·) →
    i < j → l[j] ≤ l[i]`) and a count-prefix lemma for sorted lists. -/
theorem committedIndex_safety (voters : List Nat) (acked : AckedFn)
    (hn : 0 < voters.length) :
    majority voters.length ≤ countGe voters acked (committedIndex voters acked) := by
  sorry

/-- **CI-Maximality** (sorry): `committedIndex` is the largest such value.

    Any `k > committedIndex voters acked` has fewer than `majority(n)` acked voters.

    Proof sketch: the element at position `majority(n)` in the sorted list
    (if it exists) is strictly less than the one at `majority(n)-1`.
    When `k` exceeds `committedIndex`, `countGe` drops below the majority
    threshold. -/
theorem committedIndex_maximality (voters : List Nat) (acked : AckedFn)
    (k : Nat) (hk : committedIndex voters acked < k) :
    countGe voters acked k < majority voters.length := by
  sorry

/-- **CI-Monotonicity** (sorry): committing never regresses when every voter's
    acked index is non-decreasing.

    If `acked1 v ≤ acked2 v` for all `v`, then
    `committedIndex voters acked1 ≤ committedIndex voters acked2`.

    Proof sketch: each element of `sortedAcked voters acked2` is ≥ the
    corresponding element of `sortedAcked voters acked1` (pointwise ordering
    on sorted lists). -/
theorem committedIndex_mono (voters : List Nat) (acked1 acked2 : AckedFn)
    (hle : ∀ v, acked1 v ≤ acked2 v) :
    committedIndex voters acked1 ≤ committedIndex voters acked2 := by
  sorry

end FVSquad.CommittedIndex
