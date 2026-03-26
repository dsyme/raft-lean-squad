/-!
# Formal Specification: `limit_size`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises the `limit_size` function from `src/util.rs`.

## What `limit_size` does

```rust
pub fn limit_size<T: PbMessage>(entries: &mut Vec<T>, max: Option<u64>)
```

Truncates `entries` in-place so the total serialised byte-size of retained entries
stays within `max`.  **Always keeps at least the first entry** regardless of size.
No-ops when `max` is `None` or `NO_LIMIT = u64::MAX`.

Rust algorithm (src/util.rs):
1. Return unchanged if `entries.len() ≤ 1`.
2. Return unchanged if `max` is `None` or `u64::MAX`.
3. Scan with `take_while`: always keep the first element (when `size == 0` in the
   accumulator, unconditionally return `true`); keep further elements while the
   running total does not exceed `max`.
4. Truncate to the count produced by that scan.

## Modelling choices

- Type `T` with `compute_size()` is abstracted to type `α` with `size : α → Nat`.
- Rust `Vec` mutation is replaced by a pure function returning the new list.
- `u64` is replaced by unbounded `Nat` (overflow not modelled — precondition).
- `NO_LIMIT` / `None` are unified as `Option.none`.
-/

/-! ## Size helper -/

/-- Sum of the sizes of all elements in a list. -/
def totalSize {α : Type} (size : α → Nat) : List α → Nat
  | []      => 0
  | e :: es => size e + totalSize size es

@[simp] theorem totalSize_nil {α : Type} (size : α → Nat) :
    totalSize size [] = 0 := rfl

@[simp] theorem totalSize_cons {α : Type} (size : α → Nat) (e : α) (es : List α) :
    totalSize size (e :: es) = size e + totalSize size es := rfl

/-- Total size of a prefix is at most total size of the full list. -/
theorem totalSize_take_le {α : Type} (size : α → Nat) (l : List α) (k : Nat) :
    totalSize size (l.take k) ≤ totalSize size l := by
  induction l generalizing k with
  | nil => simp
  | cons e es ih =>
    cases k with
    | zero => simp [totalSize]
    | succ n =>
      simp [List.take_succ_cons, totalSize]
      exact ih n

/-! ## Functional model -/

/-- Count how many entries to keep.
    Mirrors the Rust `take_while` scan with the "always keep the first" rule.
    Parameters: `size` function, `budget`, remaining entries, current count `k`,
    cumulative size so far `cum`. -/
def limitSizeCount {α : Type} (size : α → Nat) (budget : Nat) :
    List α → Nat → Nat → Nat
  | [],      k, _   => k
  | e :: es, k, cum =>
    let cum' := cum + size e
    if k == 0 then
      -- First element: always include (mirrors `if size == 0 { return true }` in Rust)
      limitSizeCount size budget es 1 cum'
    else if cum' > budget then
      k   -- stop here
    else
      limitSizeCount size budget es (k + 1) cum'

/-- The pure functional model of `limit_size`.
    Returns the longest head-prefix of `entries` satisfying the size budget,
    always keeping at least 1 element when the input is non-empty.
    Matches `Option.none` for the unlimited case (covers both `None` and `NO_LIMIT`). -/
def limitSize {α : Type} (size : α → Nat) (entries : List α) (max : Option Nat) :
    List α :=
  match max with
  | none        => entries
  | some budget =>
    if entries.length ≤ 1 then entries
    else entries.take (limitSizeCount size budget entries 0 0)

/-! ## Evaluations (sanity-check against src/util.rs doctest) -/

section Eval

-- Entries are Nat values used as their own size (via `id`).
private def e5 : List Nat := [100, 100, 100, 100, 100]

#eval limitSize id e5 (some 220)   -- [100, 100]  ← 2 entries fit in 220
#eval limitSize id e5 (some 0)     -- [100]        ← budget 0, but keep 1
#eval limitSize id e5 none         -- [100, 100, 100, 100, 100] ← no limit
#eval limitSize id e5 (some 500)   -- [100, 100, 100, 100, 100] ← all fit
#eval limitSize id e5 (some 100)   -- [100]        ← exactly 1 fits (2nd would be 200)
#eval limitSize id e5 (some 99)    -- [100]        ← first kept even over budget
#eval limitSize id ([] : List Nat) (some 100)  -- []
#eval limitSize id [42] (some 0)               -- [42]

end Eval

/-! ## Key monotonicity lemma for `limitSizeCount` -/

/-- `limitSizeCount` called with a non-empty list always returns at least 1. -/
theorem limitSizeCount_pos {α : Type} (size : α → Nat) (budget : Nat)
    (e : α) (es : List α) :
    1 ≤ limitSizeCount size budget (e :: es) 0 0 := by
  simp only [limitSizeCount]
  -- After the `if k == 0` branch, we recurse with k = 1.
  -- We need to show the recursive result is ≥ 1.
  sorry

/-- `limitSizeCount` never returns more than the list's length. -/
theorem limitSizeCount_le_length {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (k cum : Nat) (hk : k ≤ entries.length) :
    limitSizeCount size budget entries k cum ≤ entries.length := by
  sorry

/-! ## Specification theorems -/

section Spec

variable {α : Type} (size : α → Nat)

/-! ### P1: Result is a prefix of the input -/

theorem limitSize_is_prefix (entries : List α) (max : Option Nat) :
    limitSize size entries max <+: entries := by
  simp only [limitSize]
  split
  · exact List.prefix_refl entries
  · split
    · exact List.prefix_refl entries
    · exact List.take_prefix _ _

/-! ### P2: Non-empty input is never fully emptied -/

theorem limitSize_nonempty (entries : List α) (max : Option Nat)
    (hne : entries ≠ []) : limitSize size entries max ≠ [] := by
  simp only [limitSize]
  split
  · exact hne
  · split
    · exact hne
    · -- The take returns a non-empty list because limitSizeCount returns ≥ 1
      -- (see limitSizeCount_pos). Full proof in Task 5.
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h1 | h2
      · -- limitSizeCount returned 0, but limitSizeCount_pos says it is ≥ 1
        exact absurd h1 (by
          cases entries with
          | nil => exact absurd rfl hne
          | cons e es => exact Nat.ne_of_gt (limitSizeCount_pos size _ e es))
      · exact hne h2

/-! ### P3: No-op when `max = none` -/

@[simp]
theorem limitSize_none (entries : List α) :
    limitSize size entries none = entries := rfl

/-! ### P4: No-op when input has ≤ 1 elements -/

theorem limitSize_le_one (entries : List α) (hlen : entries.length ≤ 1)
    (max : Option Nat) : limitSize size entries max = entries := by
  simp only [limitSize]
  split
  · rfl
  · simp [hlen]

/-! ### P5: No-op on empty list -/

@[simp]
theorem limitSize_nil (max : Option Nat) :
    limitSize size ([] : List α) max = [] :=
  limitSize_le_one size [] (by simp) max

/-! ### P6: No-op on singleton -/

@[simp]
theorem limitSize_singleton (e : α) (max : Option Nat) :
    limitSize size [e] max = [e] :=
  limitSize_le_one size [e] (by simp) max

/-! ### P7: Result length ≤ original length -/

theorem limitSize_length_le (entries : List α) (max : Option Nat) :
    (limitSize size entries max).length ≤ entries.length :=
  (limitSize_is_prefix size entries max).length_le

/-! ### P8: Result length ≥ 1 when input is non-empty -/

theorem limitSize_length_pos (entries : List α) (hne : entries ≠ [])
    (max : Option Nat) : 0 < (limitSize size entries max).length :=
  List.ne_nil_iff_length_pos.mp (limitSize_nonempty size entries max hne)

/-! ### P9: Size bound
    When the result has > 1 entry, the total size fits within the budget. -/

theorem limitSize_size_bound (entries : List α) (budget : Nat) :
    (limitSize size entries (some budget)).length = 1 ∨
    totalSize size (limitSize size entries (some budget)) ≤ budget := by
  sorry

/-! ### P10: Maximality
    If the result has k < original-length entries, adding one more would exceed
    the budget. -/

theorem limitSize_maximality (entries : List α) (budget : Nat)
    (hlt : (limitSize size entries (some budget)).length < entries.length) :
    budget < totalSize size
      (entries.take ((limitSize size entries (some budget)).length + 1)) := by
  sorry

/-! ### P11: Idempotence — a second application is a no-op. -/

theorem limitSize_idempotent (entries : List α) (max : Option Nat) :
    limitSize size (limitSize size entries max) max =
    limitSize size entries max := by
  sorry

/-! ### P12: Prefix of original is prefix of result (monotone truncation).
    Equivalently: the result is determined by a contiguous head-prefix of the input. -/

theorem limitSize_prefix_of_prefix (entries : List α) (max : Option Nat)
    (k : Nat) (hk : k ≤ (limitSize size entries max).length) :
    limitSize size (entries.take k) max = entries.take k := by
  -- entries.take k has length ≤ k ≤ (limitSize ...).length ≤ entries.length
  apply limitSize_le_one
  simp only [List.length_take]
  have hle := limitSize_length_le size entries max
  sorry

end Spec
