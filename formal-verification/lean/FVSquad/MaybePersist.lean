/-!
# MaybePersist — Model and Proofs for `RaftLog::maybe_persist`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Formalises `RaftLog::maybe_persist` and `RaftLog::maybe_persist_snap`
from `src/raft_log.rs` (lines 545–610).

## Background

In the async-persist flow, a Raft node hands a batch of log entries to storage,
and when storage confirms completion it calls `maybe_persist(index, term)`.
Because leadership changes can happen concurrently, the log state may have changed
since the batch was sent.  Three guards prevent advancing the `persisted` index to a
stale position:

1. `index > persisted`  — no regression
2. `index < firstUpdateIndex`  — below the start of any not-yet-confirmed unstable batch
3. `logTerm index = term`  — term still matches (guards against truncate+re-insert)

## Model

We abstract the relevant state as:
- `persisted : Nat`
- `firstUpdateIndex : Nat`  (derived from `unstable.snapshot?.index` or `unstable.offset`)
- `logTerm : Nat → Nat`  (infallible; storage errors are abstracted away)

Omissions documented:
- `Unstable` internals (only `firstUpdateIndex` matters here)
- Storage error paths (`is_ok_and` → direct equality)
- Logger / debug output

## What This File Provides

| ID  | Name                               | Status    | Description |
|-----|------------------------------------|-----------|-------------|
| MP1 | `maybePersist_true_iff`            | ✅ proved | Returns `true` ↔ all three guards hold |
| MP2 | `maybePersist_monotone`            | ✅ proved | `persisted` never decreases |
| MP3 | `maybePersist_true_advances`       | ✅ proved | Returns `true` → new persisted = `index` |
| MP4 | `maybePersist_false_unchanged`     | ✅ proved | Returns `false` → persisted unchanged |
| MP5 | `maybePersist_true_gt`             | ✅ proved | Returns `true` → new persisted > old persisted |
| MP6 | `maybePersist_true_lt_fui`         | ✅ proved | Returns `true` → new persisted < `firstUpdateIndex` |
| MP7 | `maybePersist_true_term`           | ✅ proved | Returns `true` → `logTerm(new persisted) = term` |
| MP8 | `maybePersist_idempotent`          | ✅ proved | Calling again with the same args → `false` |
| SP1 | `maybePersistSnap_true_iff`        | ✅ proved | Snap variant: returns `true` ↔ `index > persisted` |
| SP2 | `maybePersistSnap_monotone`        | ✅ proved | Snap variant: monotone |
| SP3 | `maybePersistSnap_true_advances`   | ✅ proved | Snap variant: returns `true` → new persisted = `index` |
| SP4 | `maybePersistSnap_false_unchanged` | ✅ proved | Snap variant: returns `false` → persisted unchanged |

**Sorry count**: 0.  All theorems proved without `sorry`.

-/

namespace FVSquad.MaybePersist

-- ---------------------------------------------------------------------------
-- Implementation models
-- ---------------------------------------------------------------------------

/--
`maybePersist persisted firstUpdateIndex logTerm index term` returns `(newPersisted, advanced)`.

Models `RaftLog::maybe_persist`:
```rust
if index > persisted && index < firstUpdateIndex && store.term(index).is_ok_and(|t| t == term) {
    persisted = index; true
} else { false }
```
-/
def maybePersist (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) : Nat × Bool :=
  if index > persisted ∧ index < firstUpdateIndex ∧ logTerm index = term then
    (index, true)
  else
    (persisted, false)

/--
`maybePersistSnap persisted index` returns `(newPersisted, advanced)`.

Models `RaftLog::maybe_persist_snap` (success path only; fatal branches are omitted):
```rust
if index > persisted { persisted = index; true } else { false }
```
-/
def maybePersistSnap (persisted index : Nat) : Nat × Bool :=
  if index > persisted then
    (index, true)
  else
    (persisted, false)

-- ---------------------------------------------------------------------------
-- Helper abbreviations
-- ---------------------------------------------------------------------------

/-- The three guards required by `maybe_persist`. -/
def guardsHold (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) : Prop :=
  index > persisted ∧ index < firstUpdateIndex ∧ logTerm index = term

-- ---------------------------------------------------------------------------
-- Theorems for `maybePersist`
-- ---------------------------------------------------------------------------

/-- **MP1**: `maybePersist` returns `true` iff all three guards hold. -/
theorem maybePersist_true_iff (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    (maybePersist persisted firstUpdateIndex logTerm index term).2 = true ↔
    guardsHold persisted firstUpdateIndex logTerm index term := by
  simp only [maybePersist, guardsHold]
  by_cases h : index > persisted ∧ index < firstUpdateIndex ∧ logTerm index = term
  · simp [h]
  · simp [h]

/-- **MP2**: `persisted` never decreases. -/
theorem maybePersist_monotone (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    persisted ≤ (maybePersist persisted firstUpdateIndex logTerm index term).1 := by
  simp only [maybePersist]
  split
  · next h => omega
  · omega

/-- **MP3**: Returns `true` → new persisted = `index`. -/
theorem maybePersist_true_advances (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    (maybePersist persisted firstUpdateIndex logTerm index term).2 = true →
    (maybePersist persisted firstUpdateIndex logTerm index term).1 = index := by
  simp only [maybePersist]
  split
  · intro; rfl
  · intro h; simp at h

/-- **MP4**: Returns `false` → persisted unchanged. -/
theorem maybePersist_false_unchanged (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    (maybePersist persisted firstUpdateIndex logTerm index term).2 = false →
    (maybePersist persisted firstUpdateIndex logTerm index term).1 = persisted := by
  simp only [maybePersist]
  split
  · intro h; simp at h
  · intro; rfl

/-- **MP5**: Returns `true` → new persisted > old persisted. -/
theorem maybePersist_true_gt (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    (maybePersist persisted firstUpdateIndex logTerm index term).2 = true →
    (maybePersist persisted firstUpdateIndex logTerm index term).1 > persisted := by
  simp only [maybePersist]
  split
  · next h => intro; omega
  · intro h; simp at h

/-- **MP6**: Returns `true` → new persisted < `firstUpdateIndex`. -/
theorem maybePersist_true_lt_fui (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    (maybePersist persisted firstUpdateIndex logTerm index term).2 = true →
    (maybePersist persisted firstUpdateIndex logTerm index term).1 < firstUpdateIndex := by
  simp only [maybePersist]
  split
  · next h => intro; exact h.2.1
  · intro h; simp at h

/-- **MP7**: Returns `true` → `logTerm` at new persisted equals `term`. -/
theorem maybePersist_true_term (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    (maybePersist persisted firstUpdateIndex logTerm index term).2 = true →
    logTerm (maybePersist persisted firstUpdateIndex logTerm index term).1 = term := by
  simp only [maybePersist]
  split
  · next h => intro; exact h.2.2
  · intro h; simp at h

/-- **MP8**: After a successful call, calling again with the same args returns `false`
(idempotent: we cannot advance the same index twice). -/
theorem maybePersist_idempotent (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term : Nat) :
    let s := maybePersist persisted firstUpdateIndex logTerm index term
    (maybePersist s.1 firstUpdateIndex logTerm index term).2 = false := by
  simp only [maybePersist]
  by_cases h : index > persisted ∧ index < firstUpdateIndex ∧ logTerm index = term
  · simp only [if_pos h]
    simp only [if_neg (by omega : ¬(index > index ∧ index < firstUpdateIndex ∧ logTerm index = term))]
  · simp only [if_neg h]

-- ---------------------------------------------------------------------------
-- Theorems for `maybePersistSnap`
-- ---------------------------------------------------------------------------

/-- **SP1**: Snap variant: returns `true` iff `index > persisted`. -/
theorem maybePersistSnap_true_iff (persisted index : Nat) :
    (maybePersistSnap persisted index).2 = true ↔ index > persisted := by
  simp only [maybePersistSnap]
  split
  · next h => simp; omega
  · next h => simp; omega

/-- **SP2**: Snap variant: `persisted` never decreases. -/
theorem maybePersistSnap_monotone (persisted index : Nat) :
    persisted ≤ (maybePersistSnap persisted index).1 := by
  simp only [maybePersistSnap]
  split
  · next h => omega
  · omega

/-- **SP3**: Snap variant: returns `true` → new persisted = `index`. -/
theorem maybePersistSnap_true_advances (persisted index : Nat) :
    (maybePersistSnap persisted index).2 = true →
    (maybePersistSnap persisted index).1 = index := by
  simp only [maybePersistSnap]
  split
  · intro; rfl
  · intro h; simp at h

/-- **SP4**: Snap variant: returns `false` → persisted unchanged. -/
theorem maybePersistSnap_false_unchanged (persisted index : Nat) :
    (maybePersistSnap persisted index).2 = false →
    (maybePersistSnap persisted index).1 = persisted := by
  simp only [maybePersistSnap]
  split
  · intro h; simp at h
  · intro; rfl

-- ---------------------------------------------------------------------------
-- Cross-property: maybePersist and maybePersistSnap both monotone
-- ---------------------------------------------------------------------------

/-- Applying `maybePersist` then `maybePersistSnap` with the same persisted bound:
    the final persisted ≥ initial persisted. -/
theorem compose_monotone (persisted firstUpdateIndex : Nat) (logTerm : Nat → Nat)
    (index term snapIndex : Nat) :
    let s1 := maybePersist persisted firstUpdateIndex logTerm index term
    let s2 := maybePersistSnap s1.1 snapIndex
    persisted ≤ s2.1 := by
  simp only [maybePersist, maybePersistSnap]
  split <;> split <;> omega

end FVSquad.MaybePersist
