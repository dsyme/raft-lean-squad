# Informal Specification — `RaftLog::append`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**File**: `src/raft_log.rs`  
**Function**: `pub fn append(&mut self, ents: &[Entry]) -> u64`

---

## Purpose

`RaftLog::append` is the **leader-side log append gate**.  It writes a batch of
new entries into the unstable portion of the log, potentially truncating any
conflicting unstable entries that follow the insertion point.  It returns the new
`last_index` after the append.

This function acts as a safety gate: it **panics** (via `fatal!`) if the caller
tries to truncate entries that have already been committed, which would violate the
Raft safety property that committed log entries are never lost.

---

## Rust source (paraphrased)

```rust
pub fn append(&mut self, ents: &[Entry]) -> u64 {
    if ents.is_empty() { return self.last_index(); }
    let after = ents[0].index - 1;         // index just before the new entries
    if after < self.committed { fatal!() }  // safety gate
    self.unstable.truncate_and_append(ents);
    self.last_index()
}
```

---

## Preconditions

1. **`ents` is well-formed**: if non-empty, `ents[0].index ≥ 1` (indices are
   1-based in Raft), and entries are contiguous: `ents[i].index = ents[0].index + i`.
2. **Safety gate**: `ents[0].index - 1 ≥ committed` — the insertion point is at or
   after the last committed index.  Violating this causes a fatal panic (modelled as
   an `assume` / precondition violation).
3. The log state is well-formed before the call:
   `first_index ≤ committed ≤ last_index`.

---

## Postconditions

### If `ents` is empty
- Returns `last_index` unchanged.
- The log state is completely unchanged.

### If `ents` is non-empty (let `after = ents[0].index - 1`)
1. **Return value**: returns `ents.last().index` = `ents[0].index + ents.len() - 1`.
2. **New last_index**: equals the return value.
3. **Committed unchanged**: `committed` is not modified.
4. **First_index unchanged**: `first_index` is not modified.
5. **Entries after `after` are replaced**: `unstable.truncate_and_append` removes any
   existing unstable entries with `index > after` and appends `ents`.
6. **Log is well-formed after**: `first_index ≤ committed ≤ new_last_index`.
7. **Safety invariant preserved**: `committed ≤ new_last_index` (since
   `after ≥ committed` implies `ents[0].index - 1 ≥ committed`, so
   `ents[0].index ≥ committed + 1 ≤ new_last_index`).

---

## Invariants

The following properties always hold after `append`:

- `committed ≤ last_index` — committed never exceeds the log.
- `first_index ≤ committed` — first index precedes committed.
- No committed entry is truncated: for all `i ≤ committed`, the entry at index `i`
  is the same before and after the call (because `after ≥ committed` means we only
  truncate entries with index `> after ≥ committed`).

---

## Edge cases

| Scenario | Behaviour |
|----------|-----------|
| `ents.is_empty()` | No-op; returns current `last_index`. |
| `after == committed` | Allowed; new entries start exactly at `committed + 1`. |
| `after > last_index` | Would leave a gap — **not allowed** by Raft invariants (callers must not do this); not guarded here. |
| `after < first_index` | Replaces the entire unstable portion (handled inside `truncate_and_append`). |
| `ents` entirely in unstable range | Partial replacement of unstable entries. |
| Single-entry `ents` | `new_last_index = ents[0].index`. |

---

## Examples

```
State: first=1, committed=5, last=8, unstable_offset=7, unstable=[e7, e8]
Call:  append([e9])        -- after = 8 = last_index
Result: new last=9, unstable=[e7, e8, e9], committed=5 (unchanged)

State: first=1, committed=5, last=8
Call:  append([e7, e8, e9])  -- after = 6 ≥ committed=5
Result: new last=9, unstable entries for [7,9] are replaced, committed=5

State: first=1, committed=5, last=8
Call:  append([e5])        -- after = 4 < committed=5  ← PANIC (fatal!)
Result: process crashes
```

---

## Key property to verify

> **Safety gate correctness**: `after ≥ committed` is a *sufficient* condition to
> guarantee that no committed entry is truncated.
>
> Formally: for all `i ≤ committed`, the entry at index `i` in `new_log` equals the
> entry at index `i` in `old_log`.

This follows because `truncate_and_append` only modifies entries with index `≥ after + 1 = ents[0].index ≥ committed + 1`, which are all *above* the committed index.

---

## Inferred intent / open questions

- **Is `after > last_index` (gap creation) checked?** The current code does not check
  for gaps between `last_index` and `ents[0].index - 1`.  Callers are expected to
  maintain this invariant.  An open question for maintainers: should `append` assert
  `after ≤ last_index`?

- **What if `ents` indices are non-contiguous?** `truncate_and_append` does not
  validate entry contiguity; callers must provide valid sequences.

---

## Lean verification plan

**Lean file**: `formal-verification/lean/FVSquad/RaftLogAppend.lean`  
**Phase**: 2 → 3 (informal spec written; Lean spec to follow)

Proposed Lean model:
- Reuse `UnstableLogState` from `UnstableLog.lean` for the unstable portion.
- Define a minimal `RaftLogState` with `firstIndex`, `committed`, and an unstable
  log state.
- Prove `append_last_index_eq` — the returned index equals `ents.last.index`.
- Prove `append_committed_unchanged` — committed is not modified.
- Prove `append_safety_gate` — if `after ≥ committed`, no entry `≤ committed` is
  removed (connecting to `UnstableLog.lean`'s `truncateAndAppend` theorems).
- Prove `append_empty_noop` — empty input leaves the log unchanged.
