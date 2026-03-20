# Informal Specification: `RaftLog::slice` and `must_check_outofbounds`

🔬 *Lean Squad — automated formal verification for dsyme/fv-squad.*

**Source files**: `src/raft_log.rs` (lines ~501–700), `src/log_unstable.rs` (lines ~182–210)

---

## Purpose

`RaftLog::slice(low, high, max_size, context)` retrieves a contiguous range of log
entries with indices in the half-open interval **[low, high)**.

The log is physically stored in two parts:
- **Stable storage** (`self.store`): entries at indices `[first_index, unstable.offset)`.
- **Unstable buffer** (`self.unstable`): entries at indices
  `[unstable.offset, unstable.offset + unstable.entries.len())`.

`slice` transparently assembles entries from whichever part(s) contain the requested
range, then truncates the result to at most `max_size` bytes via `limit_size`.

`must_check_outofbounds` is the guard that validates [low, high) before any
assembly takes place.

---

## Preconditions

For `must_check_outofbounds(low, high)` to not panic:
- `low ≤ high` (otherwise panics with "invalid slice lo > hi")
- `high ≤ last_index() + 1` (otherwise panics with "slice out of bound")

Return values of `must_check_outofbounds`:
- Returns `Some(Error::Store(StorageError::Compacted))` if `low < first_index()`
- Returns `None` (success) if `first_index() ≤ low ≤ high ≤ last_index() + 1`

For `slice(low, high, max_size, context)` to succeed:
- `must_check_outofbounds(low, high)` returns `None` (no error)
- In particular: `first_index() ≤ low ≤ high ≤ last_index() + 1`

---

## Postconditions

Let `offset = unstable.offset`, `U = unstable.offset + unstable.entries.len()`.

1. **Return type**: `Ok(entries: Vec<Entry>)`.

2. **Count bound**: `entries.len() ≤ high - low`.

3. **Split-point assembly**: The result is assembled by concatenating:
   - *Stable part*: `store.entries(low, min(high, offset), max_size, context)`
     for the portion `low < offset`.
   - *Unstable part*: `unstable.entries[max(low, offset) - offset .. high - offset]`
     for the portion `high > offset`.
   If the stable read returns an `Unavailable` error, the function panics.
   If it returns `LogTemporarilyUnavailable`, the error is propagated.

4. **Early return**: If the stable read returns fewer entries than requested
   (i.e., fewer than `min(high, offset) - low`), the unstable part is **not** read
   and the truncated stable result is returned directly. This handles the case where
   storage is compacting.

5. **Size cap**: After assembly, `limit_size(&mut ents, max_size)` is called.
   The result has cumulative entry-byte-size ≤ `max_size` (or all entries if
   `max_size` is `None`/`NO_LIMIT`). The cap always includes at least the first
   entry, even if it exceeds `max_size`.

6. **Empty range**: If `low == high`, returns `Ok(vec![])` immediately.

---

## Invariants

- The assembled entries are a **contiguous prefix** of the full [low, high) range in
  index order: returned entries span indices `[low, low + count)` for some
  `count ≤ high - low`.
- Returned indices are **strictly increasing** (consecutive integers starting at `low`).
- No gaps: if an entry at index `i` is present and `i < high - 1`, then either
  `i+1` is also present or the size limit was hit.

---

## `Unstable::slice(lo, hi)` (inner helper)

Used internally by `RaftLog::slice` for the unstable portion.

Preconditions (checked by `must_check_outofbounds`):
- `lo ≥ offset` and `hi ≤ offset + entries.len()`
- `lo ≤ hi`

Returns: `&entries[lo - offset .. hi - offset]` — a direct slice into the Vec.

The `Unstable::must_check_outofbounds` panics (using `fatal!`) if these are violated.
Unlike `RaftLog::must_check_outofbounds`, it does not return a `Compacted` error —
the unstable region is always in memory.

---

## Edge Cases

1. **Empty range** (`low == high`): returns `Ok(vec![])` immediately, no I/O.

2. **Fully compacted** (`low < first_index`): `must_check_outofbounds` returns
   `Some(Compacted)`, propagated as `Err`.

3. **Entirely in stable storage** (`high ≤ offset`): only stable storage is read,
   unstable buffer is untouched.

4. **Entirely in unstable buffer** (`low ≥ offset`): stable storage is skipped,
   only unstable slice is taken.

5. **Spanning the split** (`low < offset ≤ high`): both stable and unstable parts
   are read and concatenated; early-return guards ensure partial stable reads do
   not contaminate the unstable part.

6. **Size limit of 0**: `limit_size` always includes at least one entry; result is
   a single-entry vec (the first entry in the range).

7. **NO_LIMIT** (`max_size = None`): all entries in [low, high) are returned.

---

## Examples

From `test_slice` (offset=100, num=100, stable=[101..150), unstable=[150..200)):

| low | high | max_size  | expected result        | notes                          |
|-----|------|-----------|------------------------|--------------------------------|
| 99  | 101  | NO_LIMIT  | `Err(Compacted)`       | low < first_index=101          |
| 100 | 101  | NO_LIMIT  | `Err(Compacted)`       | low == first_index-1           |
| 149 | 151  | NO_LIMIT  | `[149, 150]`           | spans stable/unstable split    |
| 150 | 151  | NO_LIMIT  | `[150]`                | entirely unstable              |
| 199 | 200  | NO_LIMIT  | `[199]`                | last entry                     |
| 200 | 201  | NO_LIMIT  | panic                  | hi > last_index+1              |
| 149 | 151  | 0         | `[149]`                | size limit: at least 1 entry   |
| 149 | 152  | 2*halfe   | `[149, 150]`           | 2-entry size cap               |

---

## Inferred Intent

The split-point assembly pattern is fundamental to the Raft log design: stable
storage is the persistent backing store (disk), while the unstable buffer is the
in-memory staging area for recently proposed entries. `slice` abstracts this
split so callers see a unified sequential log.

The early-return on partial stable reads is a **correctness guard**: if stable
storage returns fewer entries than requested (possible during a background
compaction), the function does not attempt to fill in with unstable entries
at potentially non-adjacent indices, avoiding index-discontinuities in results.

---

## Open Questions

1. **Concurrent compaction safety**: Can `first_index()` change between
   `must_check_outofbounds` and the `store.entries(...)` call? If so, is the
   `Compacted` error returned from `store.entries` sufficient, or is there a TOCTOU
   gap?

2. **Unstable gap**: Is it possible for `unstable.offset > last_stable_index + 1`
   (i.e., a gap between stable and unstable)? The code does not explicitly guard
   against this. If a gap exists, does `slice` silently skip those indices?

3. **limit_size vs stable early-return**: If stable storage returns exactly
   `min(high, offset) - low` entries but they already exceed `max_size`, the
   unstable portion is still read. Should the size check happen before the
   unstable read? (Currently, `limit_size` is applied only at the very end.)

4. **`context` parameter**: The `GetEntriesContext` is forwarded to storage but
   otherwise ignored in the spec. Its semantics (pagination hints, priority) are
   outside scope here.
