# Informal Specification — `RaftLog::next_entries_since` + `applied_index_upper_bound`

> 🔬 *Lean Squad — informal specification for FV target 15.*

**Source**: `src/raft_log.rs`, lines ~450–480
**Language**: Rust

---

## Purpose

`next_entries_since(since_idx, max_size)` returns the next slice of log entries that are
ready to be applied to the application state machine.  
An entry is "ready to apply" if it is both:
- **committed** — acknowledged by a quorum of servers (index ≤ `committed`), and
- **applicable** — within the `max_apply_unpersisted_log_limit` (index ≤ `persisted + limit`).

The function avoids delivering entries that the application has already processed
(`since_idx` is typically the previously-applied index) and never reaches below the
log's compaction frontier (`first_index`).

The helper `applied_index_upper_bound()` computes the shared upper limit:
```rust
fn applied_index_upper_bound(&self) -> u64 {
    std::cmp::min(
        self.committed,
        self.persisted + self.max_apply_unpersisted_log_limit,
    )
}
```

---

## Preconditions

- `committed`, `persisted`, `applied`, `first_index` are all valid `u64` values.
- The log holds entries in the range `[first_index, last_index]`.
- `max_apply_unpersisted_log_limit` (`limit`) is a non-negative `u64`.
- `since_idx` is a valid application index (typically `applied`, may be 0 on first call).
- `max_size` is either `None` (unlimited) or `Some(n)` (byte budget).

---

## Core Definitions

### `applied_index_upper_bound`

```
aub = min(committed, persisted + limit)
```

- Always ≤ `committed` (no uncommitted entries escape).
- Always ≤ `persisted + limit` (no overshoot past the unpersisted cap).
- Monotone: if `committed` or `persisted` increases, `aub` can only increase.

### Window Computation

```
offset = max(since_idx + 1, first_index)
high   = aub + 1
```

The window is `[offset, high)`.  
**Non-empty condition**: `high > offset`, i.e., `aub ≥ offset`.

---

## Postconditions

1. **Returns `None`** iff `applied_index_upper_bound() + 1 ≤ max(since_idx + 1, first_index)`.
   Equivalently: no new ready entries exist starting from `offset`.

2. **Returns `Some(entries)`** (when non-empty):
   - `entries` is a sub-slice of the log in the range `[offset, high)`.
   - If `max_size` is given, the total byte size ≤ `max_size` (handled by `limit_size`; already proved in `LimitSize.lean`).
   - `entries` is non-empty (since `high > offset`).
   - First entry index = `offset`; entries are contiguous and in ascending index order.

3. **Bounds guaranteed**:
   - All returned entry indices are ≤ `committed` (never uncommitted).
   - All returned entry indices are ≤ `persisted + limit`.
   - All returned entry indices are ≥ `first_index` (never below compaction frontier).

---

## Invariants

### `applied_index_upper_bound` bounds
- `aub ≤ committed` — safety: no uncommitted entry can be applied.
- `aub ≤ persisted + limit` — policy: unpersisted-log cap is respected.

### Monotonicity
- If `committed'` ≥ `committed`, then `aub(committed', persisted, limit)` ≥ `aub(committed, persisted, limit)`.
- If `persisted'` ≥ `persisted`, then `aub(committed, persisted', limit)` ≥ `aub(committed, persisted, limit)`.

### Offset lower bound
- `offset ≥ first_index` always (the `max` clamps).

### Since monotonicity
- A larger `since_idx` gives a larger `offset`, producing a sub-window: the result (if any) starts later.

### Limit=0 case
- When `limit = 0`: `aub = min(committed, persisted)`. Ready entries require persistence.

---

## Edge Cases

| Scenario | Expected behavior |
|----------|------------------|
| `since_idx + 1 > aub` | `None` — no new entries |
| `first_index > aub` | `None` — log is ahead of applied-up-to-date |
| `since_idx + 1 = first_index` (first call after compaction) | `offset = first_index`; full window available |
| `limit = 0` | `aub = min(committed, persisted)`; no unpersisted entries |
| `limit = NO_LIMIT (u64::MAX)` | `aub = committed`; all committed entries eligible |
| `max_size = None` | Full window returned |
| `max_size = Some(0)` | Empty slice (but returns `Some([])` — `limit_size` behaviour; note: checked by `LimitSize.lean`) |
| `committed = persisted = since_idx` | `offset = since_idx + 1 > committed = aub`; `None` |

---

## Examples

### Example 1 — Normal case
```
committed = 10, persisted = 10, limit = 0, first_index = 1, since_idx = 5
aub    = min(10, 10) = 10
offset = max(6, 1) = 6
high   = 11
→ Some(entries[6..11])   -- 5 entries
```

### Example 2 — No new entries
```
committed = 5, persisted = 5, limit = 0, first_index = 1, since_idx = 5
aub    = 5
offset = max(6, 1) = 6
high   = 6
→ 6 > 6 is false → None
```

### Example 3 — Unpersisted cap active
```
committed = 100, persisted = 10, limit = 5, first_index = 1, since_idx = 0
aub    = min(100, 15) = 15
offset = max(1, 1) = 1
high   = 16
→ Some(entries[1..16])   -- 15 entries, all persisted+limit-bounded
```

### Example 4 — Log compacted ahead of since_idx
```
committed = 20, persisted = 20, limit = 0, first_index = 15, since_idx = 5
aub    = 20
offset = max(6, 15) = 15   -- clamped to first_index
high   = 21
→ Some(entries[15..21])   -- 6 entries from first_index onwards
```

---

## Inferred Intent

The design ensures that the state machine advances **at most one entry at a time through the
committed/persisted gate**, bounded by both the consensus commit point and the
unpersisted-log pipeline limit. The `since_idx` parameter enables incremental delivery
without re-sending already-applied entries, and the `first_index` clamp handles the case
where the application has been reset by a snapshot.

---

## Open Questions

1. **Atomicity**: Can `committed` or `persisted` change between computing `aub` and the slice?
   The Rust implementation holds a mutable `&mut self` reference for writes but `&self` here,
   so presumably external synchronisation is the caller's responsibility. The spec treats the
   values as immutable snapshots.

2. **`max_size = Some(0)`**: Does the current `limit_size` implementation return an empty
   slice or panic? The `LimitSize.lean` proof covers this; if `limit_size` returns `[]`,
   then `next_entries_since` would return `Some([])` which seems surprising.

3. **`first_index` after snapshot**: After `restore()`, `first_index` may jump significantly.
   If `since_idx` is from before the snapshot, `offset` is correctly clamped. But the
   application must handle the gap. This is a caller responsibility, not a property of this
   function.
