# Correspondence Tests: `committed_index`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

Task 8 (Route B) of the Lean Squad workflow verifies that the abstract Lean model
and the concrete Rust implementation agree on observable input/output behaviour.

| Level | Where checked | Tool |
|-------|--------------|------|
| Lean model | `FVSquad/CommittedIndexCorrespondence.lean` | `#guard` (compile-time) |
| Rust implementation | `src/quorum/majority.rs` `test_committed_index_correspondence` | `cargo test` |

Both test suites use the same 8 cases defined in `cases.json`.

## Running the tests

```bash
# Lean — compile-time guards (run from repo root)
cd formal-verification/lean
lake build FVSquad.CommittedIndexCorrespondence

# Rust — unit test
cargo test test_committed_index_correspondence
```

## Case summary

| ID | voters | acked_map | sorted_desc | majority | expected |
|----|--------|-----------|-------------|---------|---------|
| 1  | [1] | {1→5} | [5] | 1 | 5 |
| 2  | [1,2] | {1→5,2→3} | [5,3] | 2 | 3 |
| 3  | [1,2,3] | {1→2,2→4,3→6} | [6,4,2] | 2 | 4 |
| 4  | [1,2,3] | {1→2,2→2,3→2} | [2,2,2] | 2 | 2 |
| 5  | [1,2,3] | {1→0,2→0,3→0} | [0,0,0] | 2 | 0 |
| 6  | [1,2,3,4,5] | {1→1,…,5→5} | [5,4,3,2,1] | 3 | 3 |
| 7  | [1,2] | {1→10} (voter 2 missing→0) | [10,0] | 2 | 0 |
| 8  | [1,2,3] | {1→10,2→10,3→10} | [10,10,10] | 2 | 10 |

## Correspondence model

The Lean model `committedIndex` is a pure functional abstraction of the Rust
`Configuration::committed_index(false, l)` method.  Correspondence:

- `voters : List Nat` ↔ `cfg.voters : HashSet<u64>`
- `acked : Nat → Nat` ↔ `l.acked_index(v).unwrap_or_default().index`
- `majority(n) = n/2+1` ↔ `crate::majority(n) = n/2+1`
- Sorting in descending order is identical on both sides

**What is not tested**: the `use_group_commit = true` path (group-commit extension)
and the `voters.is_empty()` branch (Rust returns `u64::MAX`, Lean model returns 0
— this divergence is documented in `CORRESPONDENCE.md`).
