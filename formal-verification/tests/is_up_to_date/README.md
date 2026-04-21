# Correspondence Tests: `is_up_to_date`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

Task 8 (Route B) of the Lean Squad workflow verifies that the abstract Lean model
and the concrete Rust implementation agree on observable input/output behaviour.

| Level | Where checked | Tool |
|-------|--------------|------|
| Lean model | `FVSquad/IsUpToDateCorrespondence.lean` | `#guard` (compile-time) |
| Rust implementation | `src/raft_log.rs` `test_is_up_to_date_correspondence` | `cargo test` |

Both test suites use the same 12 cases defined in `cases.json`.

## Running the tests

```bash
# Lean — compile-time guards (run from repo root)
cd formal-verification/lean
lake build FVSquad.IsUpToDateCorrespondence

# Rust — unit test
cargo test test_is_up_to_date_correspondence
```

## Case summary

Cases 1–9 mirror the 9 cases in the existing Rust unit test `test_is_up_to_date`
(log = `[(1,1),(2,2),(3,3)]` → `last_term=3`, `last_index=3`).

| ID | voter_term | voter_index | cand_term | cand_index | expected | Property |
|----|-----------|------------|-----------|-----------|---------|---------|
| 1  | 3 | 3 | 4 | 2 | true  | higher cand term beats lower index |
| 2  | 3 | 3 | 4 | 3 | true  | higher cand term wins |
| 3  | 3 | 3 | 4 | 4 | true  | higher cand term wins |
| 4  | 3 | 3 | 2 | 2 | false | lower cand term loses |
| 5  | 3 | 3 | 2 | 3 | false | lower cand term loses |
| 6  | 3 | 3 | 2 | 4 | false | lower cand term loses even with higher index |
| 7  | 3 | 3 | 3 | 2 | false | same term, shorter cand log loses |
| 8  | 3 | 3 | 3 | 3 | true  | same term, equal (isUpToDate_refl) |
| 9  | 3 | 3 | 3 | 4 | true  | same term, longer cand log wins |
| 10 | 0 | 0 | 0 | 0 | true  | empty voter log |
| 11 | 5 | 10 | 5 | 9 | false | same term, shorter cand |
| 12 | 5 | 10 | 6 | 0 | true  | higher cand term wins regardless |

## Correspondence model

The Lean model `isUpToDate` is a pure functional abstraction of the Rust
`RaftLog::is_up_to_date` method.  It abstracts:

- `RaftLog` → `LogId { term, index }` (captures only `last_term()` and `last_index()`)
- `u64` → `Nat` (no overflow; practical log sizes ≪ 2^63)
- No I/O, storage, or mutable state — pure comparison function

The function logic is identical:
```
Lean:  cand_term > voter.term || (cand_term == voter.term && cand_index >= voter.index)
Rust:  term > self.last_term() || (term == self.last_term() && last_index >= self.last_index())
```
