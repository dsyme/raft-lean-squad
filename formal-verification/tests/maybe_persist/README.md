# Correspondence Tests: `maybe_persist` and `maybe_persist_snap`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This directory contains test fixtures validating correspondence between the Lean 4 models
`maybePersist` / `maybePersistSnap` (in `FVSquad/MaybePersistCorrespondence.lean`) and
the Rust implementations `RaftLog::maybe_persist` / `RaftLog::maybe_persist_snap`
(in `src/raft_log.rs`).

## Purpose

Task 8 (Route B) of the Lean Squad workflow verifies that the abstract Lean model and the
concrete Rust implementation agree on observable input/output behaviour for a selected set
of representative cases.  Agreement is checked at two levels:

| Level | Where checked | Tool |
|-------|--------------|------|
| Lean model | `FVSquad/MaybePersistCorrespondence.lean` | `#guard` (compile-time) |
| Rust implementation | `src/raft_log.rs` `test_maybe_persist_correspondence` | `cargo test` |

Both test suites use exactly the same 15 cases defined in `cases.json`.

## Running the tests

```bash
# Lean – compile-time guards (run from repo root)
cd formal-verification/lean
lake build FVSquad.MaybePersistCorrespondence

# Rust – unit test
cargo test test_maybe_persist_correspondence
```

## Fixture: Log state

For `maybePersist` cases (IDs 1–10), the Rust side constructs a `RaftLog` as follows:
- `apply_snapshot(snap_index=3, term=1)` → `persisted = 3`
- Append entries `[(4,1), (5,2), (6,3)]` and stabilise → `first_update_index = 7`
- `store.term(4)=1`, `store.term(5)=2`, `store.term(6)=3`

This matches the Lean `testLogTerm` fixture.

For `maybePersistSnap` cases (IDs 11–15), the Rust side uses different `persisted` values
(3, 5, 6, 3, 0 respectively) to exercise the `index > persisted` branch, with
sufficient `committed` and `unstable.offset` to avoid fatal paths.

## Case table

| ID | variant | persisted | fui | call | expected | Guard failing |
|----|---------|-----------|-----|------|----------|---------------|
| 1  | persist | 3 | 7 | (5, 2) | true  | all pass |
| 2  | persist | 3 | 7 | (3, 1) | false | guard 1 |
| 3  | persist | 3 | 7 | (7, 3) | false | guard 2 |
| 4  | persist | 3 | 7 | (5,99) | false | guard 3 |
| 5  | persist | 3 | 7 | (4, 1) | true  | all pass |
| 6  | persist | 3 | 7 | (2, 1) | false | guard 1 |
| 7  | persist | 3 | 7 | (8, 3) | false | guard 2 |
| 8  | persist | 3 | 7 | (6, 3) | true  | all pass |
| 9  | persist | 3 | 7 | (6, 1) | false | guard 3 |
| 10 | persist | 5 | 7 | (5, 2) | false | guard 1 (idempotent) |
| 11 | snap    | 3 | — | snap(5) | true  | 5 > 3 |
| 12 | snap    | 5 | — | snap(5) | false | 5 ≤ 5 |
| 13 | snap    | 6 | — | snap(5) | false | 5 ≤ 6 |
| 14 | snap    | 3 | — | snap(4) | true  | 4 > 3 |
| 15 | snap    | 0 | — | snap(1) | true  | 1 > 0 |
