# Joint Vote Result Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

This directory contains shared test fixtures for **Route B correspondence validation**
of `Configuration::vote_result` in `src/quorum/joint.rs`.

## Correspondence level: **exact**

`jointVoteResult` directly mirrors `Configuration::vote_result`: it calls
`voteResult` (= `MajorityConfig::vote_result`) on each sub-quorum and combines
via the same 3-way match table.

## Test cases

`cases.json` defines 15 test cases covering all 9 combinations of sub-quorum results:

- Cases 1–9: all 9 (incoming result) × (outgoing result) combinations
- Cases 10–13: degenerate/non-joint configurations (empty incoming or outgoing)
- Cases 14–15: larger quorums

## Running the tests

**Lean side** (compile-time `#guard` checks):
```bash
cd formal-verification/lean && lake build FVSquad.JointVoteCorrespondence
```

**Rust side** (runtime assertion):
```bash
cargo test test_joint_vote_result_correspondence
```

Both commands must pass for correspondence to be considered validated.
