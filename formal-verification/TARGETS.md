# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). See `FVSquad/MajorityQuorum.lean`. |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). Bridge lemma `countGe_eq_sorted_countP` completed the `committedIndex_safety` and `committedIndex_maximal` proofs. See `FVSquad/CommittedIndex.lean`. |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 5 — Proofs | ✅ Done | All key theorems proved (0 `sorry`): `truncateAndAppend_wellFormed`, `stableEntries_wellFormed`, `stableSnap_wellFormed`. See `FVSquad/UnstableLog.lean`. |
| 4 | `Inflights` ring buffer | `src/tracker/inflights.rs` | 5 — Proofs | ✅ Done | Abstract model fully proved (0 `sorry`): 20+ theorems. Concrete ring-buffer model added with `concreteAdd_abstract`, `ring_pos_ne`. See `FVSquad/Inflights.lean`. |
| 5 | `limit_size` utility | `src/util.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). Budget helpers `limitSizeGo_count_add`, `limitSizeGo_budget'`, `limitSizeGo_stop_condition` enable proofs of `limitSize_sum_le` (budget safety) and `limitSize_maximal` (maximality). See `FVSquad/LimitSize.lean`. |
| 6 | `Progress` state machine | `src/tracker/progress.rs`, `src/tracker/state.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). ~45 theorems including master invariant `valid_preserved_by_all_ops`. See `FVSquad/Progress.lean`. |
| 7 | `JointConfig` joint quorum | `src/quorum/joint.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). 20+ theorems covering `jointVoteResult` and `jointCommittedIndex` safety/monotonicity. See `FVSquad/JointQuorum.lean`. |
| 8 | `is_up_to_date` + `find_conflict_by_term` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. `isUpToDate` (total preorder, 8 theorems), `findConflictByTerm` (8 theorems incl. maximality). See `FVSquad/LogOrdering.lean`. |
| 9 | `RaftLog::maybe_append` + `maybe_commit` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | All sorrys removed. `findConflict_zero_all_match` (with `hpos` precondition), `maybeAppend_commit_le_leader` (with `hle`), `maybeAppend_commit_le_lastNew` (with `hle`) fully proved via `commitTo_exact_or_unchanged`. See `FVSquad/MaybeAppend.lean`. |
| 10 | `ReadOnly` queue (ReadIndex protocol) | `src/read_only.rs` | 5 — Proofs | ✅ Done | All 30 theorems proved (0 `sorry`). `mem_take_indexOf` inductive lemma closed PROP-19/20. See `FVSquad/ReadOnly.lean`. |
| 11 | `RaftLog::maybe_persist` | `src/raft_log.rs` | 3 — Lean Spec | 🔄 In progress | Informal spec + 16 Lean propositions covering WF-preservation, monotonicity, idempotency, fixed-point. See `FVSquad/MaybePersist.lean`. |

| 10 | `ReadOnly` queue (ReadIndex protocol) | `src/read_only.rs` | 5 — Proofs | ✅ Done | All 30 theorems proved (0 `sorry`). `mem_take_indexOf` inductive lemma closed PROP-19/20. See `FVSquad/ReadOnly.lean`. |

| 11 | `RaftLog::maybe_persist` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | Informal spec + 16 Lean propositions, all proved (0 `sorry`). See `FVSquad/MaybePersist.lean`. |

| 12 | `RaftLog::maybe_commit` (standalone) | `src/raft_log.rs` | 5 — Proofs | ✅ Done | Informal spec + 16 theorems (0 `sorry`): guard iff, monotone committed, WF-preservation, idempotency, sequential composition. See `FVSquad/MaybeCommit.lean`. |

| 10 | `ReadOnly` queue (ReadIndex protocol) | `src/read_only.rs` | 5 — Proofs | ✅ Done | All 30 theorems proved (0 `sorry`). `mem_take_indexOf` inductive lemma closed PROP-19/20. See `FVSquad/ReadOnly.lean`. |

| 11 | `RaftLog::maybe_persist` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | Informal spec + 16 Lean propositions, all proved (0 `sorry`). See `FVSquad/MaybePersist.lean`. |

| 12 | `RaftLog::maybe_commit` (standalone) | `src/raft_log.rs` | 5 — Proofs | ✅ Done | Informal spec + 16 theorems (0 `sorry`): guard iff, monotone committed, WF-preservation, idempotency, sequential composition. See `FVSquad/MaybeCommit.lean`. |

| 13 | `Progress` tracking (`maybe_update`, `update_committed`, `maybe_decr_to`) | `src/tracker/progress.rs` | 5 — Proofs | ✅ Done | Informal spec + 31 theorems (0 `sorry`): monotonicity, WF-preservation (both Replicate and Probe states), stale-rejection characterisation, cross-operation commutativity. See `FVSquad/ProgressTracking.lean`. |

| 10 | `ReadOnly` queue (ReadIndex protocol) | `src/read_only.rs` | 5 — Proofs | ✅ Done | 30 theorems, 0 `sorry`. addRequest idempotency, recvAck ack accumulation, advance FIFO drain. `mem_take_indexOf` inductive lemma unlocked the 2 remaining `sorry`s. See `FVSquad/ReadOnly.lean`. |
| 11 | `RaftLog::maybe_persist` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. Term-checked guard: index > persisted, index < firstUpdateIndex, storedTerm matches. WF preserved. See `FVSquad/MaybePersist.lean`. |
| 12 | `RaftLog::maybe_commit` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. Raft §5.4.2 term-lock safety gate. Idempotent, WF preserved, committed non-decreasing. See `FVSquad/MaybeCommit.lean`. |
| 13 | `Progress::maybe_update` / `update_committed` / `maybe_decr_to` | `src/tracker/progress.rs` | 5 — Proofs | ✅ Done | 31 theorems, 0 `sorry`. WF = `next_idx ≥ matched + 1` preserved by all ops. See `FVSquad/ProgressTracking.lean`. |
| 14 | `ProgressTracker::quorum_recently_active` | `src/tracker.rs` | 5 — Proofs | 🔄 In progress | 15 theorems + examples. Self-inclusion, monotonicity, post-state reset. See `FVSquad/QuorumRecentlyActive.lean`. |

| 10 | `ReadOnly` queue (ReadIndex protocol) | `src/read_only.rs` | 5 — Proofs | ✅ Done | 30 theorems, 0 `sorry`. addRequest idempotency, recvAck ack accumulation, advance FIFO drain. `mem_take_indexOf` inductive lemma unlocked the 2 remaining `sorry`s. See `FVSquad/ReadOnly.lean`. |
| 11 | `RaftLog::maybe_persist` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. Term-checked guard: index > persisted, index < firstUpdateIndex, storedTerm matches. WF preserved. See `FVSquad/MaybePersist.lean`. |
| 12 | `RaftLog::maybe_commit` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. Raft §5.4.2 term-lock safety gate. Idempotent, WF preserved, committed non-decreasing. See `FVSquad/MaybeCommit.lean`. |
| 13 | `Progress::maybe_update` / `update_committed` / `maybe_decr_to` | `src/tracker/progress.rs` | 5 — Proofs | ✅ Done | 31 theorems, 0 `sorry`. WF = `next_idx ≥ matched + 1` preserved by all ops. See `FVSquad/ProgressTracking.lean`. |
| 14 | `ProgressTracker::quorum_recently_active` | `src/tracker.rs` | 5 — Proofs | 🔄 In progress | 15 theorems + examples. Self-inclusion, monotonicity, post-state reset. See `FVSquad/QuorumRecentlyActive.lean`. |
| 15 | `RaftLog::next_entries_since` + `applied_index_upper_bound` | `src/raft_log.rs` | 3 — Lean Spec | 🔄 In progress | Window computation for ready-to-apply entries. 7+ properties (aub bounds, monotonicity, window emptiness). See `FVSquad/NextEntries.lean`. |
| 16 | `RaftLog::append` | `src/raft_log.rs` | 2 — Informal Spec | 🔄 In progress | Informal spec written. Safety gate (`after ≥ committed`) prevents committed-entry truncation. See `specs/raftlog_append_informal.md`. |
| 17 | `RaftLog::entries` | `src/raft_log.rs` | 1 — Research | ⬜ Not started | Slice `[idx, last+1)` subject to `max_size`. Trivial bounds; delegates to `slice`. |
| 18 | `RaftLog::slice` + `must_check_outofbounds` | `src/raft_log.rs`, `src/log_unstable.rs` | 4 — Implementation | 🔄 In progress | Informal spec + 30 Lean theorems (0 `sorry`) + concrete `sliceIndices` model: 18 new theorems covering membership, partition, disjointness, tier completeness. See `FVSquad/RaftLogSlice.lean`. |

## Phase Legend

| Phase | Description |
|-------|-------------|
| 1 | Research — target identified, approach documented |
| 2 | Informal Spec — `specs/<name>_informal.md` written |
| 3 | Lean Spec — Lean 4 types + propositions (with `sorry`) |
| 4 | Implementation — Lean model of the Rust implementation |
| 5 | Proofs — `sorry`s removed, theorems fully proved |
