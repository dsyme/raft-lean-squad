# Informal Specification: Leader Completeness

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `formal-verification/lean/FVSquad/LeaderCompleteness.lean`  
**Related**: Raft paper §5.4.1, `src/raft.rs` (vote-granting and log replication)  
**Phase**: 5 (implemented and proved in Lean)

---

## Purpose

The **Leader Completeness Property** is one of Raft's fundamental safety guarantees
(Raft §5.4.1):

> *If a log entry is committed in a given term, that entry will be present in the logs
> of all leaders for all higher-numbered terms.*

In practice, this means a newly elected leader always has the most up-to-date log — it
will never be missing an entry that a majority of the cluster has already committed.

This property is the bridge between Raft's **election safety** (at most one winner per
term) and **log safety** (committed entries are never lost).  Without it, a leader could
be elected without some committed entries, causing data loss.

---

## The Argument (Informal)

The proof rests on two interacting invariants:

1. **Quorum overlap**: the set of nodes that voted for a winner (a majority) and the set
   of nodes that acknowledged a committed entry (also a majority) must share at least one
   node — because any two majorities over the same voter list must intersect.

2. **Vote freshness gate**: Raft grants a vote only when the candidate's log is *at
   least as up-to-date* as the voter's log (`isUpToDate`).  A candidate's log is more
   up-to-date if its last entry has a higher term, or if its last entry has the same term
   but a greater or equal index.

Together, these imply: the shared voter (who both voted *for* the winner and *has* the
committed entry) only voted because the winner's log was at least as fresh as theirs.
Combined with the Log Matching Invariant (LMI), this forces the winner's log to contain
all entries up to and including the committed one.

---

## Preconditions

- `voters` is a non-empty list of node identifiers (a valid Raft configuration).
- `record : VoteRecord` records, for each (term, voter) pair, which candidate the voter
  voted for in that term.  The record is consistent: every recorded vote was cast via
  `voteGranted` (the `VoteRecordConsistency` invariant).
- A candidate `cand` won term `term`: it received votes from a majority of `voters`.
- Entry `e` is quorum-committed at index `k`: a majority of `voters` has `e` in their
  log at index `k`.
- The **Log Matching Invariant** (`LogMatchingInvariantFor`) holds across the cluster:
  if two nodes agree on an entry at index `j`, they agree on all entries at indices ≤ `j`.
- The **CandidateLogCovers** condition holds: for every voter who voted for `cand`,
  `cand`'s log agrees with that voter's log at every index where the voter has an entry.
  This follows from `isUpToDate` combined with LMI (formalised as `HLogConsistency`).

---

## Postconditions

- The winner's log contains `e` at index `k`:  
  `candLog k = some e`  
  where `candLog` is the candidate's log at the time of the election.

---

## Key Intermediate Results

### VoteRecordConsistency (VRC)
Every vote in the record was cast according to `voteGranted`: if `record term voter = some cand`
then `voteGranted (voterLog voter) ... = true`.  This invariant is maintained by the
vote-request handler: a node only records a vote when `voteGranted` returns `true`.

### CandidateLogCovers
For every voter `w` who voted for `cand` in `term`, and for every index `k` where `w`
has an entry `e`, the candidate's log at `k` equals `w`'s log at `k`.

This is the **key bridge** between the election model and log safety.  It depends on:
- **Log Matching**: the candidate's log is an extension of every voter's log up to the
  voter's last index (follows from AppendEntries replication invariant).
- **No Truncation**: leaders never overwrite committed entries.

### HLogConsistency
If the candidate's log is at least as up-to-date as voter `w`'s log (i.e., `isUpToDate`
returns true), and voter `w` has entry `e` at index `k ≤ w.lastIndex`, then the
candidate also has `e` at `k`.

This is the missing protocol-level invariant (A4/A5 gap) that connects `isUpToDate`
comparisons to actual log content equivalence.

---

## Invariants

| Invariant | Description |
|-----------|-------------|
| `VoteRecordConsistency` | Every vote recorded was granted by `voteGranted` |
| `CandidateLogCovers` | Winning candidate's log matches every voter who voted for it |
| `HLogConsistency` | `isUpToDate` ⇒ log content agreement up to voter's last index |
| `LogMatchingInvariantFor` | Agreement at index `j` implies agreement at all ≤ `j` |

---

## Edge Cases

- **Empty voters**: the theorems require a non-empty voter list (`hd :: tl`) since both
  `wonInTerm` and `isQuorumCommitted` use `hasQuorum`, which requires a majority over
  a non-empty list to be meaningful.  An empty cluster has no committed entries.

- **Candidate wins with minimal majority**: the quorum intersection argument requires
  only that the voter list is non-empty; it works for any majority size ≥ ⌊n/2⌋+1.

- **Candidate log is shorter than voter's log**: `isUpToDate` compares `(lastTerm, lastIndex)`
  pairs.  A shorter log with a higher-term last entry is considered more up-to-date.  The
  candidate does not need a longer log — only a more recent one.

- **Same-term, same-index logs**: when the candidate and voter have identical `(lastTerm,
  lastIndex)`, `isUpToDate` returns `true`, but the logs may diverge *after* that index.
  `CandidateLogCovers` only requires agreement up to the voter's last replicated index.

---

## Examples

**Basic case** (3-voter cluster):
- Voters: `{A, B, C}`, term 2
- Committed entry `e` at index 5: both A and B have it (`isQuorumCommitted`)
- C wins term 2: A and B voted for C
- A voted for C because C's log had `(lastTerm=2, lastIndex=5)` ≥ A's `(lastTerm=2, lastIndex=5)`
- By quorum overlap: A is in both quorums → A voted for C AND A has `e` at 5
- By `CandidateLogCovers`: C's log at 5 = A's log at 5 = `some e`
- **Conclusion**: C has `e` at index 5 ✓

**Larger term** (stronger up-to-dateness):
- A has `(lastTerm=1, lastIndex=10)`, C has `(lastTerm=2, lastIndex=3)`
- `isUpToDate A.log 2 3 = true` because C's last term (2) > A's last term (1)
- C's log at indices ≤ 3 matches A's log (by HLogConsistency + LMI)
- But entries at indices 4–10 in A's log were from term 1 and are superseded

---

## Lean 4 Formalisation

The formal proof in `LeaderCompleteness.lean` is structured as:

| ID  | Lean Name | Property |
|-----|-----------|---------|
| LC1 | `electionWinner_overlaps_commitQuorum` | Vote quorum ∩ commit quorum ≠ ∅ |
| LC2 | `electionWinner_shared_voter` | Shared voter voted for winner AND has committed entry |
| LC3 | `leaderCompleteness` | Winner has all committed entries (given `CandidateLogCovers`) |
| LC4 | `leaderCompleteness_fullChain` | Unique winner + has committed entries (uses RE5) |
| LC5 | `wonInTerm_implies_isUpToDate` | Voter who voted → winner was `isUpToDate` |
| LC5b | `wonInTerm_voters_allUpToDate` | All voters who voted → winner was `isUpToDate` wrt each |
| LC6 | `hqc_preserved_from_leaderBroadcast` | Concrete condition discharging `hqc_preserved` |
| LC7 | `candidateLog_of_logMatchingAndUpToDate` | LMI + `HLogConsistency` → `CandidateLogCovers` |
| LC8 | `leaderCompleteness_via_logMatching` | Full LC given LMI + VRC + `HLogConsistency` |

---

## Open Questions

None — all key aspects are formalised and proved in Lean.  The remaining proof
obligation (discharging `HLogConsistency` from a concrete model of AppendEntries
transitions) is addressed by `ElectionReachability.lean` (ER1–ER12) and
`ElectionConcreteModel.lean` (ECM1–ECM6).

---

## Inferred Intent

From the Raft paper, Raft's leader completeness is explicitly required to prevent a
newly elected leader from inadvertently overwriting committed entries.  The formal proof
in this file makes the dependency structure explicit: `HLogConsistency` is the deepest
protocol invariant, and it is discharged only via the AppendEntries broadcast history
(`hae`).  Any future change to the vote-granting or replication logic must preserve
these invariants.

*Generated by Lean Squad Run 104 — 2026-04-25 UTC.*
