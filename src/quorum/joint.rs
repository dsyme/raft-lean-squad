// Copyright 2020 TiKV Project Authors. Licensed under Apache-2.0.

use super::{AckedIndexer, VoteResult};
use crate::util::Union;
use crate::HashSet;
use crate::MajorityConfig;
use std::cmp;

/// A configuration of two groups of (possibly overlapping) majority configurations.
/// Decisions require the support of both majorities.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Configuration {
    pub(crate) incoming: MajorityConfig,
    pub(crate) outgoing: MajorityConfig,
}

impl Configuration {
    /// Creates a new configuration using the given IDs.
    pub fn new(voters: HashSet<u64>) -> Configuration {
        Configuration {
            incoming: MajorityConfig::new(voters),
            outgoing: MajorityConfig::default(),
        }
    }

    #[cfg(test)]
    pub(crate) fn new_joint_from_majorities(
        incoming: MajorityConfig,
        outgoing: MajorityConfig,
    ) -> Self {
        Self { incoming, outgoing }
    }

    /// Creates an empty configuration with given capacity.
    pub fn with_capacity(cap: usize) -> Configuration {
        Configuration {
            incoming: MajorityConfig::with_capacity(cap),
            outgoing: MajorityConfig::default(),
        }
    }

    /// Returns the largest committed index for the given joint quorum. An index is
    /// jointly committed if it is committed in both constituent majorities.
    ///
    /// The bool flag indicates whether the index is computed by group commit algorithm
    /// successfully. It's true only when both majorities use group commit.
    pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool) {
        let (i_idx, i_use_gc) = self.incoming.committed_index(use_group_commit, l);
        let (o_idx, o_use_gc) = self.outgoing.committed_index(use_group_commit, l);
        (cmp::min(i_idx, o_idx), i_use_gc && o_use_gc)
    }

    /// Takes a mapping of voters to yes/no (true/false) votes and returns a result
    /// indicating whether the vote is pending, lost, or won. A joint quorum requires
    /// both majority quorums to vote in favor.
    pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult {
        let i = self.incoming.vote_result(&check);
        let o = self.outgoing.vote_result(check);
        match (i, o) {
            // It won if won in both.
            (VoteResult::Won, VoteResult::Won) => VoteResult::Won,
            // It lost if lost in either.
            (VoteResult::Lost, _) | (_, VoteResult::Lost) => VoteResult::Lost,
            // It remains pending if pending in both or just won in one side.
            _ => VoteResult::Pending,
        }
    }

    /// Clears all IDs.
    pub fn clear(&mut self) {
        self.incoming.clear();
        self.outgoing.clear();
    }

    /// Returns true if (and only if) there is only one voting member
    /// (i.e. the leader) in the current configuration.
    pub fn is_singleton(&self) -> bool {
        self.outgoing.is_empty() && self.incoming.len() == 1
    }

    /// Returns an iterator over two hash set without cloning.
    pub fn ids(&self) -> Union<'_> {
        Union::new(&self.incoming, &self.outgoing)
    }

    /// Check if an id is a voter.
    #[inline]
    pub fn contains(&self, id: u64) -> bool {
        self.incoming.contains(&id) || self.outgoing.contains(&id)
    }

    /// Describe returns a (multi-line) representation of the commit indexes for the
    /// given lookuper.
    #[cfg(test)]
    pub(crate) fn describe(&self, l: &impl AckedIndexer) -> String {
        MajorityConfig::new(self.ids().iter().collect()).describe(l)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quorum::VoteResult;

    // These 15 cases mirror FVSquad/JointVoteCorrespondence.lean exactly.
    // Each case specifies incoming voters, outgoing voters, yes-voters, no-voters,
    // and the expected joint VoteResult.
    //
    // Cases 1–9 cover all 9 combinations of (incoming result) × (outgoing result).
    // Cases 10–13 cover non-joint / degenerate configurations.
    // Cases 14–15 cover larger quorums.
    #[test]
    fn test_joint_vote_result_correspondence() {
        let cases: &[(&[u64], &[u64], &[u64], &[u64], VoteResult)] = &[
            // Case 1: incoming=Won, outgoing=Won → Won
            (&[1, 2, 3], &[4, 5], &[1, 2, 3, 4, 5], &[], VoteResult::Won),
            // Case 2: incoming=Won, outgoing=Lost → Lost
            (&[1, 2, 3], &[4, 5], &[1, 2], &[4, 5], VoteResult::Lost),
            // Case 3: incoming=Won, outgoing=Pending → Pending
            (&[1, 2, 3], &[4, 5], &[1, 2, 4], &[], VoteResult::Pending),
            // Case 4: incoming=Lost, outgoing=Won → Lost
            (&[1, 2, 3], &[4, 5], &[4, 5], &[1, 2, 3], VoteResult::Lost),
            // Case 5: incoming=Lost, outgoing=Lost → Lost
            (&[1, 2, 3], &[4, 5], &[], &[1, 2, 3, 4, 5], VoteResult::Lost),
            // Case 6: incoming=Lost, outgoing=Pending → Lost
            (&[1, 2, 3], &[4, 5], &[4], &[1, 2, 3], VoteResult::Lost),
            // Case 7: incoming=Pending, outgoing=Won → Pending
            (&[1, 2, 3], &[4, 5], &[1, 4, 5], &[3], VoteResult::Pending),
            // Case 8: incoming=Pending, outgoing=Lost → Lost
            (&[1, 2, 3], &[4, 5], &[1], &[3, 4, 5], VoteResult::Lost),
            // Case 9: incoming=Pending, outgoing=Pending → Pending
            (&[1, 2, 3], &[4, 5], &[1, 4], &[3], VoteResult::Pending),
            // Case 10: empty incoming (convention Won), outgoing Won → Won
            (&[], &[4, 5], &[4, 5], &[], VoteResult::Won),
            // Case 11: non-joint (empty outgoing), incoming Won → Won
            (&[1], &[], &[1], &[], VoteResult::Won),
            // Case 12: non-joint (empty outgoing), incoming Lost → Lost
            (&[1], &[], &[], &[1], VoteResult::Lost),
            // Case 13: non-joint (empty outgoing), incoming Pending → Pending
            (&[1], &[], &[], &[], VoteResult::Pending),
            // Case 14: 2+2 voters, both Win → Won
            (&[1, 2], &[3, 4], &[1, 2, 3, 4], &[], VoteResult::Won),
            // Case 15: 5-voter incoming Won, 4-voter outgoing Lost → Lost
            (&[1, 2, 3, 4, 5], &[6, 7, 8, 9], &[1, 2, 3], &[6, 7, 8, 9], VoteResult::Lost),
        ];

        for (i, &(incoming_ids, outgoing_ids, yes_ids, no_ids, expected)) in cases.iter().enumerate() {
            let incoming: MajorityConfig = MajorityConfig::new(
                incoming_ids.iter().copied().collect()
            );
            let outgoing: MajorityConfig = MajorityConfig::new(
                outgoing_ids.iter().copied().collect()
            );
            let cfg = Configuration::new_joint_from_majorities(incoming, outgoing);
            let check = |id: u64| -> Option<bool> {
                if yes_ids.contains(&id) {
                    Some(true)
                } else if no_ids.contains(&id) {
                    Some(false)
                } else {
                    None
                }
            };
            let result = cfg.vote_result(check);
            assert_eq!(
                result, expected,
                "Case {}: incoming={:?} outgoing={:?} yes={:?} no={:?}: expected {:?}, got {:?}",
                i + 1, incoming_ids, outgoing_ids, yes_ids, no_ids, expected, result
            );
        }
    }
}
