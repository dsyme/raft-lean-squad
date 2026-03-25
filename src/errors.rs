// Copyright 2019 TiKV Project Authors. Licensed under Apache-2.0.
#[cfg(feature = "thiserror")]
use thiserror::Error;
use std::fmt;

/// The base error type for raft
#[derive(Debug)]
#[cfg_attr(feature = "thiserror", derive(Error))]
pub enum Error {
    /// An IO error occurred
    #[cfg_attr(feature = "thiserror", error("{0}"))]
    #[cfg(not(feature = "aeneas"))]
    Io(#[cfg_attr(feature = "thiserror", from)] std::io::Error),
    /// A storage error occurred.
    #[cfg_attr(feature = "thiserror", error("{0}"))]
    Store(#[cfg_attr(feature = "thiserror", from)] StorageError),
    /// Raft cannot step the local message.
    #[cfg_attr(feature = "thiserror", error("raft: cannot step raft local message"))]
    StepLocalMsg,
    /// The raft peer is not found and thus cannot step.
    #[cfg_attr(feature = "thiserror", error("raft: cannot step as peer not found"))]
    StepPeerNotFound,
    /// The proposal of changes was dropped.
    #[cfg_attr(feature = "thiserror", error("raft: proposal dropped"))]
    ProposalDropped,
    /// The configuration is invalid.
    #[cfg_attr(feature = "thiserror", error("{0}"))]
    ConfigInvalid(String),
    /// A protobuf message codec failed in some manner.
    #[cfg_attr(feature = "thiserror", error("protobuf codec error {0:?}"))]
    CodecError(#[cfg_attr(feature = "thiserror", from)] crate::protocompat::PbError),
    /// The node exists, but should not.
    #[cfg_attr(feature = "thiserror", error("The node {id} already exists in the {set} set."))]
    Exists {
        /// The node id.
        id: u64,
        /// The node set.
        set: &'static str,
    },
    /// The node does not exist, but should.
    #[cfg_attr(feature = "thiserror", error("The node {id} is not in the {set} set."))]
    NotExists {
        /// The node id.
        id: u64,
        /// The node set.
        set: &'static str,
    },
    /// ConfChange proposal is invalid.
    #[cfg_attr(feature = "thiserror", error("{0}"))]
    ConfChangeError(String),
    /// The request snapshot is dropped.
    #[cfg_attr(feature = "thiserror", error("raft: request snapshot dropped"))]
    RequestSnapshotDropped,
}

#[cfg(not(feature = "thiserror"))]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Store(e) => write!(f, "{e}"),
            Error::StepLocalMsg => write!(f, "raft: cannot step raft local message"),
            Error::StepPeerNotFound => write!(f, "raft: cannot step as peer not found"),
            Error::ProposalDropped => write!(f, "raft: proposal dropped"),
            Error::ConfigInvalid(s) => write!(f, "{s}"),
            Error::CodecError(e) => write!(f, "protobuf codec error {e:?}"),
            Error::Exists { id, set } => write!(f, "The node {id} already exists in the {set} set."),
            Error::NotExists { id, set } => write!(f, "The node {id} is not in the {set} set."),
            Error::ConfChangeError(s) => write!(f, "{s}"),
            Error::RequestSnapshotDropped => write!(f, "raft: request snapshot dropped"),
            #[cfg(not(feature = "aeneas"))]
            Error::Io(e) => write!(f, "{e}"),
        }
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Error) -> bool {
        match (self, other) {
            (Error::StepPeerNotFound, Error::StepPeerNotFound) => true,
            (Error::ProposalDropped, Error::ProposalDropped) => true,
            (Error::Store(ref e1), Error::Store(ref e2)) => e1 == e2,
            #[cfg(not(feature = "aeneas"))]
            (Error::Io(ref e1), Error::Io(ref e2)) => e1.kind() == e2.kind(),
            (Error::StepLocalMsg, Error::StepLocalMsg) => true,
            (Error::ConfigInvalid(ref e1), Error::ConfigInvalid(ref e2)) => e1 == e2,
            (Error::RequestSnapshotDropped, Error::RequestSnapshotDropped) => true,
            (Error::ConfChangeError(e1), Error::ConfChangeError(e2)) => e1 == e2,
            _ => false,
        }
    }
}

/// An error with the storage.
#[derive(Debug)]
#[cfg_attr(feature = "thiserror", derive(Error))]
pub enum StorageError {
    /// The storage was compacted and not accessible
    #[cfg_attr(feature = "thiserror", error("log compacted"))]
    Compacted,
    /// The log is not available.
    #[cfg_attr(feature = "thiserror", error("log unavailable"))]
    Unavailable,
    /// The log is being fetched.
    #[cfg_attr(feature = "thiserror", error("log is temporarily unavailable"))]
    LogTemporarilyUnavailable,
    /// The snapshot is out of date.
    #[cfg_attr(feature = "thiserror", error("snapshot out of date"))]
    SnapshotOutOfDate,
    /// The snapshot is being created.
    #[cfg_attr(feature = "thiserror", error("snapshot is temporarily unavailable"))]
    SnapshotTemporarilyUnavailable,
    /// Some other error occurred.
    #[cfg(not(feature = "aeneas"))]
    #[cfg_attr(feature = "thiserror", error("unknown error {0}"))]
    Other(#[cfg_attr(feature = "thiserror", from)] Box<dyn std::error::Error + Sync + Send>),
}

#[cfg(not(feature = "thiserror"))]
impl fmt::Display for StorageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StorageError::Compacted => write!(f, "log compacted"),
            StorageError::Unavailable => write!(f, "log unavailable"),
            StorageError::LogTemporarilyUnavailable => write!(f, "log is temporarily unavailable"),
            StorageError::SnapshotOutOfDate => write!(f, "snapshot out of date"),
            StorageError::SnapshotTemporarilyUnavailable => write!(f, "snapshot is temporarily unavailable"),
            #[cfg(not(feature = "aeneas"))]
            StorageError::Other(e) => write!(f, "unknown error {e}"),
        }
    }
}

impl PartialEq for StorageError {
    fn eq(&self, other: &StorageError) -> bool {
        matches!(
            (self, other),
            (StorageError::Compacted, StorageError::Compacted)
                | (StorageError::Unavailable, StorageError::Unavailable)
                | (
                    StorageError::LogTemporarilyUnavailable,
                    StorageError::LogTemporarilyUnavailable
                )
                | (
                    StorageError::SnapshotOutOfDate,
                    StorageError::SnapshotOutOfDate
                )
                | (
                    StorageError::SnapshotTemporarilyUnavailable,
                    StorageError::SnapshotTemporarilyUnavailable,
                )
        )
    }
}

/// A result type that wraps up the raft errors.
pub type Result<T> = std::result::Result<T, Error>;

#[cfg(not(feature = "thiserror"))]
impl From<StorageError> for Error {
    fn from(e: StorageError) -> Self {
        Error::Store(e)
    }
}

#[cfg(not(feature = "thiserror"))]
impl From<crate::protocompat::PbError> for Error {
    fn from(e: crate::protocompat::PbError) -> Self {
        Error::CodecError(e)
    }
}

#[allow(clippy::eq_op)]
#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    #[test]
    fn test_error_equal() {
        assert_eq!(Error::StepPeerNotFound, Error::StepPeerNotFound);
        assert_eq!(
            Error::Store(StorageError::Compacted),
            Error::Store(StorageError::Compacted)
        );
        assert_eq!(
            Error::Io(io::Error::new(io::ErrorKind::UnexpectedEof, "oh no!")),
            Error::Io(io::Error::new(io::ErrorKind::UnexpectedEof, "oh yes!"))
        );
        assert_ne!(
            Error::Io(io::Error::new(io::ErrorKind::NotFound, "error")),
            Error::Io(io::Error::new(io::ErrorKind::BrokenPipe, "error"))
        );
        assert_eq!(Error::StepLocalMsg, Error::StepLocalMsg);
        assert_eq!(
            Error::ConfigInvalid(String::from("config error")),
            Error::ConfigInvalid(String::from("config error"))
        );
        assert_ne!(
            Error::ConfigInvalid(String::from("config error")),
            Error::ConfigInvalid(String::from("other error"))
        );
        assert_eq!(
            Error::from(io::Error::other("oh no!")),
            Error::from(io::Error::other("oh yes!"))
        );
        assert_ne!(
            Error::StepPeerNotFound,
            Error::Store(StorageError::Compacted)
        );
    }

    #[test]
    fn test_storage_error_equal() {
        assert_eq!(StorageError::Compacted, StorageError::Compacted);
        assert_eq!(StorageError::Unavailable, StorageError::Unavailable);
        assert_eq!(
            StorageError::SnapshotOutOfDate,
            StorageError::SnapshotOutOfDate
        );
        assert_eq!(
            StorageError::SnapshotTemporarilyUnavailable,
            StorageError::SnapshotTemporarilyUnavailable
        );
        assert_ne!(StorageError::Compacted, StorageError::Unavailable);
        assert_ne!(
            StorageError::Other(Box::new(StorageError::Unavailable)),
            StorageError::Unavailable
        );
    }
}
