/// The Fiat-Shamir crate has two types of errors:
/// [`DomainSeparatorMismatch`], which is the error exposed in the low-level interface for
/// bytes and native elements, which arises whenever the IO Pattern specified and the IO
/// pattern executed mismatch. [`ProofError`], which is the error exposed to high-level
/// interfaces dealing with structured types and for end-user applications.
/// Three types of errors can happen when dealing with [`ProofError`]:
///
/// - Serialization/Deseralization errors ([`ProofError::SerializationError`]): This includes
///   all potential problems when extracting a particular type from sequences of bytes.
///
/// - Invalid Proof format ([`ProofError::InvalidIO`]): At a higher level, a proof object have
///   to respect the same length and the same types as the protocol description. This error is
///   a wrapper under the [`DomainSeparatorMismatch`] and provides convenient
///   dereference/conversion implementations for moving from/to an [`DomainSeparatorMismatch`].
///
/// - Invalid Proof: An error to signal that the verification equation has failed. Destined for
///   end users.
///
/// A [`core::Result::Result`] wrapper called [`ProofResult`] (having error fixed to
/// [`ProofError`]) is also provided.
use std::{error::Error, fmt::Display};

/// An error happened when creating or verifying a proof.
#[derive(Debug, Clone)]
pub enum ProofError {
    /// Signals the verification equation has failed.
    InvalidProof,
    /// Verifier is asking more data than what was provided in the transcript.
    ExceededTranscript,
    /// Invalid Pow Grinding
    InvalidGrindingWitness,
    /// Invalid Padding in the transcript
    InvalidPadding,
}

/// The result type when trying to prove or verify a proof using Fiat-Shamir.
pub type ProofResult<T> = Result<T, ProofError>;

impl Display for ProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof => write!(f, "Invalid proof"),
            Self::ExceededTranscript => write!(f, "Verifier exceeded transcript length"),
            Self::InvalidGrindingWitness => write!(f, "Invalid grinding witness"),
            Self::InvalidPadding => write!(f, "Invalid padding in the transcript"),
        }
    }
}

impl Error for ProofError {}
