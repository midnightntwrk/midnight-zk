//! Custom error type for the IVC module.

use std::fmt;

use midnight_proofs::plonk;

/// Error type for IVC operations.
#[derive(Debug)]
pub enum IvcError {
    /// A proof generation failed.
    ProofGeneration(plonk::Error),
    /// The provided instance is malformed.
    InvalidInstance,
    /// The instance's VK representation does not match the verifier's key.
    VkMismatch,
    /// The proof is invalid (accumulator pairing check failed).
    InvalidProof,
    /// The proof transcript contains trailing data.
    TranscriptNotEmpty,
}

impl From<plonk::Error> for IvcError {
    fn from(e: plonk::Error) -> Self {
        IvcError::ProofGeneration(e)
    }
}

impl fmt::Display for IvcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IvcError::ProofGeneration(e) => write!(f, "proof generation failed: {e}"),
            IvcError::InvalidInstance => write!(f, "invalid instance"),
            IvcError::VkMismatch => write!(f, "verifying-key mismatch"),
            IvcError::InvalidProof => write!(f, "invalid proof"),
            IvcError::TranscriptNotEmpty => write!(f, "proof transcript not empty"),
        }
    }
}

impl std::error::Error for IvcError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            IvcError::ProofGeneration(e) => Some(e),
            _ => None,
        }
    }
}
