// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
    /// The provided witness is invalid.
    InvalidWitness(String),
    /// The instance's VK representation does not match the verifier's key.
    VkMismatch,
    /// The proof is invalid (accumulator pairing check failed).
    InvalidProof,
    /// The proof transcript contains trailing data.
    TranscriptNotEmpty,
    /// The application-level decider check failed.
    DeciderFailed,
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
            IvcError::InvalidWitness(msg) => write!(f, "invalid witness: {msg}"),
            IvcError::VkMismatch => write!(f, "verifying-key mismatch"),
            IvcError::InvalidProof => write!(f, "invalid proof"),
            IvcError::TranscriptNotEmpty => write!(f, "proof transcript not empty"),
            IvcError::DeciderFailed => write!(f, "decider check failed"),
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
