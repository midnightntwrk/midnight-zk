// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

//! SHA256 instructions interface.
//!
//! This interface is not exposed directly to the user. Instead, we expose
//! SHA functionality via the [crate::hash::sha256::Sha256] gadget.

use std::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter},
    plonk::Error,
};

use super::{AssignedBlockWord, BLOCK_SIZE, DIGEST_SIZE};

/// The set of circuit instructions required to use the
/// [Sha256](crate::hash::sha256::Sha256) gadget.
pub trait Sha256Instructions<F: PrimeField>: Chip<F> + Clone + Debug {
    /// Variable representing the SHA-256 internal state.
    type State: Clone + Debug;

    /// Places the SHA-256 IV in the circuit, returning the initial state
    /// variable.
    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error>;

    /// Creates an initial state from the output state of a previous block
    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state, processes a block of input
    /// and returns the final state.
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [AssignedBlockWord<F>; BLOCK_SIZE],
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state applies padding,
    /// processes the final blocks of input and returns the final state.
    /// There are exactly:
    /// - two blocks if the padding starts at the 14 word and,
    /// - one block if the padding starts in the 15th or 16th word.
    ///
    /// Take also input the final length of the hash to apply the padding
    /// correctly
    fn apply_padding(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        block1: Option<[AssignedBlockWord<F>; BLOCK_SIZE]>,
        block2: [AssignedBlockWord<F>; BLOCK_SIZE],
        hash_input_length: u64,
    ) -> Result<Self::State, Error>;

    /// Returns the padding bytes.
    fn compute_padding(&self, hash_input_length: u64) -> Vec<u8>;

    /// Converts the given state into a message digest.
    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[AssignedBlockWord<F>; DIGEST_SIZE], Error>;
}
