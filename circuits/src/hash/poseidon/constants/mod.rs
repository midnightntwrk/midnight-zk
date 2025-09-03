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

pub use ff::PrimeField;

/// Length of Poseidon's state.
pub(crate) const WIDTH: usize = 3;

/// Hash rate of Poseidon.
pub(crate) const RATE: usize = 2;

/// Number of full rounds of the Poseidon permutation.
pub(crate) const NB_FULL_ROUNDS: usize = 8;

/// Number of partial rounds of the Poseidon permutation.
pub(crate) const NB_PARTIAL_ROUNDS: usize = 60;

/// A PrimeField with the constants needed to compute Poseidon's permutation
/// (MDS matrix and round constants).
pub trait PoseidonField: PrimeField {
    /// The MDS matrix used for the linear layer at each round of Poseidon.
    const MDS: [[Self; WIDTH]; WIDTH];

    /// The constants added to Poseidon's state on every round.
    const ROUND_CONSTANTS: [[Self; WIDTH]; NB_FULL_ROUNDS + NB_PARTIAL_ROUNDS];
}

mod blstrs;
