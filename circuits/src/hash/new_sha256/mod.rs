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

//! Implementation in-circuit of the SHA256 hash function.

#![allow(non_snake_case)]

mod gates;
mod sha256_chip;
mod types;
mod utils;

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};
use sha2::Digest;
pub use sha256_chip::{Sha256Chip, Sha256Config};

use crate::{
    instructions::{hash::HashCPU, DecompositionInstructions, HashInstructions},
    types::AssignedByte,
};

impl<F: PrimeField> HashCPU<u8, [u8; 32]> for Sha256Chip<F> {
    fn hash(inputs: &[u8]) -> [u8; 32] {
        let output = sha2::Sha256::digest(inputs);
        output.into_iter().collect::<Vec<_>>().try_into().unwrap()
    }
}

impl<F: PrimeField> HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 32]> for Sha256Chip<F> {
    fn hash(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        let output_words = self.sha256(layouter, inputs)?;

        // convert the assigned 32-bit words to assigned bytes in big-endian order
        let assigned_bytes = output_words
            .into_iter()
            .map(|word| {
                self.native_gadget
                    .assigned_to_be_bytes(layouter, &word.0, Some(4))
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        Ok(assigned_bytes.try_into().unwrap())
    }
}
