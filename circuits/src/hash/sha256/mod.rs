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

mod sha256_chip;
mod types;
mod utils;

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};
use sha2::Digest;
pub use sha256_chip::{Sha256Chip, Sha256Config, NB_SHA256_ADVICE_COLS, NB_SHA256_FIXED_COLS};

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
        let mut output_bytes = Vec::with_capacity(32);

        // We convert each `AssignedPlain<32>` returned by `self.sha256` into 4 bytes.
        for word in self.sha256(layouter, inputs)? {
            let bytes = (self.native_gadget).assigned_to_be_bytes(layouter, &word.0, Some(4))?;
            output_bytes.extend(bytes)
        }

        Ok(output_bytes.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use midnight_curves::Fq as Scalar;

    use crate::{
        field::NativeGadget, hash::sha256::Sha256Chip, instructions::hash::tests::test_hash,
        types::AssignedByte,
    };

    #[test]
    fn test_sha_hash() {
        test_hash::<
            Scalar,
            AssignedByte<Scalar>,
            [AssignedByte<Scalar>; 32],
            Sha256Chip<Scalar>,
            NativeGadget<Scalar, _, _>,
        >(true, "SHA256", 15);
    }
}
