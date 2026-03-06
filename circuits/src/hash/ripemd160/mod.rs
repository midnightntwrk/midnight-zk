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

//! Implementation in-circuit of the RIPEMD-160 hash function.

#![allow(non_snake_case)]
mod ripemd160_chip;
mod types;
mod utils;

use midnight_proofs::{circuit::Layouter, plonk::Error};
use ripemd::Digest;
pub use ripemd160_chip::{
    RipeMD160Chip, RipeMD160Config, NB_RIPEMD160_ADVICE_COLS, NB_RIPEMD160_FIXED_COLS,
};

use crate::{
    instructions::{hash::HashCPU, DecompositionInstructions, HashInstructions},
    types::AssignedByte,
    CircuitField,
};

impl<F: CircuitField> HashCPU<u8, [u8; 20]> for RipeMD160Chip<F> {
    fn hash(inputs: &[u8]) -> [u8; 20] {
        let output = ripemd::Ripemd160::digest(inputs);
        output.into_iter().collect::<Vec<_>>().try_into().unwrap()
    }
}

impl<F: CircuitField> HashInstructions<F, AssignedByte<F>, [AssignedByte<F>; 20]>
    for RipeMD160Chip<F>
{
    fn hash(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 20], Error> {
        let mut output_bytes = Vec::with_capacity(20);

        // We convert each `AssignedWord` returned by `self.ripemd160` into 4 bytes.
        for word in self.ripemd160(layouter, inputs)? {
            let bytes = self.native_gadget.assigned_to_le_bytes(layouter, &word.0, Some(4))?;
            output_bytes.extend(bytes)
        }

        Ok(output_bytes.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use midnight_curves::Fq as Scalar;

    use crate::{
        field::NativeGadget, hash::ripemd160::RipeMD160Chip, instructions::hash::tests::test_hash,
        types::AssignedByte,
    };

    #[test]
    fn test_ripemd160_hash() {
        fn test_wrapper(input_size: usize, k: u32, cost_model: bool) {
            test_hash::<
                Scalar,
                AssignedByte<Scalar>,
                [AssignedByte<Scalar>; 20],
                RipeMD160Chip<Scalar>,
                NativeGadget<Scalar, _, _>,
            >(cost_model, "RIPEMD160", input_size, k)
        }

        const RIPEMD160_BLOCK_SIZE: usize = 64;
        const RIPEMD160_EDGE_PADDING: usize = 55;
        test_wrapper(2 * RIPEMD160_BLOCK_SIZE, 15, true);

        test_wrapper(RIPEMD160_BLOCK_SIZE, 14, false);
        test_wrapper(RIPEMD160_BLOCK_SIZE - 1, 14, false);
        test_wrapper(RIPEMD160_BLOCK_SIZE - 2, 14, false);
        test_wrapper(4 * RIPEMD160_BLOCK_SIZE, 15, false);

        test_wrapper(RIPEMD160_EDGE_PADDING, 14, false);
        test_wrapper(RIPEMD160_EDGE_PADDING - 1, 14, false);

        test_wrapper(0, 14, false);
        test_wrapper(1, 14, false);
        test_wrapper(2, 14, false);
    }
}
