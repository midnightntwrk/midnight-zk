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

//! Import of the keccak variant of SHA, implementation from [Alexandros Zacharakis](https://github.com/alexandroszacharakis8).

use ff::PrimeField;
#[cfg(test)]
use keccak::packed_chip::{PackedConfig, PACKED_ADVICE_COLS, PACKED_FIXED_COLS};
use keccak::{packed_chip::PackedChip, sha3_256_gadget::Keccak256, KECCAK_SQUEEZE_BYTES};
#[cfg(test)]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

#[cfg(test)]
use crate::testing_utils::FromScratch;
use crate::{
    external::{unsafe_convert_to_bytes, NG},
    instructions::AssertionInstructions,
    types::{AssignedByte, InnerValue},
};

/// The chip for the external implementation of Keccak.
pub type KeccakChip<F> = Keccak256<F, PackedChip<F>>;

/// Wrapper for the main method of Keccak.
pub fn digest<F: PrimeField>(
    chip: &KeccakChip<F>,
    native_gadget: &NG<F>,
    layouter: &mut impl Layouter<F>,
    input: &[AssignedByte<F>],
) -> Result<[AssignedByte<F>; KECCAK_SQUEEZE_BYTES], Error> {
    // The Keccak implementation requires `Value<u8>` inputs, instead of assigned
    // bytes. We extract these values from `input`, and bridge the broken link with
    // `assert_equal` below.
    let raw_input = input.iter().map(|b| b.value()).collect::<Vec<Value<u8>>>();
    let (reassigned_input, digest) = chip.digest(layouter, &raw_input)?;

    // Rebuilding the broken link between the re-assigned input and the original
    // one. The unsafe conversion is sound since we are processing Keccak bytes.
    let reassigned_input = unsafe_convert_to_bytes(layouter, native_gadget, &reassigned_input)?;
    for (original_byte, reassigned_byte) in input.iter().zip(reassigned_input.iter()) {
        native_gadget.assert_equal(layouter, original_byte, reassigned_byte)?
    }
    // This check should not be necessary to put in-circuit, as it should be
    // reflected in the verification process.
    assert!(input.len() == reassigned_input.len());

    let digest = unsafe_convert_to_bytes(layouter, native_gadget, &digest)?;
    Ok(digest.try_into().unwrap())
}

