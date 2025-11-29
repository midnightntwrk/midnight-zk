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

//! Import of the blake2b hash implementation from [Eryx](https://github.com/eryxcoop).

#[cfg(test)]
use blake2b::blake2b::blake2b_chip::Blake2bConfig;
#[cfg(test)]
use blake2b::blake2b::NB_BLAKE2B_ADVICE_COLS;
use blake2b::{blake2b::blake2b_chip::Blake2bChip, types::byte::Byte};
use ff::PrimeField;
#[cfg(test)]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};
use midnight_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};

#[cfg(test)]
use crate::testing_utils::FromScratch;
use crate::{
    external::{unsafe_convert_to_bytes, NG},
    field::AssignedNative,
    types::AssignedByte,
};

/// Blake2b hash.
pub fn hash<F: PrimeField>(
    chip: &Blake2bChip<F>,
    native_gadget: &NG<F>,
    layouter: &mut impl Layouter<F>,
    input: &[AssignedByte<F>],
    key: &[AssignedByte<F>],
    output_size: usize,
) -> Result<[AssignedByte<F>; 64], Error> {
    let input = &input.iter().map(AssignedNative::from).collect::<Vec<_>>();
    let key = &key.iter().map(AssignedNative::from).collect::<Vec<_>>();
    let output = &chip.hash(layouter, input, key, output_size)?.map(AssignedCell::<Byte, F>::from);
    Ok(unsafe_convert_to_bytes(layouter, native_gadget, output)?.try_into().unwrap())
}

