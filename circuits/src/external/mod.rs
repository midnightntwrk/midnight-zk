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

//! Imports of third-party implementations of circuits. External libraries
//! remain largely independent code bases, in that they may depend on
//! `midnight-proofs`, but not `midnight-circuits`. For their return type to
//! match that of `midnight-circuits`, unsafe type conversions are performed.

use midnight_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
    utils::rational::Rational,
};

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    instructions::{ConversionInstructions, UnsafeConversionInstructions},
    types::{AssignedByte, InnerValue},
};

pub mod blake2b;
pub mod keccak;

/// Native gadget shortcut.
type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// Converts a slice of assigned cell to a slice of Midnight `AssignedByte<F>`.
/// This function is re-range checks the cells. Although redundant, it ensures
/// that a potential soundness issue in the external chip does not propagade to
/// our library.
fn convert_to_bytes<V, F>(
    layouter: &mut impl Layouter<F>,
    native_gadget: &NG<F>,
    bytes: &[AssignedCell<V, F>],
) -> Result<Vec<AssignedByte<F>>, Error>
where
    F: ff::PrimeField,
    V: Clone + Into<u8>,
    for<'v> Rational<F>: From<&'v V>,
{
    (bytes.iter())
        .map(|b| native_gadget.convert(layouter, &b.clone().convert_to_native()))
        .collect::<Result<Vec<AssignedByte<F>>, Error>>()
}
