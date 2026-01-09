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

use midnight_circuits::{
    field::{decomposition::chip::P2RDecompositionChip, AssignedNative, NativeChip, NativeGadget},
    instructions::{
        AssertionInstructions, AssignmentInstructions, ConversionInstructions,
        UnsafeConversionInstructions,
    },
    types::AssignedByte,
};
use midnight_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
    utils::rational::Rational,
};

pub mod blake2b;
pub mod keccak_sha3;

/// Native gadget shortcut.
type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

/// Converts a slice of assigned cell to a slice of Midnight `AssignedByte<F>`.
/// This function is unsafe in that it assumes that the values have
/// been properly range-checked.
fn unsafe_convert_to_bytes<V, F>(
    layouter: &mut impl Layouter<F>,
    native_gadget: &NG<F>,
    bytes: &[AssignedCell<V, F>],
) -> Result<Vec<AssignedByte<F>>, Error>
where
    F: ff::PrimeField,
    V: Clone,
    for<'v> Rational<F>: From<&'v V>,
{
    (bytes.iter())
        .map(|b| native_gadget.convert_unsafe(layouter, &b.clone().convert_to_native()))
        .collect()
}

/// Converts a slice of assigned cell to a slice of Midnight `AssignedByte<F>`.
/// This function is re-range checks the cells. Although redundant, it ensures
/// that a potential soundness issue in the external chip does not allow to end
/// up with unsound `AssignedByte` elements in our library (which could
/// potentially break other chips).
fn convert_to_bytes<V, F>(
    layouter: &mut impl Layouter<F>,
    native_gadget: &NG<F>,
    bytes: &[AssignedCell<V, F>],
) -> Result<Vec<AssignedByte<F>>, Error>
where
    F: ff::PrimeField,
    V: Clone,
    for<'v> Rational<F>: From<&'v V>,
{
    let bytes_as_native: &[AssignedNative<F>] =
        &bytes.iter().map(|b| b.convert_to_native()).collect::<Vec<_>>();

    // Instead of using `native_gadget.convert` on each individual cell, we extract
    // their value, reassign them in a batched way using `assign_many` (more
    // efficient), and assert equality with the original vector.
    let extracted_bytes = bytes_as_native
        .iter()
        .map(|b| {
            b.value().map(|b| {
                <NG<F> as ConversionInstructions<_, _, AssignedByte<F>>>::convert_value(
                    native_gadget,
                    b,
                )
                .expect("there is visibly a soundness issue in the range checks of an external implementation (found a byte overflowing 2^8).")
            })
        })
        .collect::<Vec<_>>();
    let reassigned_bytes: Vec<AssignedByte<F>> =
        native_gadget.assign_many(layouter, &extracted_bytes)?;
    for (x, y) in reassigned_bytes.iter().zip(bytes_as_native.iter()) {
        native_gadget.assert_equal(layouter, &AssignedNative::<F>::from(x), y)?;
    }
    Ok(reassigned_bytes)
}
