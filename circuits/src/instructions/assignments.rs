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

//! Assignment instructions interface.
//!
//! It provides functions for assigning fixed and secret values into the
//! circuit.
//!
//! This trait is parametrized by the resulting `Assigned` type (a generic of
//! this trait that implements [InnerValue]). The assignment functions take an
//! `Assigned::Element` as input and return an `Assigned` value.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::types::InnerValue;

/// The set of circuit instructions for assignment operations.
pub trait AssignmentInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: InnerValue,
{
    /// Assigns an element as a private input to the circuit.
    ///
    /// In the following example, `chip` implements [AssignmentInstructions] for
    /// [AssignedNative](crate::types::AssignedNative).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// // we load a secret variable into the circuit, only the prover may know its value
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// # });
    /// ```
    ///
    /// But `chip` can also implement [AssignmentInstructions] for
    /// [AssignedBit](crate::types::AssignedBit) or
    /// [AssignedByte](crate::types::AssignedByte) and other types.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let bit: AssignedBit<F> = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let byte: AssignedByte<F> = chip.assign(&mut layouter, Value::known(42u8))?;
    /// # });
    /// ```
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Assigned::Element>,
    ) -> Result<Assigned, Error>;

    /// Assigns a fixed (constant) element.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// // we load a constant into the circuit, everyone knows the value of `k`
    /// let x: AssignedNative<F> = chip.assign_fixed(&mut layouter, F::ONE)?;
    ///
    /// // we can also assign fixed bits or bytes if the chip supports these types
    /// let bit: AssignedBit<F> = chip.assign_fixed(&mut layouter, false)?;
    /// let byte: AssignedByte<F> = chip.assign_fixed(&mut layouter, 255u8)?;
    /// # });
    /// ```
    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: Assigned::Element,
    ) -> Result<Assigned, Error>;

    /// Assigns several elements as private inputs to the circuit.
    ///
    /// This is potentially more efficient than calling
    /// [assign](AssignmentInstructions::assign) multiple times.
    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<Assigned::Element>],
    ) -> Result<Vec<Assigned>, Error> {
        values
            .iter()
            .map(|v| self.assign(layouter, v.clone()))
            .collect::<Result<Vec<Assigned>, Error>>()
    }

    /// Assigns several elements fixed values to the circuit.
    ///
    /// This is potentially more efficient than calling
    /// [assign_fixed](AssignmentInstructions::assign_fixed) multiple times.
    fn assign_many_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Assigned::Element],
    ) -> Result<Vec<Assigned>, Error> {
        values
            .iter()
            .map(|v| self.assign_fixed(layouter, v.clone()))
            .collect::<Result<Vec<Assigned>, Error>>()
    }
}
