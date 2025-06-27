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

//! Field instructions interface.

use ff::{Field, PrimeField};
use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use super::PublicInputInstructions;
use crate::{
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        EqualityInstructions, ZeroInstructions,
    },
    types::{AssignedBit, InnerConstants, Instantiable},
    utils::util::qnr,
};

/// The set of circuit instructions for field operations.
pub trait FieldInstructions<F, Assigned>:
    AssignmentInstructions<F, Assigned>
    + PublicInputInstructions<F, Assigned>
    + AssertionInstructions<F, Assigned>
    + ArithInstructions<F, Assigned>
    + EqualityInstructions<F, Assigned>
    + ZeroInstructions<F, Assigned>
    + ControlFlowInstructions<F, Assigned>
    + AssignmentInstructions<F, AssignedBit<F>>
where
    F: PrimeField,
    Assigned::Element: PrimeField,
    Assigned: Instantiable<F> + InnerConstants + Clone,
{
    /// The field order.
    fn order(&self) -> BigUint;

    /// Assert that the given input is a quadratic residue of the field.
    /// This is done by exhibiting a square root.
    fn assert_qr(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<(), Error> {
        let sqrt_x_value = x
            .value()
            .map(|x| Assigned::Element::sqrt(&x).expect("a quadratic residue"));

        let sqrt_x = self.assign(layouter, sqrt_x_value)?;
        let sqr = self.mul(layouter, &sqrt_x, &sqrt_x, None)?;
        self.assert_equal(layouter, &sqr, x)
    }

    /// Returns `1` if the given input is a quadratic residue and `0` otherwise.
    fn is_square(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
    ) -> Result<AssignedBit<F>, Error> {
        let is_square_value = x.value().map(|x| bool::from(x.sqrt().is_some()));
        let is_square = self.assign(layouter, is_square_value)?;

        // x is a quadratic residue iff x * qnr is not.
        let x_times_qnr = self.mul_by_constant(layouter, x, qnr::<Assigned::Element>())?;
        let y = self.select(layouter, &is_square, x, &x_times_qnr)?;

        self.assert_qr(layouter, &y)?;

        Ok(is_square)
    }
}
