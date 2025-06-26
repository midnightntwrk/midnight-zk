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

//! Conversion instructions interface.
//!
//! It provides functions to convert between two types and their assigned
//! counterparts.
//!
//! The trait is parametrised by the source and target types, `AssignedSource`
//! and `AssignedTarget` respectively.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::types::InnerValue;

/// The set of circuit instructions for conversion operations.
pub trait ConversionInstructions<F, AssignedSource, AssignedTarget>
where
    F: PrimeField,
    AssignedSource: InnerValue,
    AssignedTarget: InnerValue,
{
    /// Converts an AssignedSource::Element into an AssignedTarget::Element,
    /// returns `None` if the conversion failed.
    // We choose to require this conversion at the chip level to have flexilibity.
    // Different chips may convert between the same types in different ways.
    // If that were not the case, we could alternatively perform the conversion at
    // the type level.
    fn convert_value(&self, x: &AssignedSource::Element) -> Option<AssignedTarget::Element>;

    /// Converts an AssignedSource into an AssignedTarget.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let bit: AssignedBit<F> = chip.assign(&mut layouter, Value::known(true))?;
    /// let val: AssignedNative<F> = chip.convert(&mut layouter, &bit)?;
    /// # });
    /// ```
    fn convert(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSource,
    ) -> Result<AssignedTarget, Error>;
}

/// The set of circuit instructions for unsafe conversion operations.
pub trait UnsafeConversionInstructions<F, AssignedSource, AssignedTarget>:
    ConversionInstructions<F, AssignedSource, AssignedTarget>
where
    F: PrimeField,
    AssignedSource: InnerValue,
    AssignedTarget: InnerValue,
{
    /// Converts an AssignedSource element into an AssignedTarget one.
    /// Potentially more efficient than `convert`, but see the warning below.
    ///
    /// # WARNING
    ///
    /// This function does not guarantee that the target object is built
    /// correctly. Make sure you know what you are doing if you use this
    /// function, e.g. you know that the source element has been sufficiently
    /// restricted so that the resulting target element is properly constrained.
    fn convert_unsafe(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedSource,
    ) -> Result<AssignedTarget, Error>;
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    pub enum Operation {
        Convert,
        UnsafeConvert,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, AssignedSource, AssignedTarget, ConversionChip>
    where
        AssignedSource: InnerValue,
        AssignedTarget: InnerValue,
    {
        x: AssignedSource::Element,
        expected: Option<AssignedTarget::Element>,
        operation: Operation,
        _marker: PhantomData<(F, AssignedSource, AssignedTarget, ConversionChip)>,
    }

    impl<F, AssignedSource, AssignedTarget, ConversionChip> Circuit<F>
        for TestCircuit<F, AssignedSource, AssignedTarget, ConversionChip>
    where
        F: PrimeField,
        AssignedSource: InnerValue,
        AssignedTarget: InnerValue,
        AssignedSource::Element: Clone + Default,
        AssignedTarget::Element: Clone + Default,
        ConversionChip: ConversionInstructions<F, AssignedSource, AssignedTarget>
            + UnsafeConversionInstructions<F, AssignedSource, AssignedTarget>
            + AssignmentInstructions<F, AssignedSource>
            + AssertionInstructions<F, AssignedTarget>
            + FromScratch<F>,
    {
        type Config = <ConversionChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            ConversionChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = ConversionChip::new_from_scratch(&config);

            let x = chip.assign(&mut layouter, Value::known(self.x.clone()))?;

            let y = match self.operation {
                Operation::Convert => chip.convert(&mut layouter, &x),
                Operation::UnsafeConvert => chip.convert_unsafe(&mut layouter, &x),
            }?;

            if let Some(expected) = self.expected.clone() {
                chip.assert_equal_to_fixed(&mut layouter, &y, expected)?;
            }

            Ok(())
        }
    }

    pub fn run<F, AssignedSource, AssignedTarget, ConversionChip>(
        x: AssignedSource::Element,
        expected: Option<AssignedTarget::Element>,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        AssignedSource: InnerValue,
        AssignedSource::Element: Clone + Default,
        AssignedTarget: InnerValue,
        AssignedTarget::Element: Clone + Default,
        ConversionChip: ConversionInstructions<F, AssignedSource, AssignedTarget>
            + UnsafeConversionInstructions<F, AssignedSource, AssignedTarget>
            + AssignmentInstructions<F, AssignedSource>
            + AssertionInstructions<F, AssignedTarget>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, AssignedSource, AssignedTarget, ConversionChip> {
            x,
            expected,
            operation,
            _marker: PhantomData,
        };
        let log2_nb_rows = 5;
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, op_name, 0, circuit);
        }
    }
}
