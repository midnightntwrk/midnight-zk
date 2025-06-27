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

//! Assertion instructions interface.
//!
//! It provides functions for (dis)equality assertions for values of type
//! `Assigned` (a generic of this trait that implements [InnerValue]).
//! Furthermore, assertions between `Assigned` elements and fixed values of type
//! `Assigned::Element`.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::types::InnerValue;

/// The set of circuit instructions for assertion operations.
///
///
/// In the following examples, `chip` implements [AssertionInstructions]
/// for [AssignedNative](crate::types::AssignedNative),
/// [AssignedBit](crate::types::AssignedBit) and
/// [AssignedByte](crate::types::AssignedByte).
pub trait AssertionInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: InnerValue,
{
    /// Ensures that the given assigned elements are the same.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// chip.assert_equal(&mut layouter, &x, &x)?;
    /// # });
    /// ```
    ///
    /// The following should produce an unsatisfiable circuit.
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// let y: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ONE))?;
    /// chip.assert_equal(&mut layouter, &x, &y)?;
    /// # });
    /// ```
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(), Error>;

    /// Ensures that the given assigned elements are different.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedByte<F> = chip.assign(&mut layouter, Value::known(255u8))?;
    /// let y: AssignedByte<F> = chip.assign(&mut layouter, Value::known(0u8))?;
    /// chip.assert_not_equal(&mut layouter, &x, &y)?;
    /// # });
    /// ```
    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(), Error>;

    /// Ensures that the given assigned element is equal to the given constant.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ONE))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &x, F::ONE)?;
    /// # });
    /// ```
    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        constant: Assigned::Element,
    ) -> Result<(), Error>;

    /// Ensures that the given assigned element is different from the given
    /// constant.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedBit<F> = chip.assign(&mut layouter, Value::known(false))?;
    /// chip.assert_not_equal_to_fixed(&mut layouter, &x, true)?;
    /// # });
    /// ```
    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        constant: Assigned::Element,
    ) -> Result<(), Error>;
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
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::{FromScratch, Sampleable},
        types::InnerConstants,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum Operation {
        Eq,
        Neq,
        EqFixed,
        NeqFixed,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, AssertionChip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        y: Assigned::Element,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, AssertionChip)>,
    }

    impl<F, Assigned, AssertionChip> Circuit<F> for TestCircuit<F, Assigned, AssertionChip>
    where
        F: PrimeField,
        Assigned: InnerValue,
        Assigned::Element: Default,
        AssertionChip: AssertionInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = <AssertionChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            AssertionChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = AssertionChip::new_from_scratch(&config);
            AssertionChip::load_from_scratch(&mut layouter, &config);

            let x = chip.assign(&mut layouter, Value::known(self.x.clone()))?;
            let y = chip.assign_fixed(&mut layouter, self.y.clone())?;

            match self.operation {
                Operation::Eq => chip.assert_equal(&mut layouter, &x, &y),
                Operation::Neq => chip.assert_not_equal(&mut layouter, &x, &y),
                Operation::EqFixed => chip.assert_equal_to_fixed(&mut layouter, &x, self.y.clone()),
                Operation::NeqFixed => {
                    chip.assert_not_equal_to_fixed(&mut layouter, &x, self.y.clone())
                }
            }
        }
    }

    fn run<F, Assigned, AssertionChip>(
        x: &Assigned::Element,
        y: &Assigned::Element,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default,
        AssertionChip: AssertionInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, AssertionChip> {
            x: x.clone(),
            y: y.clone(),
            operation,
            _marker: PhantomData,
        };

        let log2_nb_rows = 10;
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

    pub fn test_assertions<F, Assigned, AssertionChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerConstants + Sampleable,
        Assigned::Element: Default,
        AssertionChip: AssertionInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let zero = Assigned::inner_zero();
        let one = Assigned::inner_one();
        let x = Assigned::sample_inner(&mut rng);
        let y = Assigned::sample_inner(&mut rng);
        let mut cost_model = true;
        [
            (&x, &x, true),
            (&x, &y, false),
            (&zero, &zero, true),
            (&zero, &one, false),
        ]
        .into_iter()
        .for_each(|(x, y, eq)| {
            run::<F, Assigned, AssertionChip>(
                x,
                y,
                Operation::Eq,
                eq,
                cost_model,
                name,
                "assert_eq",
            );
            run::<F, Assigned, AssertionChip>(
                x,
                y,
                Operation::Neq,
                !eq,
                cost_model,
                name,
                "assert_neq",
            );
            run::<F, Assigned, AssertionChip>(
                x,
                y,
                Operation::EqFixed,
                eq,
                cost_model,
                name,
                "assert_eq_fixed",
            );
            run::<F, Assigned, AssertionChip>(
                x,
                y,
                Operation::NeqFixed,
                !eq,
                cost_model,
                name,
                "assert_neq_fixed",
            );
            cost_model = false;
        });
    }
}
