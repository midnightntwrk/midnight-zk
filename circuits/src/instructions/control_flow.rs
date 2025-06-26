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

//! Control flow instructions interface.
//!
//! It provides functions for conditionally selecting and asserting equality a
//! pair of `Assigned` elements.
//!
//! The trait is parametrized by `Assigned` type.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use super::AssertionInstructions;
use crate::types::{AssignedBit, InnerValue};

/// The set of circuit instructions for control flow operations.
pub trait ControlFlowInstructions<F: PrimeField, Assigned>:
    AssertionInstructions<F, Assigned>
where
    Assigned: InnerValue,
{
    /// Returns `x` if `cond = true` and `y` otherwise.
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// let y: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ONE))?;
    /// let cond: AssignedBit<F> = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let choice = chip.select(&mut layouter, &cond, &x, &y)?;
    /// chip.assert_equal(&mut layouter, &choice, &x)?;
    /// # });
    /// ```
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error>;

    /// Equality assertion only if `cond` is set to `1`.
    fn cond_assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(), Error> {
        let x = self.select(layouter, cond, x, y)?;
        self.assert_equal(layouter, &x, y)
    }

    /// Swaps two elements `x` and `y` only if `cond` is set to `1`.
    fn cond_swap(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(Assigned, Assigned), Error> {
        let new_x = self.select(layouter, cond, y, x)?;
        let new_y = self.select(layouter, cond, x, y)?;

        Ok((new_x, new_y))
    }
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, Column, ConstraintSystem, Fixed},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::{FromScratch, Sampleable},
        types::InnerValue,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum Operation {
        Select,
        CondAssertEqual,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, ControlFlowChip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        y: Assigned::Element,
        cond: bool,
        expected: Assigned::Element,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, ControlFlowChip)>,
    }

    impl<F, Assigned, ControlFlowChip> Circuit<F> for TestCircuit<F, Assigned, ControlFlowChip>
    where
        F: PrimeField,
        Assigned: InnerValue,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = (<ControlFlowChip as FromScratch<F>>::Config, Column<Fixed>);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let fixed_column = meta.fixed_column();
            meta.enable_equality(fixed_column);
            (
                ControlFlowChip::configure_from_scratch(
                    meta,
                    &[committed_instance_column, instance_column],
                ),
                fixed_column,
            )
        }

        fn synthesize(
            &self,
            (config, fixed_column): Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = ControlFlowChip::new_from_scratch(&config);
            ControlFlowChip::load_from_scratch(&mut layouter, &config);

            let x = chip.assign_fixed(&mut layouter, self.x.clone())?;
            let y = chip.assign_fixed(&mut layouter, self.y.clone())?;
            let cond_value = layouter.assign_region(
                || "Assign fixed",
                |mut region| {
                    region.assign_fixed(
                        || "cond value",
                        fixed_column,
                        0,
                        || Value::known(if self.cond { F::ONE } else { F::ZERO }),
                    )
                },
            )?;

            let cond = AssignedBit(cond_value);

            match self.operation {
                Operation::Select => {
                    let res = chip.select(&mut layouter, &cond, &x, &y)?;
                    chip.assert_equal_to_fixed(&mut layouter, &res, self.expected.clone())
                }
                Operation::CondAssertEqual => chip.cond_assert_equal(&mut layouter, &cond, &x, &y),
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, ControlFlowChip>(
        x: &Assigned::Element,
        y: &Assigned::Element,
        cond: bool,
        expected: &Assigned::Element,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, ControlFlowChip> {
            x: x.clone(),
            y: y.clone(),
            cond,
            expected: expected.clone(),
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

    pub fn test_select<F, Assigned, ControlFlowChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue + Sampleable,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let x = Assigned::sample_inner(&mut rng);
        let y = Assigned::sample_inner(&mut rng);
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            true,
            &x,
            Operation::Select,
            true,
            true,
            name,
            "select",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            false,
            &y,
            Operation::Select,
            true,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            true,
            &y,
            Operation::Select,
            false,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            false,
            &x,
            Operation::Select,
            false,
            false,
            "",
            "",
        );
    }

    pub fn test_cond_assert_equal<F, Assigned, ControlFlowChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue + Sampleable,
        Assigned::Element: Default,
        ControlFlowChip: ControlFlowInstructions<F, Assigned>
            + AssignmentInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let x = Assigned::sample_inner(&mut rng);
        let y = Assigned::sample_inner(&mut rng);
        let none = Assigned::Element::default();
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &x,
            true,
            &none,
            Operation::CondAssertEqual,
            true,
            true,
            name,
            "cond_assert_equal",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &x,
            false,
            &none,
            Operation::CondAssertEqual,
            true,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            false,
            &none,
            Operation::CondAssertEqual,
            true,
            false,
            "",
            "",
        );
        run::<F, Assigned, ControlFlowChip>(
            &x,
            &y,
            true,
            &none,
            Operation::CondAssertEqual,
            false,
            false,
            "",
            "",
        );
    }
}
