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

//! Zero instructions interface.
//!
//! It provides an interface for comparing assigned values with zero.
//!
//! Implementors of this trait need to implement [AssertionInstructions]
//! and [EqualityInstructions]. The trait is parametrized by `assigned`
//! values that implement `InnerConstants`, which gives access to zero.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    instructions::{AssertionInstructions, EqualityInstructions},
    types::{AssignedBit, InnerConstants},
};

/// The set of circuit instructions for zero equality and assertions.
pub trait ZeroInstructions<F, Assigned>:
    AssertionInstructions<F, Assigned> + EqualityInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: InnerConstants,
{
    /// Enforces that the given assigned element is zero.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    ///
    /// // we can now assert that the value is zero (this, obviously, discloses the value)
    /// chip.assert_zero(&mut layouter, &x)?;
    /// # });
    /// ```
    fn assert_zero(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<(), Error> {
        self.assert_equal_to_fixed(layouter, x, Assigned::inner_zero())
    }

    /// Asserts that the given element is non-zero.
    fn assert_non_zero(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<(), Error> {
        self.assert_not_equal_to_fixed(layouter, x, Assigned::inner_zero())
    }

    /// Returns `1` iff the given element equals zero (the additive identity).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    ///
    /// // the following value should be constrained further
    /// let cond: AssignedBit<F> = chip.is_zero(&mut layouter, &x)?;
    /// # });
    /// ```
    fn is_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
    ) -> Result<AssignedBit<F>, Error> {
        self.is_equal_to_fixed(layouter, x, Assigned::inner_zero())
    }
}

#[cfg(test)]
pub mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::AssignmentInstructions,
        testing_utils::{FromScratch, Sampleable},
        types::{AssignedNative, InnerValue},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum Operation {
        Assert,
        AssertNon,
        IsZero,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, ZeroChip>
    where
        Assigned: InnerValue,
    {
        x: Assigned::Element,
        expected: Option<bool>,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, ZeroChip)>,
    }

    impl<F, Assigned, ZeroChip> Circuit<F> for TestCircuit<F, Assigned, ZeroChip>
    where
        F: PrimeField,
        Assigned: InnerConstants,
        ZeroChip:
            ZeroInstructions<F, Assigned> + AssignmentInstructions<F, Assigned> + FromScratch<F>,
    {
        type Config = <ZeroChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            let constants_column = meta.fixed_column();
            meta.enable_constant(constants_column);
            ZeroChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = ZeroChip::new_from_scratch(&config);
            ZeroChip::load_from_scratch(&mut layouter, &config);

            let x = chip.assign_fixed(&mut layouter, self.x.clone())?;
            match self.operation {
                Operation::Assert => chip.assert_zero(&mut layouter, &x),
                Operation::AssertNon => chip.assert_non_zero(&mut layouter, &x),
                Operation::IsZero => {
                    let res = chip.is_zero(&mut layouter, &x)?;
                    let res_as_value: AssignedNative<F> = res.into();
                    layouter.assign_region(
                        || "assert contains fixed",
                        |mut region| {
                            region.constrain_constant(
                                res_as_value.cell(),
                                if self.expected.unwrap() {
                                    F::ONE
                                } else {
                                    F::ZERO
                                },
                            )
                        },
                    )
                }
            }
        }
    }

    fn run<F, Assigned, ZeroChip>(
        x: &Assigned::Element,
        expected: Option<bool>,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerConstants,
        ZeroChip:
            ZeroInstructions<F, Assigned> + AssignmentInstructions<F, Assigned> + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, ZeroChip> {
            x: x.clone(),
            expected,
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

    pub fn test_zero_assertions<F, Assigned, ZeroChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerConstants + Sampleable,
        ZeroChip:
            ZeroInstructions<F, Assigned> + AssignmentInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let mut cost_model = true;
        [
            (Assigned::sample_inner(&mut rng), false),
            (Assigned::inner_zero(), true),
            (Assigned::inner_one(), false),
        ]
        .into_iter()
        .for_each(|(x, is_zero)| {
            run::<F, Assigned, ZeroChip>(
                &x,
                None,
                Operation::Assert,
                is_zero,
                cost_model,
                name,
                "assert_zero",
            );
            run::<F, Assigned, ZeroChip>(
                &x,
                None,
                Operation::AssertNon,
                !is_zero,
                cost_model,
                name,
                "assert_non_zero",
            );
            cost_model = false;
        });
    }

    pub fn test_is_zero<F, Assigned, ZeroChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerConstants + Sampleable,
        ZeroChip:
            ZeroInstructions<F, Assigned> + AssignmentInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let mut cost_model = true;
        [
            (Assigned::sample_inner(&mut rng), false),
            (Assigned::inner_zero(), true),
            (Assigned::inner_one(), false),
        ]
        .into_iter()
        .for_each(|(x, expected)| {
            run::<F, Assigned, ZeroChip>(
                &x,
                Some(expected),
                Operation::IsZero,
                true,
                cost_model,
                name,
                "is_zero",
            );
            run::<F, Assigned, ZeroChip>(
                &x,
                Some(!expected),
                Operation::IsZero,
                false,
                false,
                "",
                "",
            );
            cost_model = false;
        });
    }
}
