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

//! Range-check and comparison instructions interface.
//!
//! It provides functions to compare assigned values with other assigned
//! values or fixed elements.
//!
//! Comparisons are defined by comparing the *interger representation* of field
//! elements and assumes we only compare "small" integers, i.e. all elements are
//! bounded. The maximum allowed bound is implementation specific and should be
//! at most 2^{F::NUM_BITS/2 - 1} to avoid breaking "natural" properties of
//! comparison

use std::{fmt::Debug, ops::Add};

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    field::AssignedBounded,
    instructions::BinaryInstructions,
    types::{AssignedBit, InnerValue},
};

/// The set of circuit instructions for comparison operations.
pub trait ComparisonInstructions<F, Assigned>: Clone + Debug + BinaryInstructions<F>
where
    F: PrimeField,
    Assigned: InnerValue,
    Assigned::Element: From<u64> + Add<Output = Assigned::Element>,
{
    /// All numbers involved in comparisons should be in the range [0,
    /// 2^{MAX_BOUND_IN_BITS}) and no comparison should be allowed for some
    /// bound > MAX_BOUND_IN_BITS.
    const MAX_BOUND_IN_BITS: u32;

    /// Converts an assigned element into an assigned bounded element.
    /// The circuit becomes unsatisfiable if the element value is not in [0,
    /// 2^{bound_in_bits}).
    fn bounded_of_element(
        &self,
        layouter: &mut impl Layouter<F>,
        n: usize,
        x: &Assigned,
    ) -> Result<AssignedBounded<F>, Error>;

    /// Converts an assigned bounded element into an assigned element with the
    /// same value.
    fn element_of_bounded(
        &self,
        layouter: &mut impl Layouter<F>,
        bounded: &AssignedBounded<F>,
    ) -> Result<Assigned, Error>;

    /// Returns `true` iff the given assigned element is strictly lower than the
    /// given bound.
    fn lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        bound: Assigned::Element,
    ) -> Result<AssignedBit<F>, Error>;

    /// Returns `true` iff the given assigned element is strictly greater than
    /// the given bound.
    fn greater_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        bound: Assigned::Element,
    ) -> Result<AssignedBit<F>, Error> {
        let b = self.leq_fixed(layouter, x, bound)?;
        self.not(layouter, &b)
    }

    /// Returns `true1` iff the given assigned element is lower than or equal to
    /// the given bound.
    fn leq_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        bound: Assigned::Element,
    ) -> Result<AssignedBit<F>, Error> {
        self.lower_than_fixed(layouter, x, bound + Assigned::Element::from(1))
    }

    /// Returns `true` iff the given assigned element is greater than or equal
    /// to the given bound.
    fn geq_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        bound: Assigned::Element,
    ) -> Result<AssignedBit<F>, Error> {
        let b = self.lower_than_fixed(layouter, x, bound)?;
        self.not(layouter, &b)
    }

    /// Returns `true` iff `x < y`.
    ///
    /// The following example will make the circuit unsatisfiable
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::from(276u64)))?;
    /// let y: AssignedNative<F> = chip.assign(&mut layouter, Value::known(F::from(313u64)))?;
    ///
    /// let x: AssignedBounded<F> = chip.bounded_of_element(&mut layouter, 16, &x)?;
    /// let y: AssignedBounded<F> = chip.bounded_of_element(&mut layouter, 16, &y)?;
    ///
    /// let check = chip.lower_than(&mut layouter, &x, &y)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &check, true)?;
    /// # });
    /// ```
    fn lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error>;

    /// Returns `true` iff `x > y`.
    fn greater_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let b = self.leq(layouter, x, y)?;
        self.not(layouter, &b)
    }

    /// Returns `true` iff `x <= y`.
    fn leq(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error>;

    /// Returns `true` iff `x >= y`.
    fn geq(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBounded<F>,
        y: &AssignedBounded<F>,
    ) -> Result<AssignedBit<F>, Error>;
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
    use rand::{RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions, DecompositionInstructions},
        testing_utils::FromScratch,
        types::{InnerConstants, Instantiable},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum Op {
        BoundedOfElement,
        LeqFixed,
        GeqFixed,
        LowerFixed,
        GreaterFixed,
        Leq,
        Geq,
        Lower,
        Greater,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, Chip>
    where
        Assigned: InnerValue,
    {
        n: usize,
        x: Assigned::Element,
        y: Assigned::Element,
        expected: bool,
        operation: Op,
        _marker: PhantomData<(F, Assigned, Chip)>,
    }

    impl<F, Assigned, Chip> Circuit<F> for TestCircuit<F, Assigned, Chip>
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone + Debug,
        Chip: AssignmentInstructions<F, Assigned>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + ComparisonInstructions<F, Assigned>
            + DecompositionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = <Chip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            Chip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = Chip::new_from_scratch(&config);
            Chip::load_from_scratch(&mut layouter, &config);

            let x = chip.assign(&mut layouter, Value::known(self.x))?;

            match self.operation {
                Op::BoundedOfElement => {
                    chip.bounded_of_element(&mut layouter, self.n, &x)?;
                    Ok(())
                }
                _ => {
                    let assigned_x = {
                        let x = chip.assign(&mut layouter, Value::known(self.x))?;
                        chip.bounded_of_element(&mut layouter, self.n, &x)?
                    };
                    let assigned_y = {
                        let y = chip.assign(&mut layouter, Value::known(self.y))?;
                        chip.bounded_of_element(&mut layouter, self.n, &y)?
                    };
                    let b = match self.operation {
                        Op::Leq => chip.leq(&mut layouter, &assigned_x, &assigned_y),
                        Op::Geq => chip.geq(&mut layouter, &assigned_x, &assigned_y),
                        Op::Lower => chip.lower_than(&mut layouter, &assigned_x, &assigned_y),
                        Op::Greater => chip.greater_than(&mut layouter, &assigned_x, &assigned_y),
                        Op::LeqFixed => chip.leq_fixed(&mut layouter, &assigned_x, self.y),
                        Op::GeqFixed => chip.geq_fixed(&mut layouter, &assigned_x, self.y),
                        Op::LowerFixed => chip.lower_than_fixed(&mut layouter, &assigned_x, self.y),
                        Op::GreaterFixed => {
                            chip.greater_than_fixed(&mut layouter, &assigned_x, self.y)
                        }
                        _ => unreachable!(),
                    }?;

                    let expected = chip.assign_fixed(&mut layouter, self.expected)?;
                    chip.assert_equal(&mut layouter, &b, &expected)
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, Chip>(
        x: u64,
        y: u64,
        expected: bool,
        n: usize,
        operation: Op,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone + Debug,
        Chip: AssignmentInstructions<F, Assigned>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + ComparisonInstructions<F, Assigned>
            + DecompositionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, Chip> {
            x: Assigned::Element::from(x),
            y: Assigned::Element::from(y),
            expected,
            n,
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

    pub fn test_lower_and_greater<F, Assigned, Chip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone + Debug,
        Chip: AssignmentInstructions<F, Assigned>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + ComparisonInstructions<F, Assigned>
            + DecompositionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let x = rng.next_u64();
        let y = rng.next_u64();
        let m = u64::MAX;
        let mut cost_model = true;
        [
            (x, x),
            (x, y),
            (y, x),
            (x, m),
            (m, x),
            (m - 1, m),
            (m, m - 1),
            (m, m),
            (0, 0),
            (0, 1),
            (1, 0),
            (0, 2),
            (1, 2),
            (2, 2),
            (2, 1),
        ]
        .into_iter()
        .for_each(|(x, y)| {
            // Positive
            run::<F, Assigned, Chip>(x, y, x >= y, 64, Op::Geq, true, cost_model, name, "geq");
            run::<F, Assigned, Chip>(x, y, x <= y, 64, Op::Leq, true, cost_model, name, "leq");
            run::<F, Assigned, Chip>(x, y, x < y, 64, Op::Lower, true, cost_model, name, "lower");
            run::<F, Assigned, Chip>(
                x,
                y,
                x > y,
                64,
                Op::Greater,
                true,
                cost_model,
                name,
                "greater",
            );
            run::<F, Assigned, Chip>(
                x,
                y,
                x <= y,
                64,
                Op::LeqFixed,
                true,
                cost_model,
                name,
                "leq_fixed",
            );
            run::<F, Assigned, Chip>(
                x,
                y,
                x >= y,
                64,
                Op::GeqFixed,
                true,
                cost_model,
                name,
                "geq_fixed",
            );
            run::<F, Assigned, Chip>(
                x,
                y,
                x < y,
                64,
                Op::LowerFixed,
                true,
                cost_model,
                name,
                "lower_fixed",
            );
            run::<F, Assigned, Chip>(
                x,
                y,
                x > y,
                64,
                Op::GreaterFixed,
                true,
                cost_model,
                name,
                "greater_fixed",
            );
            cost_model = false;
            // Negative
            run::<F, Assigned, Chip>(x, y, x > y, 64, Op::Leq, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x < y, 64, Op::Geq, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x >= y, 64, Op::Lower, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x <= y, 64, Op::Greater, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x > y, 64, Op::LeqFixed, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x < y, 64, Op::GeqFixed, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x >= y, 64, Op::LowerFixed, false, false, "", "");
            run::<F, Assigned, Chip>(x, y, x <= y, 64, Op::GreaterFixed, false, false, "", "");
        })
    }

    pub fn test_assert_bounded_element<F, Assigned, Chip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone + Debug,
        Chip: AssignmentInstructions<F, Assigned>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + ComparisonInstructions<F, Assigned>
            + DecompositionInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let x = rng.next_u64();
        let m = u64::MAX;
        let mut cost_model = true;
        [
            (x, 64, true),
            (m, 64, true),
            (m, 63, false),
            (0, 1, true),
            (0, 2, true),
            (2, 1, false),
            (2, 2, true),
            (7, 3, true),
            (8, 3, false),
            (15, 4, true),
            (16, 4, false),
            ((1 << 20) - 1, 20, true),
            (1 << 20, 20, false),
        ]
        .into_iter()
        .for_each(|(x, bound, must_pass)| {
            run::<F, Assigned, Chip>(
                x,
                u64::default(),
                bool::default(),
                bound,
                Op::BoundedOfElement,
                must_pass,
                cost_model,
                name,
                "bounded_of_element",
            );
            cost_model = false;
        })
    }
}
