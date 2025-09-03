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

//! Arithmetic instructions interface.
//!
//! It provides functions for performing arithmetic operations between assigned
//! values in the circuit.
//!
//! This trait is parametrized by a generic `Assigned` (required to implement
//! [InnerValue]) which defines the type over which the arithmetic operations
//! take place.

use std::{
    fmt::Debug,
    ops::{Add, Neg},
};

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    instructions::{AssertionInstructions, AssignmentInstructions},
    types::InnerValue,
};

/// The set of circuit instructions for arithmetic operations.
pub trait ArithInstructions<F, Assigned>:
    Clone + Debug + AssignmentInstructions<F, Assigned> + AssertionInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned::Element:
        PartialEq + From<u64> + Add<Output = Assigned::Element> + Neg<Output = Assigned::Element>,
    Assigned: InnerValue,
{
    /// Addition of many elements, given a slice of terms of the form
    /// `(coeff_i, x_i)` and a constant `k`, returns
    /// `k + (sum_i coeff_i * x_i)`.
    ///
    /// This function is potentially more efficient than folding over
    /// [add](ArithInstructions::add) and
    /// [mul_by_constant](ArithInstructions::mul_by_constant).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(1)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(2)))?;
    /// let z = chip.assign(&mut layouter, Value::known(F::from(3)))?;
    ///
    /// let res = chip.linear_combination(
    ///     &mut layouter,
    ///     &[(F::from(100), x), (F::from(10), y), (F::ONE, z)],
    ///     F::ZERO,
    /// )?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(123))?;
    /// # });
    /// ```
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(Assigned::Element, Assigned)],
        constant: Assigned::Element,
    ) -> Result<Assigned, Error>;

    /// Addition.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(2)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(3)))?;
    ///
    /// let res = chip.add(&mut layouter, &x, &y)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(5))?;
    /// # });
    /// ```
    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error> {
        self.linear_combination(
            layouter,
            &[
                (Assigned::Element::from(1), x.clone()),
                (Assigned::Element::from(1), y.clone()),
            ],
            Assigned::Element::from(0),
        )
    }

    /// Subtraction.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(2)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(3)))?;
    ///
    /// let res = chip.sub(&mut layouter, &x, &y)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, -F::ONE)?;
    /// # });
    /// ```
    fn sub(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error> {
        self.linear_combination(
            layouter,
            &[
                (Assigned::Element::from(1), x.clone()),
                (-Assigned::Element::from(1), y.clone()),
            ],
            Assigned::Element::from(0),
        )
    }

    /// Multiplication, possibly with an additional multiplying constant.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(2)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(3)))?;
    ///
    /// let res = chip.mul(&mut layouter, &x, &y, None)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(6))?;
    /// # });
    /// ```
    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
        multiplying_constant: Option<Assigned::Element>,
    ) -> Result<Assigned, Error>;

    /// Division.
    /// Division of `x` by `y` will make the circuit unsatisfiable if `y = 0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(15)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(3)))?;
    ///
    /// let res = chip.div(&mut layouter, &x, &y)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(5))?;
    /// # });
    /// ```
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let zero = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    ///
    /// let res = chip.div(&mut layouter, &zero, &zero)?;
    /// # });
    /// ```
    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error>;

    /// Negation (additive inverse).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(42)))?;
    ///
    /// let res = chip.neg(&mut layouter, &x)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, -F::from(42))?;
    /// # });
    /// ```
    fn neg(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<Assigned, Error> {
        self.linear_combination(
            layouter,
            &[(-Assigned::Element::from(1), x.clone())],
            Assigned::Element::from(0),
        )
    }

    /// Inversion (multiplicative inverse).
    /// The circuit will become unsatisfiable if `x = 0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(-F::ONE))?;
    ///
    /// let res = chip.inv(&mut layouter, &x)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, -F::ONE)?;
    /// # });
    /// ```
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let zero = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    ///
    /// let res = chip.inv(&mut layouter, &zero)?;
    /// # });
    /// ```
    fn inv(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<Assigned, Error>;

    /// Inversion (multiplicative inverse).
    /// If `x = 0`, this function returns `0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// // inv0 equals inv on non-zero values
    /// let x = chip.assign(&mut layouter, Value::known(F::from(5)))?;
    /// let res = chip.inv0(&mut layouter, &x)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(5).invert().unwrap())?;
    ///
    /// // inv0 of zero does not fail and returns zero
    /// let zero = chip.assign(&mut layouter, Value::known(F::ZERO))?;
    /// let res = chip.inv0(&mut layouter, &zero)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::ZERO)?;
    /// # });
    /// ```
    fn inv0(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<Assigned, Error>;

    /// Addition of a constant.
    ///
    /// This function is potentiallly more efficient than composing
    /// [assigned_fixed](AssignmentInstructions::assign_fixed) and
    /// [add](ArithInstructions::add).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// let res = chip.add_constant(&mut layouter, &x, F::from(3))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(10))?;
    /// # });
    /// ```
    fn add_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        constant: Assigned::Element,
    ) -> Result<Assigned, Error> {
        if constant == Assigned::Element::from(0) {
            return Ok(x.clone());
        }
        self.linear_combination(
            layouter,
            &[(Assigned::Element::from(1), x.clone())],
            constant,
        )
    }

    /// Pair-wise addition of a constant slice to a slice of assigned values.
    ///
    /// This function is potentially more efficient than several calls to
    /// [add_constant](ArithInstructions::add_constant).
    ///
    /// # Panics
    ///
    /// If the given slices do not have the same length.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(22)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// let res = chip.add_constants(&mut layouter, &[x, y], &[F::from(3), F::from(5)])?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res[0], F::from(25))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res[1], F::from(12))?;
    /// # });
    /// ```
    fn add_constants(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: &[Assigned],
        constants: &[Assigned::Element],
    ) -> Result<Vec<Assigned>, Error> {
        assert_eq!(xs.len(), constants.len());

        (xs.iter().zip(constants.iter()))
            .map(|(x, c)| self.add_constant(layouter, x, c.clone()))
            .collect()
    }

    /// Multiplication by a constant.
    /// This function is potentially more efficient than composing
    /// [assigned_fixed](AssignmentInstructions::assign_fixed) and
    /// [mul](ArithInstructions::mul).
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// let res = chip.mul_by_constant(&mut layouter, &x, F::from(3))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(21))?;
    /// # });
    /// ```
    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        constant: Assigned::Element,
    ) -> Result<Assigned, Error> {
        if constant == Assigned::Element::from(0) {
            return self.assign_fixed(layouter, Assigned::Element::from(0));
        }
        if constant == Assigned::Element::from(1) {
            return Ok(x.clone());
        }
        self.linear_combination(
            layouter,
            &[(constant, x.clone())],
            Assigned::Element::from(0),
        )
    }

    /// Multiplication of an element by itself.
    fn square(&self, layouter: &mut impl Layouter<F>, x: &Assigned) -> Result<Assigned, Error> {
        self.mul(layouter, x, x, None)
    }

    /// Exponentiate the given assigned element to the given (constant) n.
    /// `pow(zero, 0)` is `one` by definition.
    fn pow(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        n: u64,
    ) -> Result<Assigned, Error> {
        if n == 0 {
            return self.assign_fixed(layouter, Assigned::Element::from(1));
        }

        let mut n = n;
        let mut tmp = x.clone();
        let mut res = None;

        // This is a simple square-and-multiply.
        // TODO: It could be optimized with windows.
        while n > 0 {
            if n & 1 != 0 {
                res = match res {
                    None => Some(tmp.clone()),
                    Some(acc) => Some(self.mul(layouter, &acc, &tmp, None)?),
                };
            }

            n >>= 1;

            if n > 0 {
                tmp = self.square(layouter, &tmp)?;
            }
        }

        Ok(res.unwrap())
    }

    /// Computes `a*x + b*y + c*z + k + m*x*y`.
    fn add_and_mul(
        &self,
        layouter: &mut impl Layouter<F>,
        (a, x): (Assigned::Element, &Assigned),
        (b, y): (Assigned::Element, &Assigned),
        (c, z): (Assigned::Element, &Assigned),
        k: Assigned::Element,
        m: Assigned::Element,
    ) -> Result<Assigned, Error> {
        let p = self.mul(layouter, x, y, None)?;
        self.linear_combination(
            layouter,
            &[(a, x.clone()), (b, y.clone()), (c, z.clone()), (m, p)],
            k,
        )
    }
}

#[cfg(test)]
#[allow(missing_docs)]
pub mod tests {
    use std::{cmp::min, marker::PhantomData};

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
        testing_utils::{FromScratch, Invertible},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum Operation {
        Add,
        Sub,
        Mul,
        Div,
        Neg,
        Inv,
        Pow(u64),
        AddConst,
        MulByConst,
        LinearComb,
        AddAndMul,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, ArithChip>
    where
        Assigned: InnerValue,
    {
        inputs: Vec<Assigned::Element>,
        expected: Assigned::Element,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, ArithChip)>,
    }

    impl<F, Assigned, ArithChip> Circuit<F> for TestCircuit<F, Assigned, ArithChip>
    where
        F: PrimeField,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        type Config = <ArithChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            ArithChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = ArithChip::new_from_scratch(&config);
            ArithChip::load_from_scratch(&mut layouter, &config);

            // y does not apply in tests of arity-1 functions.
            let y_idx = min(self.inputs.len() - 1, 1);
            let x = chip.assign(&mut layouter, Value::known(self.inputs[0].clone()))?;
            let y = chip.assign_fixed(&mut layouter, self.inputs[y_idx].clone())?;
            let k = self.inputs[y_idx].clone();

            let res = match self.operation {
                Operation::Add => chip.add(&mut layouter, &x, &y),
                Operation::Sub => chip.sub(&mut layouter, &x, &y),
                Operation::Mul => chip.mul(&mut layouter, &x, &y, None),
                Operation::Div => chip.div(&mut layouter, &x, &y),
                Operation::Neg => chip.neg(&mut layouter, &x),
                Operation::Inv => chip.inv(&mut layouter, &x),
                Operation::Pow(n) => chip.pow(&mut layouter, &x, n),
                Operation::AddConst => chip.add_constant(&mut layouter, &x, k),
                Operation::MulByConst => chip.mul_by_constant(&mut layouter, &x, k),
                Operation::LinearComb => {
                    let mut terms = vec![];
                    for i in 0..(self.inputs.len() / 2) {
                        let coeff = self.inputs[2 * i].clone();
                        let x_val = self.inputs[2 * i + 1].clone();
                        let x = chip.assign(&mut layouter, Value::known(x_val))?;
                        terms.push((coeff, x));
                    }
                    let constant = self.inputs.last().unwrap().clone();
                    chip.linear_combination(&mut layouter, &terms, constant)
                }
                Operation::AddAndMul => chip.add_and_mul(
                    &mut layouter,
                    (Assigned::Element::from(1), &x),
                    (Assigned::Element::from(1), &y),
                    (Assigned::Element::from(0), &y),
                    Assigned::Element::from(0),
                    Assigned::Element::from(1),
                ),
            }?;

            let expected = chip.assign_fixed(&mut layouter, self.expected.clone())?;
            chip.assert_equal(&mut layouter, &expected, &res)
        }
    }

    fn run<F, Assigned, ArithChip>(
        inputs: &[Assigned::Element],
        expected: Assigned::Element,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, ArithChip> {
            inputs: inputs.to_vec(),
            expected,
            operation: operation.clone(),
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

    fn i64_to_element<Element>(x: &i64) -> Element
    where
        Element: From<u64> + Neg<Output = Element>,
    {
        let mut res = Element::from(x.unsigned_abs());
        if *x < 0 {
            res = -res
        }
        res
    }

    pub fn test_add<F, Assigned, ArithChip>(chip_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u32() as i64;
        let s = rng.next_u32() as i64;
        let mut cost_model = true;
        [
            (r, r, 2 * r, true),
            (r, s, r + s, true),
            (0, 0, 0, true),
            (0, 1, 1, true),
            (1, 0, 1, true),
            (1, 1, 2, true),
            (3, 5, 8, true),
            (1, 1, 3, false),
        ]
        .iter()
        .for_each(|(x, y, expected, must_pass)| {
            let inputs = [i64_to_element(x), i64_to_element(y)];
            let expected: Assigned::Element = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected.clone(),
                Operation::Add,
                *must_pass,
                cost_model,
                chip_name,
                "add",
            );
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected,
                Operation::AddConst,
                *must_pass,
                cost_model,
                chip_name,
                "add_constant",
            );
            cost_model = false;
        });
    }

    pub fn test_sub<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u32() as i64;
        let s = rng.next_u32() as i64;
        let mut cost_model = true;
        [
            (r, r, 0, true),
            (r, s, r - s, true),
            (0, 0, 0, true),
            (1, 0, 1, true),
            (2, 1, 1, true),
            (8, 5, 3, true),
            (3, -5, 8, true),
            (3, -3, 0, false),
        ]
        .iter()
        .for_each(|(x, y, expected, must_pass)| {
            let inputs = [i64_to_element(x), i64_to_element(y)];
            let expected = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected,
                Operation::Sub,
                *must_pass,
                cost_model,
                cost_model_name,
                "sub",
            );
            cost_model = false;
        });
    }

    pub fn test_mul<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u32() as i64;
        let s = rng.next_u32() as i64;
        let mut cost_model = true;
        [
            (2, r, 2 * r, true),
            (s, 0, 0, true),
            (0, 0, 0, true),
            (1, 0, 0, true),
            (-2, -1, 2, true),
            (8, 5, 40, true),
            (3, -5, -15, true),
            (0, 1, 1, false),
            (2, 1, 0, false),
        ]
        .iter()
        .for_each(|(x, y, expected, must_pass)| {
            let inputs = [i64_to_element(x), i64_to_element(y)];
            let expected: Assigned::Element = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected.clone(),
                Operation::Mul,
                *must_pass,
                cost_model,
                cost_model_name,
                "mul",
            );
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected,
                Operation::MulByConst,
                *must_pass,
                cost_model,
                cost_model_name,
                "mul_by_const",
            );
            cost_model = false;
        });
    }

    pub fn test_div<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u32() as i64;
        let s = rng.next_u32() as i64;
        let mut cost_model = true;
        [
            (r, r, 1, true),
            (s, 1, s, true),
            (0, 1, 0, true),
            (1, 1, 1, true),
            (2, -1, -2, true),
            (8, 4, 2, true),
            (91, 13, 7, true),
            (0, 0, 0, false),
            (3, 2, 1, false),
            (s, s, -1, false),
        ]
        .iter()
        .for_each(|(x, y, expected, must_pass)| {
            let inputs = [i64_to_element(x), i64_to_element(y)];
            let expected = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected,
                Operation::Div,
                *must_pass,
                cost_model,
                cost_model_name,
                "div",
            );
            cost_model = false;
        });
    }

    pub fn test_neg<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u32() as i64;
        let mut cost_model = true;
        [
            (r, -r, true),
            (0, 0, true),
            (1, -1, true),
            (-1, 1, true),
            (2, -2, true),
            (1, 1, false),
        ]
        .iter()
        .for_each(|(x, expected, must_pass)| {
            let inputs = [i64_to_element(x)];
            let expected = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected,
                Operation::Neg,
                *must_pass,
                cost_model,
                cost_model_name,
                "neg",
            );
            cost_model = false;
        });
    }

    pub fn test_inv<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>
            + Invertible,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let zero = Assigned::Element::from(0);
        let one = Assigned::Element::from(1);
        let r = i64_to_element::<Assigned::Element>(&(rng.next_u32() as i64));
        let mut cost_model = true;
        [
            (r.invert(), r.clone(), true),
            (one.clone(), one.clone(), true),
            (-one.clone(), -one.clone(), true),
            (-one.clone(), one, false),
            (r.clone(), r, false),
            (zero.clone(), zero, false),
        ]
        .into_iter()
        .for_each(|(x, expected, must_pass)| {
            run::<F, Assigned, ArithChip>(
                &[x],
                expected,
                Operation::Inv,
                must_pass,
                cost_model,
                cost_model_name,
                "inv",
            );
            cost_model = false;
        });
    }

    pub fn test_pow<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = (rng.next_u32() >> 1) as i64;
        let mut cost_model = true;
        [
            (r, 2, r * r, true),
            (0, 0, 1, true),
            (1, 0, 1, true),
            (r, 0, 1, true),
            (1, 1, 1, true),
            (1, 2, 1, true),
            (2, 3, 8, true),
            (4, 5, 1024, true),
            (-3, 2, 9, true),
            (-7, 3, -343, true),
            (2, 62, 1 << 62, true),
            (r, 0, 0, false),
            (2, 2, 3, false),
        ]
        .iter()
        .for_each(|(x, n, expected, must_pass)| {
            let inputs = [i64_to_element(x)];
            let expected: Assigned::Element = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected.clone(),
                Operation::Pow(*n),
                *must_pass,
                cost_model,
                cost_model_name,
                "pow",
            );
            cost_model = false;
        });
    }

    pub fn test_linear_combination<F, Assigned, ArithChip>(cost_model_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u32() as i64;
        let s = rng.next_u32() as i64;
        let mut cost_model = true;
        [
            (vec![(17, r), (-4, s)], 2, 17 * r - 4 * s + 2, true),
            (vec![], r, r, true),
            (vec![(7, 13)], -1, 90, true),
            (vec![(-10, 5), (5, 10)], 0, 0, true),
            (vec![(0, 0), (0, 0)], 0, 0, true),
            (vec![(2, 3), (4, 7), (-1, 2)], 5, 37, true),
            (vec![(1, 1), (2, 1), (4, 1), (8, 1)], 0, 15, true),
            (vec![(1, 3), (2, 3), (4, 3), (8, 3), (16, 3)], 7, 100, true),
            (
                vec![
                    (1, 3),
                    (2, 3),
                    (4, 3),
                    (8, 3),
                    (16, 3),
                    (1, 1),
                    (2, 1),
                    (4, 1),
                    (8, 1),
                ],
                7,
                115,
                true,
            ),
        ]
        .iter()
        .for_each(|(terms, constant, expected, must_pass)| {
            let mut inputs = vec![];
            for (coeff, x_val) in terms {
                inputs.push(i64_to_element(coeff));
                inputs.push(i64_to_element(x_val));
            }
            inputs.push(i64_to_element(constant));
            let expected = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected,
                Operation::LinearComb,
                *must_pass,
                cost_model,
                cost_model_name,
                "linear_comb",
            );
            cost_model = false;
        });
    }

    pub fn test_add_and_mul<F, Assigned, ArithChip>(chip_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Clone + Debug + InnerValue,
        Assigned::Element: Clone
            + Debug
            + Default
            + PartialEq
            + From<u64>
            + Add<Output = Assigned::Element>
            + Neg<Output = Assigned::Element>,
        ArithChip: ArithInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        // divide by 2 to avoid overflow in multiplication
        let r = (rng.next_u32() as i64) / 2;
        let s = (rng.next_u32() as i64) / 2;
        let mut cost_model = true;
        [
            (r, s, r + s + r * s, true),
            (0, 0, 0, true),
            (1, 1, 2, false),
            (1, r, 2 * r + 1, true),
        ]
        .iter()
        .for_each(|(x, y, expected, must_pass)| {
            let inputs = [i64_to_element(x), i64_to_element(y)];
            let expected: Assigned::Element = i64_to_element(expected);
            run::<F, Assigned, ArithChip>(
                &inputs,
                expected.clone(),
                Operation::AddAndMul,
                *must_pass,
                cost_model,
                chip_name,
                "add_and_mul",
            );
            cost_model = false;
        });
    }
}
