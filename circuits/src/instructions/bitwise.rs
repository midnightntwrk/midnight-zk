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

//! Bitwise instructions interface.
//!
//! It provides functions for performing bit-wise Boolean operations between
//! assigned values in the circuit.
//!
//! This trait is parametrized by a generic `Assigned` (required to implement
//! [InnerValue](crate::types::InnerValue)) and whose inner `Element` type is
//! required to implement [PrimeField]). `Assigned` defined the type over which
//! the bitwise operations take place.

use ff::{Field, PrimeField};
use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;
use num_traits::One;

use super::{BinaryInstructions, DecompositionInstructions, RangeCheckInstructions};
use crate::types::{InnerConstants, Instantiable};

/// The set of circuit instructions for binary bit-wise operations.
pub trait BitwiseInstructions<F, Assigned>:
    BinaryInstructions<F> + DecompositionInstructions<F, Assigned> + RangeCheckInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: Instantiable<F> + InnerConstants + Clone,
    Assigned::Element: PrimeField,
{
    /// Bitwise conjunction of the given assigned elements, interpreted as
    /// binary bit-strings of length `n`.
    ///
    /// # Panics
    ///
    /// If any of the given assigned elements cannot be decomposed in `n` bits,
    /// the circuit will become unsatisfiable.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(13)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// // 0b1101 & 0b0111 = 0b0101
    /// let res = chip.band(&mut layouter, &x, &y, 4)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(5))?;
    /// # });
    /// ```
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(16)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// // x is not in the range [0, 2^4), the following should be unsatisfiable
    /// let res = chip.band(&mut layouter, &x, &y, 4)?;
    /// # });
    /// ```
    fn band(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
        n: usize,
    ) -> Result<Assigned, Error> {
        let x_bits = self.assigned_to_le_bits(layouter, x, Some(n), true)?;
        let y_bits = self.assigned_to_le_bits(layouter, y, Some(n), true)?;
        let res_bits = x_bits
            .into_iter()
            .zip(y_bits.into_iter())
            .map(|(bx, by)| self.and(layouter, &[bx, by]))
            .collect::<Result<Vec<_>, Error>>()?;
        self.assigned_from_le_bits(layouter, &res_bits)
    }

    /// Bitwise disjunction of the given assigned elements, interpreted as
    /// binary bit-strings of length `n`.
    ///
    /// # Panics
    ///
    /// If any of the given assigned elements cannot be decomposed in `n` bits,
    /// the circuit will become unsatisfiable.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(13)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// // 0b1101 | 0b0111 = 0b1111
    /// let res = chip.bor(&mut layouter, &x, &y, 4)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(15))?;
    /// # });
    /// ```
    fn bor(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
        n: usize,
    ) -> Result<Assigned, Error> {
        let x_bits = self.assigned_to_le_bits(layouter, x, Some(n), true)?;
        let y_bits = self.assigned_to_le_bits(layouter, y, Some(n), true)?;
        let res_bits = x_bits
            .into_iter()
            .zip(y_bits.into_iter())
            .map(|(bx, by)| self.or(layouter, &[bx, by]))
            .collect::<Result<Vec<_>, Error>>()?;
        self.assigned_from_le_bits(layouter, &res_bits)
    }

    /// Bitwise exclusive-or of the given assigned elements, interpreted as
    /// binary bit-strings of length `n`.
    ///
    /// # Panics
    ///
    /// If any of the given assigned elements cannot be decomposed in `n` bits,
    /// the circuit will become unsatisfiable.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(13)))?;
    /// let y = chip.assign(&mut layouter, Value::known(F::from(7)))?;
    ///
    /// // 0b1101 ^ 0b0111 = 0b1010
    /// let res = chip.bxor(&mut layouter, &x, &y, 4)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(10))?;
    /// # });
    /// ```
    fn bxor(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        y: &Assigned,
        n: usize,
    ) -> Result<Assigned, Error> {
        let x_bits = self.assigned_to_le_bits(layouter, x, Some(n), true)?;
        let y_bits = self.assigned_to_le_bits(layouter, y, Some(n), true)?;
        let res_bits = x_bits
            .into_iter()
            .zip(y_bits.into_iter())
            .map(|(bx, by)| self.xor(layouter, &[bx, by]))
            .collect::<Result<Vec<_>, Error>>()?;
        self.assigned_from_le_bits(layouter, &res_bits)
    }

    /// Bitwise negation of the given assigned element, interpreted as a
    /// binary bit-string of length `n`.
    ///
    /// # Panics
    ///
    /// If the given assigned element cannot be decomposed in `n` bits, the
    /// circuit will become unsatisfiable.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(6)))?;
    ///
    /// // !0b0110 = 0b1001
    /// let res = chip.bnot(&mut layouter, &x, 4)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, F::from(9))?;
    /// # });
    /// ```
    fn bnot(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Assigned,
        n: usize,
    ) -> Result<Assigned, Error> {
        // Simply return `2^n - 1 - x` after having verified that `x in [0, 2^n)`.
        self.assert_lower_than_fixed(layouter, x, &(BigUint::one() << n))?;
        self.linear_combination(
            layouter,
            &[(-Assigned::inner_one(), x.clone())],
            Assigned::Element::from(2).pow([n as u64]) - Assigned::inner_one(),
        )
    }
}

#[cfg(test)]
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
    use crate::{testing_utils::FromScratch, utils::circuit_modeling::circuit_to_json};

    #[derive(Clone, Copy, Debug)]
    enum Operation {
        Band,
        Bor,
        Bxor,
        Bnot,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, BitwiseChip>
    where
        Assigned: InnerConstants,
    {
        inputs: Vec<Assigned::Element>,
        expected: Assigned::Element,
        n: usize,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, BitwiseChip)>,
    }

    impl<F, Assigned, BitwiseChip> Circuit<F> for TestCircuit<F, Assigned, BitwiseChip>
    where
        F: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        Assigned::Element: PrimeField,
        BitwiseChip: BitwiseInstructions<F, Assigned> + FromScratch<F>,
    {
        type Config = <BitwiseChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            BitwiseChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = BitwiseChip::new_from_scratch(&config);
            BitwiseChip::load_from_scratch(&mut layouter, &config);

            // y does not apply in tests of arity-1 functions.
            let y_idx = min(self.inputs.len() - 1, 1);
            let x = chip.assign(&mut layouter, Value::known(self.inputs[0]))?;
            let y = chip.assign(&mut layouter, Value::known(self.inputs[y_idx]))?;

            let res = match self.operation {
                Operation::Band => chip.band(&mut layouter, &x, &y, self.n),
                Operation::Bor => chip.bor(&mut layouter, &x, &y, self.n),
                Operation::Bxor => chip.bxor(&mut layouter, &x, &y, self.n),
                Operation::Bnot => chip.bnot(&mut layouter, &x, self.n),
            }?;

            chip.assert_equal_to_fixed(&mut layouter, &res, self.expected)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, BitwiseChip>(
        inputs: &[Assigned::Element],
        expected: &Assigned::Element,
        n: usize,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        circuit_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        Assigned::Element: PrimeField,
        BitwiseChip: BitwiseInstructions<F, Assigned> + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, BitwiseChip> {
            inputs: inputs.to_vec(),
            expected: *expected,
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
            circuit_to_json(log2_nb_rows, circuit_name, op_name, 0, circuit);
        }
    }

    pub fn test_band<F, Assigned, BitwiseChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        Assigned::Element: PrimeField + From<u64>,
        BitwiseChip: BitwiseInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u64();
        let s = rng.next_u64();
        let mut cost_model = true;
        [
            (r, r, r, true),
            (r, r, 0, false),
            (r, s, r & s, true),
            (0, 0, 0, true),
            (1, 1, 1, true),
            (5, 7, 5, true),
            (5, 2, 0, true),
            (0, 0, 1, false),
        ]
        .iter()
        .for_each(|(x, y, z, must_pass)| {
            let inputs = [Assigned::Element::from(*x), Assigned::Element::from(*y)];
            let expected = Assigned::Element::from(*z);
            run::<F, Assigned, BitwiseChip>(
                &inputs,
                &expected,
                64,
                Operation::Band,
                *must_pass,
                cost_model,
                name,
                "band",
            );
            cost_model = false;
        });
        let ten = Assigned::Element::from(10);
        run::<F, Assigned, BitwiseChip>(
            &[ten, ten],
            &ten,
            3,
            Operation::Band,
            false,
            cost_model,
            "",
            "",
        );
    }

    pub fn test_bor<F, Assigned, BitwiseChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        Assigned::Element: PrimeField + From<u64>,
        BitwiseChip: BitwiseInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u64();
        let s = rng.next_u64();
        let mut cost_model = true;
        [
            (r, r, r, true),
            (r, r, 0, false),
            (r, s, r | s, true),
            (0, 0, 0, true),
            (1, 1, 1, true),
            (5, 7, 7, true),
            (5, 2, 7, true),
            (0, 0, 1, false),
        ]
        .iter()
        .for_each(|(x, y, z, must_pass)| {
            let inputs = [Assigned::Element::from(*x), Assigned::Element::from(*y)];
            let expected = Assigned::Element::from(*z);
            run::<F, Assigned, BitwiseChip>(
                &inputs,
                &expected,
                64,
                Operation::Bor,
                *must_pass,
                cost_model,
                name,
                "bor",
            );
            cost_model = false;
        });
        let ten = Assigned::Element::from(10);
        run::<F, Assigned, BitwiseChip>(&[ten, ten], &ten, 3, Operation::Bor, false, false, "", "");
    }

    pub fn test_bxor<F, Assigned, BitwiseChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        Assigned::Element: PrimeField + From<u64>,
        BitwiseChip: BitwiseInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u64();
        let s = rng.next_u64();
        let mut cost_model = true;
        [
            (r, r, r, false),
            (r, r, 0, true),
            (r, s, r ^ s, true),
            (0, 0, 0, true),
            (1, 1, 0, true),
            (5, 7, 2, true),
            (5, 2, 7, true),
            (0, 0, 1, false),
        ]
        .iter()
        .for_each(|(x, y, z, must_pass)| {
            let inputs = [Assigned::Element::from(*x), Assigned::Element::from(*y)];
            let expected = Assigned::Element::from(*z);
            run::<F, Assigned, BitwiseChip>(
                &inputs,
                &expected,
                64,
                Operation::Bxor,
                *must_pass,
                cost_model,
                name,
                "bxor",
            );
            cost_model = false;
        });
        let zero = Assigned::Element::from(0);
        let ten = Assigned::Element::from(10);
        run::<F, Assigned, BitwiseChip>(
            &[ten, ten],
            &zero,
            3,
            Operation::Bxor,
            false,
            false,
            "",
            "",
        );
    }

    pub fn test_bnot<F, Assigned, BitwiseChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        Assigned::Element: PrimeField + From<u64>,
        BitwiseChip: BitwiseInstructions<F, Assigned> + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r = rng.next_u64();
        let mut cost_model = true;
        [
            (r, !r, true, 64),
            (r, !r + 1, false, 64),
            (0, 7, true, 3),
            (1, 6, true, 3),
            (2, 5, true, 3),
            (5, 2, true, 3),
            (0, 1, false, 3),
        ]
        .iter()
        .for_each(|(x, z, must_pass, n)| {
            let inputs = [Assigned::Element::from(*x)];
            let expected = Assigned::Element::from(*z);
            run::<F, Assigned, BitwiseChip>(
                &inputs,
                &expected,
                *n,
                Operation::Bnot,
                *must_pass,
                cost_model,
                name,
                "bnot",
            );
            cost_model = false;
        });
        let mone = -Assigned::Element::from(1);
        let eight = Assigned::Element::from(8);
        run::<F, Assigned, BitwiseChip>(&[eight], &mone, 3, Operation::Bnot, false, false, "", "");
    }
}
