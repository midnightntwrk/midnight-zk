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

//! Integer division and moduli instructions interface.
//!
//! It provides instructions for computing quotient and remidners between
//! bounded integers that fit in the native field.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::{
    instructions::{ArithInstructions, RangeCheckInstructions},
    types::InnerValue,
    utils::types::FromBigUint,
};

/// Set of circuit instructions for integer division.
pub trait DivisionInstructions<F, Assigned>:
    ArithInstructions<F, Assigned> + RangeCheckInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: InnerValue,
    Assigned::Element: FromBigUint,
{
    /// Integer division by a constant.
    ///
    /// This trait is implemented with respect to an Assigned type whose inner
    /// value has an integer structure (enforced by requiring the
    /// `FromBigUint` trait).
    ///
    /// Given a `dividend` as an assigned element (interpreted as an integer),
    /// and a constant `divisor`, returns the quotient and remainder of
    /// dividing the former by the latter, as integers.
    ///
    /// An optional (inclusive) upper bound can be provided on the value of
    /// the `dividend`. It is the responsibility of the caller that, if
    /// provided, the bound on the dividend be valid.
    ///
    /// # Panics
    ///  - If `divisor = 0`.
    ///  - If `divisor > dividend_bound` when the bound is provided or if
    ///    `divisor` is greater than or equal to the maximum value that an
    ///    `Assigned::Element` can take.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(17)))?;
    ///
    /// let (q, r) = chip.div_rem(&mut layouter, &x, 5u64.into(), None)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &q, F::from(3))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &r, F::from(2))?;
    /// # });
    /// ```
    fn div_rem(
        &self,
        layouter: &mut impl Layouter<F>,
        dividend: &Assigned,
        divisor: BigUint,
        dividend_bound: Option<BigUint>,
    ) -> Result<(Assigned, Assigned), Error> {
        if divisor == BigUint::one() {
            return Ok((
                dividend.clone(),
                self.assign_fixed(layouter, Assigned::Element::from(0))?,
            ));
        }

        let dividend_bound = dividend_bound.unwrap_or((-Assigned::Element::from(1)).into_biguint());
        assert!(divisor > BigUint::zero());
        assert!(divisor <= dividend_bound);

        let (q, r) = dividend
            .value()
            .map(|v| {
                let (q, r) = v.into_biguint().div_rem(&divisor);
                (FromBigUint::from_biguint(q), FromBigUint::from_biguint(r))
            })
            .unzip();

        let q_strict_bound = (dividend_bound / &divisor) + BigUint::one();

        let r = self.assign_lower_than_fixed(layouter, r, &divisor)?;
        let q = self.assign_lower_than_fixed(layouter, q, &q_strict_bound)?;

        let sum = self.linear_combination(
            layouter,
            &[
                (FromBigUint::from_biguint(divisor), q.clone()),
                (Assigned::Element::from(1), r.clone()),
            ],
            Assigned::Element::from(0),
        )?;
        self.assert_equal(layouter, dividend, &sum)?;

        Ok((q, r))
    }

    /// Integer modulo operation.
    ///
    /// This trait is implemented with respect to an Assigned type whose inner
    /// value has an integer structure (enforced by requiring the
    /// `FromBigUint` trait).
    ///
    /// Given an `input` as an assigned element (interpreted as an integer
    /// bounded by `bound`), and a constant `modulus`, returns the remainder of
    /// dividing the former by the latter, as integers.
    ///
    /// An optional (inclusive) upper bound can be provided on the value of
    /// the `input`. It is the responsibility of the caller that, if
    /// provided, the bound on the input be valid.
    ///
    /// # Panics
    ///  - If `modulus = 0`.
    ///  - If `modulus > input_bound` when the bound is provided or if `modulus`
    ///    is greater than or equal to the maximum value that an
    ///    `Assigned::Element` can take.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(17)))?;
    ///
    /// let r = chip.rem(&mut layouter, &x, 5u64.into(), None)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &r, F::from(2))?;
    /// # });
    /// ```
    fn rem(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &Assigned,
        modulus: BigUint,
        input_bound: Option<BigUint>,
    ) -> Result<Assigned, Error> {
        self.div_rem(layouter, input, modulus, input_bound).map(|(_, r)| r)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;
    use crate::{
        testing_utils::FromScratch, types::InnerValue, utils::circuit_modeling::circuit_to_json,
    };

    struct TestCircuit<F, Assigned, DivChip>
    where
        Assigned: InnerValue,
    {
        dividend: Value<Assigned::Element>,
        divisor: BigUint,
        expected: (Assigned::Element, Assigned::Element),
        _marker: PhantomData<(F, DivChip)>,
    }

    impl<F, Assigned, DivChip> Circuit<F> for TestCircuit<F, Assigned, DivChip>
    where
        F: PrimeField,
        Assigned: InnerValue,
        Assigned::Element: FromBigUint,
        DivChip: DivisionInstructions<F, Assigned> + FromScratch<F>,
    {
        type Config = <DivChip as FromScratch<F>>::Config;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!();
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            DivChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = DivChip::new_from_scratch(&config);

            let x = chip.assign(&mut layouter, self.dividend.clone())?;
            let (q, r) = chip.div_rem(&mut layouter, &x, self.divisor.clone(), None)?;

            chip.assert_equal_to_fixed(&mut layouter, &q, self.expected.0.clone())?;
            chip.assert_equal_to_fixed(&mut layouter, &r, self.expected.1.clone())?;

            chip.load_from_scratch(&mut layouter)
        }
    }

    fn run<F, Assigned, DivChip>(
        dividend: Assigned::Element,
        divisor: BigUint,
        expected: (Assigned::Element, Assigned::Element),
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: FromBigUint,
        DivChip: DivisionInstructions<F, Assigned> + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, DivChip> {
            dividend: Value::known(dividend),
            divisor,
            expected,
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
            circuit_to_json(chip_name, "div_rem", circuit);
        }
    }

    pub fn test_div_rem<F, Assigned, DivChip>(chip_name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned: InnerValue,
        Assigned::Element: FromBigUint,
        DivChip: DivisionInstructions<F, Assigned> + FromScratch<F>,
    {
        [
            (17, 5, (3, 2), true),
            (0, 1, (0, 0), true),
            (1, 1, (1, 0), true),
            (100, 5, (20, 0), true),
            (100, 7, (14, 2), true),
            (1 << 13, 1, (1 << 13, 0), true),
        ]
        .into_iter()
        .enumerate()
        .for_each(|(i, (dividend, divisor, (q, r), must_pass))| {
            run::<F, Assigned, DivChip>(
                Assigned::Element::from(dividend),
                BigUint::from(divisor as u64),
                (Assigned::Element::from(q), Assigned::Element::from(r)),
                must_pass,
                i == 0,
                chip_name,
            )
        });

        let zero = BigUint::from(0u64);
        let one = BigUint::from(1u64);
        let two = BigUint::from(2u64);
        let max = (-Assigned::Element::from(1)).into_biguint();

        [
            (&max, &(&max - &one), (&one, &one), true),
            (&(&max + &one), &(&max - &one), (&one, &two), false),
            (&(&max + &one), &(&max - &one), (&zero, &zero), true),
        ]
        .into_iter()
        .for_each(|(dividend, divisor, (q, r), must_pass)| {
            run::<F, Assigned, DivChip>(
                FromBigUint::from_biguint(dividend.clone()),
                divisor.clone(),
                (
                    FromBigUint::from_biguint(q.clone()),
                    FromBigUint::from_biguint(r.clone()),
                ),
                must_pass,
                false,
                chip_name,
            )
        });
    }
}
