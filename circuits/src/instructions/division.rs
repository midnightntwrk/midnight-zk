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
    /// This trait is implemented with respect an Assigned type whose inner
    /// value has an integer structure (enforced by requiring the
    /// `FromBigUint` trait).
    ///
    /// Given a `dividend` as an assigned element (interpreted as an integer
    /// bounded by `bound`), and a constant `divisor`, returns the quotient
    /// and remainder of dividing the former by the latter, as integers.
    ///
    /// # Unsatisfiable
    ///  If `dividend >= bound` (when interpreted as an integer).
    ///
    /// # Panics
    ///  If `divisor = 0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(17)))?;
    ///
    /// let (q, r) = chip.div_rem(&mut layouter, &x, 32u32, 5u32)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &q, F::from(3))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &r, F::from(2))?;
    /// # });
    /// ```
    fn div_rem(
        &self,
        layouter: &mut impl Layouter<F>,
        dividend: &Assigned,
        bound: u32,
        divisor: u32,
    ) -> Result<(Assigned, Assigned), Error> {
        assert!(divisor != 0);
        assert!((F::NUM_BITS > 31) && (bound < 1 << 31) && (divisor < 1 << 31)); // Ensure the operations fit in the native field.

        let divisor_bu = BigUint::from(divisor as u64);
        let (q, r) = dividend
            .value()
            .map(|v| {
                let (q, r) = v.into_biguint().div_rem(&divisor_bu);
                (FromBigUint::from_biguint(q), FromBigUint::from_biguint(r))
            })
            .unzip();

        let r = self.assign_lower_than_fixed(layouter, r, &divisor_bu)?;

        let q = self.assign_lower_than_fixed(
            layouter,
            q,
            &(BigUint::from(divisor + bound) / divisor_bu),
        )?;

        let expected_div = self.linear_combination(
            layouter,
            &[
                (Assigned::Element::from(divisor as u64), q.clone()),
                (Assigned::Element::from(1), r.clone()),
            ],
            Assigned::Element::from(0),
        )?;
        self.assert_equal(layouter, dividend, &expected_div)?;

        Ok((q, r))
    }

    /// Integer modulo operation.
    ///
    /// This trait is implemented with respect an Assigned type whose inner
    /// value has an integer structure (enforced by requiring the
    /// `FromBigUint` trait).
    ///
    /// Given a `dividend` as an assigned element (interpreted as an integer
    /// bounded by `bound`), and a constant `modulus`, returns the remainder of
    /// dividing the former by the latter, as integers.
    ///
    /// # Unsatisfiable
    ///  If `dividend >= bound` (when interpreted as an integer).
    ///
    /// # Panics
    ///  If `modulus = 0`.
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(17)))?;
    ///
    /// let r = chip.rem(&mut layouter, &x, 32u32, 5u32)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &r, F::from(2))?;
    /// # });
    /// ```
    fn rem(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &Assigned,
        bound: u32,
        modulus: u32,
    ) -> Result<Assigned, Error> {
        self.div_rem(layouter, input, bound, modulus).map(|p| p.1)
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
        divisor: u32,
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
            let (q, r) = chip.div_rem(&mut layouter, &x, 1 << 12, self.divisor)?;

            chip.assert_equal_to_fixed(&mut layouter, &q, self.expected.0.clone())?;
            chip.assert_equal_to_fixed(&mut layouter, &r, self.expected.1.clone())?;

            chip.load_from_scratch(&mut layouter)
        }
    }

    fn run<F, Assigned, DivChip>(
        dividend: u64,
        divisor: u32,
        expected: (u64, u64),
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
            dividend: Value::known(Assigned::Element::from(dividend as u64)),
            divisor,
            expected: (
                Assigned::Element::from(expected.0),
                Assigned::Element::from(expected.1),
            ),
            _marker: PhantomData,
        };

        let k = 10;

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
            circuit_to_json(k, chip_name, "div_rem", 0, circuit);
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
            (1 << 13, 1, (1 << 13, 0), false),
        ]
        .into_iter()
        .enumerate()
        .for_each(|(i, (dividend, divisor, (q, r), must_pass))| {
            run::<F, Assigned, DivChip>(dividend, divisor, (q, r), must_pass, i == 0, chip_name)
        });
    }
}
