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

use super::{
    ArithInstructions, AssertionInstructions, AssignmentInstructions, BinaryInstructions,
    ComparisonInstructions, ControlFlowInstructions, ConversionInstructions, EqualityInstructions,
    RangeCheckInstructions, UnsafeConversionInstructions,
};
use crate::{
    field::{
        decomposition::instructions::CoreDecompositionInstructions, AssignedNative, NativeGadget,
    },
    types::AssignedBit,
    utils::util::{big_to_fe, fe_to_big},
};

/// Set of circuit instructions for integer division.
pub trait DivisionInstructions<F>: ComparisonInstructions<F, AssignedNative<F>>
where
    F: PrimeField,
{
    /// Integer division by a constant.
    /// Given an integer bounded by `bound`, represented as an `AssignedNative`
    /// and a constant `divisor`, returns the quotient and remainder s.t:
    /// `dividend = quotient * divisor + remainder` and `0 <= remainder <
    /// divisor`.
    ///
    /// # Panics
    ///  - If `dividend` in canonical form interpreted as an integer is greater
    ///    or equal than `bound`.
    ///  - If divisor is 0.
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
        dividend: &AssignedNative<F>,
        bound: u32,
        divisor: u32,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error>;

    /// Integer modulus.
    /// Given an integer bounded by `bound`, represented as an `AssignedNative`
    /// and a constant `modulus`, returns the input mod `modulus`, ensuring
    /// the result is in the [0, modulus) range.
    ///
    /// # Panics
    ///  - If `input` in canonical form interpreted as an integer is greater or
    ///    equal than `bound`.
    ///  - If `modulus` is 0.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x = chip.assign(&mut layouter, Value::known(F::from(17)))?;
    ///
    /// let r = chip.modulus(&mut layouter, &x, 32u32, 5u32)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &r, F::from(2))?;
    /// # });
    /// ```
    fn modulus(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedNative<F>,
        bound: u32,
        modulus: u32,
    ) -> Result<AssignedNative<F>, Error> {
        let (_, r) = self.div_rem(layouter, input, bound, modulus)?;
        Ok(r)
    }
}

impl<F, CoreDecomposition, NativeArith> DivisionInstructions<F>
    for NativeGadget<F, CoreDecomposition, NativeArith>
where
    F: PrimeField,
    CoreDecomposition: CoreDecompositionInstructions<F>,
    NativeArith: ArithInstructions<F, AssignedNative<F>>
        + AssertionInstructions<F, AssignedNative<F>>
        + AssignmentInstructions<F, AssignedBit<F>>
        + ConversionInstructions<F, AssignedBit<F>, AssignedNative<F>>
        + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedBit<F>>
        + BinaryInstructions<F>
        + EqualityInstructions<F, AssignedNative<F>>
        + ControlFlowInstructions<F, AssignedNative<F>>,
{
    fn div_rem(
        &self,
        layouter: &mut impl Layouter<F>,
        dividend: &AssignedNative<F>,
        bound: u32,
        divisor: u32,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error> {
        assert!(divisor != 0);
        assert!((F::NUM_BITS > 31) && (bound < 1 << 31) && (divisor < 1 << 31)); // Ensure the operations fit in the native field.

        let divisor_bu = BigUint::from(divisor as u64);
        let (q, offset) = dividend
            .value()
            .map(|&d| {
                use num_integer::Integer;
                let d: BigUint = fe_to_big(d);
                let (q, r) = d.div_rem(&divisor_bu);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();

        let offset = self.assign_lower_than_fixed(layouter, offset, &divisor_bu)?;

        let q = self.assign_lower_than_fixed(
            layouter,
            q,
            &(BigUint::from(divisor + bound) / divisor_bu),
        )?;

        let expected_div = self.linear_combination(
            layouter,
            &[
                (F::from(divisor as u64), q.clone()),
                (F::ONE, offset.clone()),
            ],
            F::ZERO,
        )?;
        self.assert_equal(layouter, dividend, &expected_div)?;

        Ok((q, offset))
    }
}

#[cfg(test)]
mod test {
    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };

    use super::*;
    use crate::{
        field::{
            decomposition::chip::{P2RDecompositionChip, P2RDecompositionConfig},
            NativeChip,
        },
        testing_utils::FromScratch,
        utils::circuit_modeling::circuit_to_json,
    };

    type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    struct TestCircuit<F: PrimeField> {
        input: Value<F>,
        divisor: u32,
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
        type Config = P2RDecompositionConfig;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!();
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            NativeGadget::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let ng = NG::<F>::new_from_scratch(&config);
            NG::<F>::load_from_scratch(&mut layouter, &config);

            let (q, r) = self
                .input
                .map(|v| {
                    use num_integer::div_rem;
                    let v = fe_to_big(v);
                    let (q, r) = div_rem(v, BigUint::from(self.divisor));
                    (big_to_fe(q), big_to_fe(r))
                })
                .unzip();

            let expected_q = ng.assign(&mut layouter, q)?;
            let expected_r = ng.assign(&mut layouter, r)?;

            let x = ng.assign(&mut layouter, self.input)?;
            let (q, r) = ng.div_rem(&mut layouter, &x, 1 << 12, self.divisor)?;

            ng.assert_equal(&mut layouter, &q, &expected_q)?;
            ng.assert_equal(&mut layouter, &r, &expected_r)?;
            Ok(())
        }
    }

    fn run_div_rem_test<F>(dividend: u32, divisor: u32, cost_model: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F> {
            input: Value::known(F::from(dividend as u64)),
            divisor,
        };

        let k = 10;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(k, "Integer division (div_rem)", "div_rem", 0, circuit);
        }
    }

    #[test]
    fn div_rem() {
        type F = midnight_curves::Fq;
        run_div_rem_test::<F>(17, 5, false);
        run_div_rem_test::<F>(0, 1, false);
        run_div_rem_test::<F>(1, 1, false);
        run_div_rem_test::<F>(100, 5, false);
        run_div_rem_test::<F>(100, 7, false);
    }
}
