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

//! Canonicity instructions interface.
//!
//! It provides functions for checking if assigned bits, representing a value
//! `k`, are canonical with respect to some field order or a given bound `n`,
//! i.e. iff `|bits| <= n::NUM_BITS` and `k`, interpreted in little-endian,
//! is strictly lower than `n`.
//!
//! The implementors of this trait need to implement [FieldInstructions]
//! where the notion of `canonical` makes sense.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};
use num_bigint::BigUint;

use crate::{
    instructions::{AssignmentInstructions, FieldInstructions},
    types::{AssignedBit, InnerConstants, Instantiable},
};

/// The set of circuit instructions for canonicity assertions.
pub trait CanonicityInstructions<F, Assigned>:
    FieldInstructions<F, Assigned> + AssignmentInstructions<F, AssignedBit<F>>
where
    F: PrimeField,
    Assigned::Element: PrimeField,
    Assigned: Instantiable<F> + InnerConstants + Clone,
{
    /// Returns `true` iff the given sequence of bits is canonical in the
    /// underlying field `Assigned::Element`. Namely, iff
    /// `|bits| <= Assigned::Element::NUM_BITS` and the integer represented by
    /// the given sequence of assigned bits, interpreted in little-endian,
    /// is strictly lower than the order of `Assigned::Element`.
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: Vec<AssignedBit<F>> = chip.assign_many(
    ///     &mut layouter,
    ///     &[
    ///         Value::known(true),
    ///         Value::known(false),
    ///         Value::known(false),
    ///         Value::known(true),
    ///         Value::known(false),
    ///     ],
    /// )?;
    ///
    /// let check: AssignedBit<F> = chip.is_canonical(&mut layouter, &x)?;
    /// // This is not sufficient to check that the value is canonical,
    /// // we need to check that the output is true.
    /// chip.assert_equal_to_fixed(&mut layouter, &check, true)?;
    /// # });
    /// ```
    fn is_canonical(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        let order = self.order();
        if bits.len() > order.bits() as usize {
            self.assign_fixed(layouter, false)
        } else {
            self.le_bits_lower_than(layouter, bits, order)
        }
    }

    /// Returns `true` iff the integer represented by the given sequence of
    /// assigned bits, interpreted in little-endian, is strictly lower than the
    /// given bound.
    /// ```
    /// # use num_bigint::BigUint;
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let x: Vec<AssignedBit<F>> = chip.assign_many(
    ///     &mut layouter,
    ///     &[
    ///         Value::known(true),
    ///         Value::known(false),
    ///         Value::known(false),
    ///         Value::known(true),
    ///         Value::known(true),
    ///     ],
    /// )?;
    ///
    /// // assert the value is less than 32
    /// let check1: AssignedBit<F> = chip.le_bits_lower_than(&mut layouter, &x, BigUint::from(32u8))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &check1, true)?;
    ///
    /// // we can also compare the number with non-powers of two
    /// let check2: AssignedBit<F> = chip.le_bits_lower_than(&mut layouter, &x, BigUint::from(17u8))?;
    /// chip.assert_equal_to_fixed(&mut layouter, &check2, false)?;
    /// # });
    /// ```
    fn le_bits_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error>;

    /// Returns `true` iff the integer represented by the given sequence of
    /// assigned bits, interpreted in little-endian, is greater than or equal
    /// to the given bound.
    fn le_bits_geq_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error>;
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
    use num_traits::{One, Zero};
    use rand::{RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        types::InnerValue,
        utils::{
            circuit_modeling::circuit_to_json,
            util::{modulus, FromScratch},
        },
    };

    #[derive(Clone, Debug)]
    enum Operation {
        Canonical,
        Lower,
        Geq,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, Assigned, CanonicityChip>
    where
        Assigned: InnerValue,
    {
        bits: Vec<bool>,
        bound: BigUint,
        expected: bool,
        operation: Operation,
        _marker: PhantomData<(F, Assigned, CanonicityChip)>,
    }

    impl<F, Assigned, CanonicityChip> Circuit<F> for TestCircuit<F, Assigned, CanonicityChip>
    where
        F: PrimeField,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        CanonicityChip: CanonicityInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + AssertionInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        type Config = <CanonicityChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            CanonicityChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = CanonicityChip::new_from_scratch(&config);
            CanonicityChip::load_from_scratch(&mut layouter, &config);

            let bits = self
                .bits
                .iter()
                .map(|b| chip.assign_fixed(&mut layouter, *b))
                .collect::<Result<Vec<_>, Error>>()?;
            let bound = self.bound.clone();

            let res = match self.operation {
                Operation::Canonical => chip.is_canonical(&mut layouter, &bits),
                Operation::Lower => chip.le_bits_lower_than(&mut layouter, &bits, bound),
                Operation::Geq => chip.le_bits_geq_than(&mut layouter, &bits, bound),
            }?;

            chip.assert_equal_to_fixed(&mut layouter, &res, self.expected)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, Assigned, CanonicityChip>(
        bits: &[u8],
        bound: Option<&BigUint>,
        expected: bool,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        CanonicityChip: CanonicityInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + AssertionInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, Assigned, CanonicityChip> {
            bits: bits.iter().map(|b| *b != 0).collect::<Vec<_>>(),
            bound: bound.unwrap_or(&BigUint::default()).clone(),
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

    /// The output type is u8 instead of bool because, for readability, we
    /// express the test vectors with integers `0` and `1` instead of
    /// `false` and `true` (respectively).
    fn decompose_biguint(n: &BigUint) -> Vec<u8> {
        (0..(n.bits() as usize))
            .map(|i| if n.bit(i as u64) { 1 } else { 0 })
            .collect()
    }

    pub fn test_canonical<F, Assigned, CanonicityChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        CanonicityChip: CanonicityInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + AssertionInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let m = modulus::<Assigned::Element>();
        let mut cost_model = true;
        [
            (vec![0], true),
            (vec![1], true),
            (vec![1, 0, 1], true),
            (decompose_biguint(&m), false),
            (decompose_biguint(&(m - BigUint::one())), true),
            (vec![0; Assigned::Element::NUM_BITS as usize], true),
            (vec![1; Assigned::Element::NUM_BITS as usize], false),
            (vec![0; 1 + Assigned::Element::NUM_BITS as usize], false),
        ]
        .iter()
        .for_each(|(bits, expected)| {
            run::<F, Assigned, CanonicityChip>(
                bits,
                None,
                *expected,
                Operation::Canonical,
                true,
                cost_model,
                name,
                "canonical",
            );
            cost_model = false;
            run::<F, Assigned, CanonicityChip>(
                bits,
                None,
                !expected,
                Operation::Canonical,
                false,
                false,
                "",
                "",
            );
        });
    }

    pub fn test_le_bits_lower_and_geq<F, Assigned, CanonChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        Assigned::Element: PrimeField,
        Assigned: Instantiable<F> + InnerConstants + Clone,
        CanonChip: CanonicityInstructions<F, Assigned>
            + AssertionInstructions<F, Assigned>
            + AssertionInstructions<F, AssignedBit<F>>
            + AssignmentInstructions<F, Assigned>
            + FromScratch<F>,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let r: BigUint = rng.next_u64().into();
        let m = modulus::<Assigned::Element>();
        let mut cost_model = true;
        [
            (decompose_biguint(&r), r.clone() - BigUint::one(), true),
            (decompose_biguint(&r), r.clone(), true),
            (decompose_biguint(&r), r + BigUint::one(), false),
            (decompose_biguint(&m), m.clone(), true),
            (decompose_biguint(&m), m + BigUint::one(), false),
            (vec![0], BigUint::zero(), true),
            (vec![1], BigUint::zero(), true),
            (vec![1, 0, 1], BigUint::from(5u64), true),
            (vec![1, 0, 1], BigUint::from(6u64), false),
            (vec![1, 1, 1, 0, 0, 0], BigUint::from(7u64), true),
            (vec![1, 1, 1, 0, 0, 0], BigUint::from(8u64), false),
        ]
        .iter()
        .for_each(|(bits, bound, geq)| {
            run::<_, _, CanonChip>(
                bits,
                Some(bound),
                !geq,
                Operation::Lower,
                true,
                cost_model,
                name,
                "lt",
            );
            run::<_, _, CanonChip>(
                bits,
                Some(bound),
                *geq,
                Operation::Geq,
                true,
                cost_model,
                name,
                "geq",
            );
            cost_model = false;
            run::<_, _, CanonChip>(
                bits,
                Some(bound),
                *geq,
                Operation::Lower,
                false,
                false,
                "",
                "",
            );
            run::<_, _, CanonChip>(
                bits,
                Some(bound),
                !geq,
                Operation::Geq,
                false,
                false,
                "",
                "",
            );
        });
    }
}
