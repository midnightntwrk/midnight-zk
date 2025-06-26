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

//! Binary instructions interface.
//!
//! It provides functions for performing Boolean operations over [AssignedBit]s.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::types::AssignedBit;

/// The set of circuit instructions for binary operations.
pub trait BinaryInstructions<F: PrimeField> {
    /// Conjunction of the given assigned bits.
    ///
    /// # Panics
    ///
    /// If `bits.len() == 0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let b0 = chip.assign(&mut layouter, Value::known(false))?;
    /// let b1 = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let res = chip.and(&mut layouter, &[b0, b1])?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, false)?;
    /// # });
    /// ```
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let res = chip.and(&mut layouter, &[])?;
    /// # });
    /// ```
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error>;

    /// Disjunction of the given assigned bits.
    ///
    /// # Panics
    ///
    /// If `bits.len() == 0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let b0 = chip.assign(&mut layouter, Value::known(false))?;
    /// let b1 = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let res = chip.or(&mut layouter, &[b0, b1])?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, true)?;
    /// # });
    /// ```
    fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error>;

    /// Exclusive-OR of all the given assigned bits.
    ///
    /// # Panics
    ///
    /// If `bits.len() == 0`.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let b0 = chip.assign(&mut layouter, Value::known(false))?;
    /// let b1 = chip.assign(&mut layouter, Value::known(true))?;
    /// let b2 = chip.assign(&mut layouter, Value::known(true))?;
    ///
    /// let res = chip.xor(&mut layouter, &[b0, b1, b2])?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, false)?;
    /// # });
    /// ```
    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error>;

    /// Negation of the given assigned bit.
    ///
    /// ```
    /// # midnight_circuits::run_test_native_gadget!(chip, layouter, {
    /// let b = chip.assign(&mut layouter, Value::known(false))?;
    ///
    /// let res = chip.not(&mut layouter, &b)?;
    /// chip.assert_equal_to_fixed(&mut layouter, &res, true)?;
    /// # });
    /// ```
    fn not(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error>;
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

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Copy, Debug)]
    enum Operation {
        And,
        Or,
        Xor,
        Not,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, BinaryChip> {
        inputs: Vec<bool>,
        expected: bool,
        operation: Operation,
        _marker: PhantomData<(F, BinaryChip)>,
    }

    impl<F, BinaryChip> Circuit<F> for TestCircuit<F, BinaryChip>
    where
        F: PrimeField,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        type Config = <BinaryChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            BinaryChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = BinaryChip::new_from_scratch(&config);
            BinaryChip::load_from_scratch(&mut layouter, &config);

            // b2 does not apply in tests of arity-1 functions.
            let b2_idx = min(self.inputs.len() - 1, 1);
            let b1 = chip.assign(&mut layouter, Value::known(self.inputs[0]))?;
            let b2 = chip.assign(&mut layouter, Value::known(self.inputs[b2_idx]))?;

            let res = match self.operation {
                Operation::And => chip.and(&mut layouter, &[b1, b2]),
                Operation::Or => chip.or(&mut layouter, &[b1, b2]),
                Operation::Xor => chip.xor(&mut layouter, &[b1, b2]),
                Operation::Not => chip.not(&mut layouter, &b1),
            }?;

            chip.assert_equal_to_fixed(&mut layouter, &res, self.expected)
        }
    }

    fn run<F, BinaryChip>(
        inputs: &[bool],
        expected: bool,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        let circuit = TestCircuit::<F, BinaryChip> {
            inputs: inputs.to_vec(),
            expected,
            operation,
            _marker: PhantomData,
        };
        let log2_nb_rows = 5;
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

    fn test_binary_op<F, BinaryChip>(
        inputs: &[u8],
        expected: u8,
        operation: Operation,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        let inputs = inputs.iter().map(|b| *b == 1).collect::<Vec<_>>();
        let expected = expected == 1;
        run::<F, BinaryChip>(
            &inputs, expected, operation, true, cost_model, chip_name, op_name,
        );
        run::<F, BinaryChip>(
            &inputs, !expected, operation, false, false, chip_name, op_name,
        );
    }

    pub fn test_and<F, BinaryChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        test_binary_op::<F, BinaryChip>(&[0, 0], 0, Operation::And, true, name, "and");
        test_binary_op::<F, BinaryChip>(&[0, 1], 0, Operation::And, false, "", "");
        test_binary_op::<F, BinaryChip>(&[1, 0], 0, Operation::And, false, "", "");
        test_binary_op::<F, BinaryChip>(&[1, 1], 1, Operation::And, false, "", "");
    }

    pub fn test_or<F, BinaryChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        test_binary_op::<F, BinaryChip>(&[0, 0], 0, Operation::Or, true, name, "or");
        test_binary_op::<F, BinaryChip>(&[0, 1], 1, Operation::Or, false, "", "");
        test_binary_op::<F, BinaryChip>(&[1, 0], 1, Operation::Or, false, "", "");
        test_binary_op::<F, BinaryChip>(&[1, 1], 1, Operation::Or, false, "", "");
    }

    pub fn test_xor<F, BinaryChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        test_binary_op::<F, BinaryChip>(&[0, 0], 0, Operation::Xor, true, name, "xor");
        test_binary_op::<F, BinaryChip>(&[0, 1], 1, Operation::Xor, false, "", "");
        test_binary_op::<F, BinaryChip>(&[1, 0], 1, Operation::Xor, false, "", "");
        test_binary_op::<F, BinaryChip>(&[1, 1], 0, Operation::Xor, false, "", "");
    }

    pub fn test_not<F, BinaryChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        BinaryChip: BinaryInstructions<F>
            + AssignmentInstructions<F, AssignedBit<F>>
            + AssertionInstructions<F, AssignedBit<F>>
            + FromScratch<F>,
    {
        test_binary_op::<F, BinaryChip>(&[0], 1, Operation::Not, true, name, "not");
        test_binary_op::<F, BinaryChip>(&[1], 0, Operation::Not, false, "", "");
    }
}
