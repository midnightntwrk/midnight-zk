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

use ff::{Field, PrimeField};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use num_bigint::{BigInt, RandBigInt};
use num_traits::Zero;
use pasta_curves::Fp;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use super::{
    chip::{P2RDecompositionChip, P2RDecompositionConfig},
    instructions::CoreDecompositionInstructions,
};
use crate::{
    field::{
        decomposition::{
            cpu_utils::{decompose_in_variable_limbsizes, variable_limbsize_coefficients},
            pow2range::Pow2RangeChip,
        },
        native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
        NativeChip,
    },
    instructions::{ArithInstructions, AssertionInstructions, AssignmentInstructions},
    types::AssignedNative,
    utils::{util::bigint_to_fe, ComposableChip},
};

#[test]
fn test_decompose_variable_in_cpu() {
    let mut rng = ChaCha8Rng::from_entropy();

    // sample 6 random limb sizes in the range (0..16)
    let mut limb_sizes = (0..6)
        .map(|_| rng.gen_range(0..16usize))
        .collect::<Vec<_>>();
    // add at least a non-zero limb size
    limb_sizes.push(rng.gen_range(1..16usize));

    // sample a random field element that can be represented with the above limb
    // sizes
    let max_bound: u128 = 1 << limb_sizes.iter().sum::<usize>();
    let x = Fp::from_u128(rng.gen_range(0..max_bound));

    // compute limbs and coefficients
    let limbs = decompose_in_variable_limbsizes::<Fp, Fp>(&x, limb_sizes.as_slice());
    let coefficients = variable_limbsize_coefficients::<Fp>(limb_sizes.as_slice());

    // reconstruct the number
    let reconstructed = limbs
        .iter()
        .zip(coefficients.iter())
        .fold(Fp::zero(), |acc, (limb, c)| acc + limb * c);

    assert_eq!(x, reconstructed);
}

#[derive(Clone, Debug)]
// enum defining the test type
enum LimbType {
    // variable size limbs that test the decompose_core function
    Variable(Vec<usize>),
    // fixed size limbs that test the fixed decomposition
    Fixed((usize, usize)),
}

#[derive(Clone, Debug)]
struct TestDecompositionCircuit<F: PrimeField, const NR_COLS: usize> {
    input: F,
    limb_sizes: LimbType,
    expected: Vec<F>,
}

impl<F, const NR_COLS: usize> Circuit<F> for TestDecompositionCircuit<F, NR_COLS>
where
    F: PrimeField,
{
    type Config = P2RDecompositionConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice_columns: [_; NB_ARITH_COLS] = core::array::from_fn(|_| meta.advice_column());
        let fixed_columns: [_; NB_ARITH_FIXED_COLS] = core::array::from_fn(|_| meta.fixed_column());
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns,
                fixed_columns,
                [committed_instance_column, instance_column],
            ),
        );
        let pow2range_config = Pow2RangeChip::configure(meta, &advice_columns[1..=NR_COLS]);

        P2RDecompositionConfig::new(&native_config, &pow2range_config)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let max_bit_len = 8;
        let native_chip = NativeChip::<F>::new(&config.native_config, &());
        let pow2range_chip = Pow2RangeChip::<F>::new(&config.pow2range_config, max_bit_len);

        pow2range_chip.load_table(&mut layouter)?;

        let decomposition_chip = P2RDecompositionChip::new(&config, &max_bit_len);

        let assigned_input: AssignedNative<F> =
            native_chip.assign(&mut layouter, Value::known(self.input))?;

        // compute the decomposition limbs
        let computed_limbs = match self.limb_sizes.clone() {
            // for the variable case we use decompose_core
            LimbType::Variable(limb_sizes) => {
                let (_, limbs) = decomposition_chip.decompose_core(
                    &mut layouter,
                    assigned_input.value().copied(),
                    limb_sizes.as_slice(),
                )?;
                Ok(limbs)
            }
            LimbType::Fixed((bit_length, limb_size)) => {
                // for the fixed case we use decompose_fixed_limb_size
                decomposition_chip.decompose_fixed_limb_size(
                    &mut layouter,
                    &assigned_input,
                    bit_length,
                    limb_size,
                )
            }
        }?;

        // assign the expected decomposition limbs
        let assigned_expected_result = self
            .expected
            .iter()
            .map(|limb| native_chip.assign(&mut layouter, Value::known(*limb)))
            .collect::<Result<Vec<_>, _>>()?;

        // check that the result is equal to the expected
        computed_limbs
            .iter()
            .zip(assigned_expected_result.iter())
            .try_for_each(|(x, y)| native_chip.assert_equal(&mut layouter, x, y))?;

        // re-compue the linear combinaion of the limbs and assert it agrees with the
        // input number. This is an extra sanity check.
        let terms_owned = match self.limb_sizes.clone() {
            LimbType::Variable(limb_sizes) => {
                // compute the term coefficient off circuit and zip them with the limbs
                // to create the linear combination terms
                variable_limbsize_coefficients(limb_sizes.as_slice())
                    .iter()
                    .filter(|c: &&F| **c != F::ZERO)
                    .copied()
                    .zip(computed_limbs.iter().cloned())
                    .collect::<Vec<(F, AssignedNative<F>)>>()
            }
            LimbType::Fixed((bit_length, limb_size)) => {
                let mut limb_sizes = vec![limb_size; bit_length / limb_size];
                if bit_length % limb_size != 0 {
                    limb_sizes.push(bit_length % limb_size)
                }
                variable_limbsize_coefficients(limb_sizes.as_slice())
                    .iter()
                    .copied()
                    .zip(computed_limbs.iter().cloned())
                    .collect::<Vec<(F, AssignedNative<F>)>>()
            }
        };

        let terms = terms_owned
            .iter()
            .map(|(c, v)| (*c, v.clone()))
            .collect::<Vec<_>>();

        let lc_result = native_chip.linear_combination(&mut layouter, terms.as_slice(), F::ZERO)?;

        native_chip.assert_equal(&mut layouter, &lc_result, &assigned_input)
    }
}

fn run_decomposition_chip_variable_test<const NR_COLS: usize>() {
    const K: u32 = 10;

    let mut rng = ChaCha8Rng::from_entropy();

    let mut limb_sizes = Vec::new();

    // sample random limb sizes of the form:
    // [
    //      a, a, a, a, a, a, a,
    //      b, b, b, b,
    //      c, c, c, c, c, c,
    // ]

    for i in [7, 4, 6] {
        let limb_size_group = rng.gen_range(1..=8usize);
        for _ in 0..i {
            limb_sizes.push(limb_size_group);
        }
        while limb_sizes.len() % NR_COLS != 0 {
            limb_sizes.push(0);
        }
    }

    // sample a random field element that can be represented with the above limb
    // sizes
    let max_bound: u128 = 1 << limb_sizes.iter().sum::<usize>();
    let x = Fp::from_u128(rng.gen_range(0..max_bound));

    let non_zero_limb_sizes = limb_sizes
        .iter()
        .filter(|x| !x.is_zero())
        .copied()
        .collect::<Vec<_>>();
    let expected = decompose_in_variable_limbsizes(&x, non_zero_limb_sizes.as_slice());

    let circuit_variable = TestDecompositionCircuit::<Fp, NR_COLS> {
        input: x,
        limb_sizes: LimbType::Variable(limb_sizes),
        expected,
    };
    let prover = MockProver::run(K, &circuit_variable, vec![vec![], vec![]])
        .expect("Failed to run mock prover");
    prover.assert_satisfied();
}

#[test]
fn test_decomposition_chip_variable() {
    run_decomposition_chip_variable_test::<1>();
    run_decomposition_chip_variable_test::<2>();
    run_decomposition_chip_variable_test::<3>();
    run_decomposition_chip_variable_test::<4>();
}

fn run_decomposition_chip_fixed_test<const NR_COLS: usize>() {
    const K: u32 = 10;

    let mut rng = ChaCha8Rng::from_entropy();

    // sample two random limb sizes:
    //  - a random limb size in the range 1..8 (less than max_limb_length)
    let limb_size_small = rng.gen_range(1..=8);
    //  - a random limb size in the range 9..42 (greater than max_limb_length)
    let limb_size_big = rng.gen_range(9..=42usize);

    // sample a random field element
    let x = Fp::random(rng);

    for limb_size in [limb_size_small, limb_size_big] {
        let mut limb_sizes = vec![limb_size; Fp::NUM_BITS as usize / limb_size];
        if Fp::NUM_BITS as usize % limb_size != 0 {
            limb_sizes.push(Fp::NUM_BITS as usize % limb_size)
        }

        let expected = decompose_in_variable_limbsizes(&x, limb_sizes.as_slice());

        let circuit_fixed = TestDecompositionCircuit::<Fp, NR_COLS> {
            input: x,
            limb_sizes: LimbType::Fixed((Fp::NUM_BITS as usize, limb_size)),
            expected,
        };

        let prover = MockProver::run(K, &circuit_fixed, vec![vec![], vec![]])
            .expect("Failed to run mock prover");
        prover.assert_satisfied();
    }
}

#[test]
fn test_decomposition_chip_fixed() {
    run_decomposition_chip_fixed_test::<1>();
    run_decomposition_chip_fixed_test::<2>();
    run_decomposition_chip_fixed_test::<3>();
    run_decomposition_chip_fixed_test::<4>();
}

#[derive(Clone, Debug)]
struct TestLessThanPow2Circuit<F: PrimeField, const NR_COLS: usize> {
    input: F,
    bound: usize,
}

impl<F, const NR_COLS: usize> Circuit<F> for TestLessThanPow2Circuit<F, NR_COLS>
where
    F: PrimeField,
{
    type Config = P2RDecompositionConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice_columns: [_; NB_ARITH_COLS] = core::array::from_fn(|_| meta.advice_column());
        let fixed_columns: [_; NB_ARITH_FIXED_COLS] = core::array::from_fn(|_| meta.fixed_column());
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns,
                fixed_columns,
                [committed_instance_column, instance_column],
            ),
        );
        let pow2range_config = Pow2RangeChip::configure(meta, &advice_columns[1..=NR_COLS]);

        P2RDecompositionConfig::new(&native_config, &pow2range_config)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let max_bit_len = 8;
        let native_chip = NativeChip::<F>::new(&config.native_config, &());
        let pow2range_chip = Pow2RangeChip::<F>::new(&config.pow2range_config, max_bit_len);

        pow2range_chip.load_table(&mut layouter)?;

        let decomposition_chip = P2RDecompositionChip::new(&config, &max_bit_len);

        // assign the element to be decomposed
        let assigned_input = native_chip.assign(&mut layouter, Value::known(self.input))?;

        decomposition_chip.assert_less_than_pow2(&mut layouter, &assigned_input, self.bound)
    }
}

fn run_decomposition_less_than_pow2_test<const NR_COLS: usize>() {
    const K: u32 = 10;

    let mut rng = ChaCha8Rng::from_entropy();

    // sample a random power in the range 1..255
    let bound = rng.gen_range(1..255usize);

    // sample a random field element
    let max_value = BigInt::from(1) << bound;
    let bign = rng.gen_bigint_range(&BigInt::zero(), &max_value);

    let x: Fp = bigint_to_fe(&bign);

    let circuit = TestLessThanPow2Circuit::<Fp, NR_COLS> { input: x, bound };

    let prover =
        MockProver::run(K, &circuit, vec![vec![], vec![]]).expect("Failed to run mock prover");
    prover.assert_satisfied();
}

#[test]
fn test_decomposition_less_than_pow2() {
    run_decomposition_less_than_pow2_test::<1>();
    run_decomposition_less_than_pow2_test::<2>();
    run_decomposition_less_than_pow2_test::<3>();
    run_decomposition_less_than_pow2_test::<4>();
}
