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

//! This configure is used to constrain an assigned value as 16-bit long.
//! An assigned value is firstly copy constrained with the cell in a_1
//! then we decompose the value in chunks of 2-bit in the cells a_2, a_3,
//! up to a_9. Finally, we enforce the correctness of the decomposition
//! and each chunk is 2-bit long.
//
// | s_range16 | a_1  |    a_2     |    a_3     | ... |    a_9      |
// |-----------|------|------------|------------|-----|-------------|
// |    1      | half | half[0..2] | half[2..4] | ... |half[14..16] |
//
// Constraints:
//
// 1) a_1 = a_2 + a_3 * 2^2 + a_4 * 2^4 + .. + a_9 * 2^{14}
// 2) a_i \in {0, 1, 2, 3} for i = 2, 3, .. 9

use ff::PrimeField;
use midnight_proofs::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use super::Gate;
use crate::hash::sha256::AssignedBits;

#[derive(Clone, Debug)]
pub struct Range16Config {
    selector: Selector,
    cols: [Column<Advice>; 9],
}

impl Range16Config {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        a_1: Column<Advice>,
        a_2: Column<Advice>,
        a_3: Column<Advice>,
        a_4: Column<Advice>,
        a_5: Column<Advice>,
        a_6: Column<Advice>,
        a_7: Column<Advice>,
        a_8: Column<Advice>,
        a_9: Column<Advice>,
    ) -> Self {
        let selector = meta.selector();
        meta.create_gate("16-bit range check", |meta| {
            let s_range16 = meta.query_selector(selector);
            let cols: [Expression<F>; 9] = [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9]
                .map(|col| meta.query_advice(col, Rotation::cur()));

            let lhs = cols[0].clone();
            let rhs = cols[1..]
                .iter()
                .rev()
                .fold(Expression::Constant(F::ZERO), |acc, coeff| {
                    acc * F::from(1 << 2) + coeff.clone()
                });
            // check the identity a_1 = a_2 + a_3 * 2 + .. + a_9 * 2^{14}
            let decompose_check = rhs + lhs * (Expression::Constant(-F::ONE));
            // for i = 2,..9, check each a_i \in {0, 1, 2, 3}
            let cols_range2_check: Vec<Expression<F>> = cols[1..]
                .iter()
                .map(|coeff| Gate::range_check(coeff.clone(), 0, 3))
                .collect();

            let mut all_checks = Vec::new();
            all_checks.push(decompose_check);
            all_checks.extend(cols_range2_check);
            all_checks
                .into_iter()
                .map(move |poly| s_range16.clone() * poly)
        });

        Range16Config {
            selector,
            cols: [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9],
        }
    }

    pub(crate) fn assign_halves_vector<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        assigned_halves: &[AssignedBits<16, F>],
    ) -> Result<(), Error> {
        assigned_halves
            .iter()
            .enumerate()
            .try_for_each(|(i, assigned_half)| {
                self.decompose_16bits(region, assigned_half.clone(), offset + i)
            })
    }

    /// Assign 2-bit chunks of the assigned half
    fn decompose_16bits<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        assigned_half: AssignedBits<16, F>,
        offset: usize,
    ) -> Result<(), Error> {
        let half_val = assigned_half.value();
        let [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9] = self.cols;

        self.selector.enable(region, offset)?;
        // assign 16-bit half
        let half =
            AssignedBits::<16, F>::assign_bits(region, || "16-bit half", a_1, offset, half_val)?;

        // equality constraint for the newly assigned half and the previous one
        region.constrain_equal(assigned_half.cell(), half.cell())?;

        fn decompose_array(input: [bool; 16]) -> Vec<Vec<bool>> {
            input.chunks_exact(2).map(|chunk| chunk.to_vec()).collect()
        }

        let pieces = half_val.map(|bits| decompose_array(bits.0));
        let pieces = pieces.transpose_vec(8);

        // assign half[0..2]
        AssignedBits::<2, F>::assign_bits(region, || "half[0..2]", a_2, offset, pieces[0].clone())?;
        // assign half[2..4]
        AssignedBits::<2, F>::assign_bits(region, || "half[2..4]", a_3, offset, pieces[1].clone())?;
        // assign half[4..6]
        AssignedBits::<2, F>::assign_bits(region, || "half[4..6]", a_4, offset, pieces[2].clone())?;
        // assign half[6..8]
        AssignedBits::<2, F>::assign_bits(region, || "half[6..8]", a_5, offset, pieces[3].clone())?;
        // assign half[8..10]
        AssignedBits::<2, F>::assign_bits(
            region,
            || "half[8..10]",
            a_6,
            offset,
            pieces[4].clone(),
        )?;
        // assign half[10..12]
        AssignedBits::<2, F>::assign_bits(
            region,
            || "half[10..12]",
            a_7,
            offset,
            pieces[5].clone(),
        )?;
        // assign half[12..14]
        AssignedBits::<2, F>::assign_bits(
            region,
            || "half[12..14]",
            a_8,
            offset,
            pieces[6].clone(),
        )?;
        // assign half[14..16]
        AssignedBits::<2, F>::assign_bits(
            region,
            || "half[14..16]",
            a_9,
            offset,
            pieces[7].clone(),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use halo2curves::pasta::Fp;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::{AssignedBits, Range16Config};

    struct TestCircuit {
        inputs: [[bool; 16]; 10],
    }
    #[derive(Clone, Debug)]
    struct CircuitConfig {
        range16_config: Range16Config,
        inputs_col: Column<Advice>,
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit {
        type Config = CircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let [inputs_col, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9]: [Column<Advice>; 10] =
                std::array::from_fn(|_i| meta.advice_column());
            let range16_config =
                Range16Config::configure(meta, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9);

            let constants_column = meta.fixed_column();
            meta.enable_constant(constants_column);

            for col in [inputs_col, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9].iter() {
                meta.enable_equality(*col);
            }

            CircuitConfig {
                range16_config,
                inputs_col,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let assigned_inputs = layouter.assign_region(
                || "assign the public inputs",
                |mut region| {
                    self.inputs
                        .into_iter()
                        .enumerate()
                        .map(|(i, input)| {
                            AssignedBits::<16, F>::assign_bits_fixed(
                                &mut region,
                                || "assign public input",
                                config.inputs_col,
                                i,
                                input,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()
                },
            )?;

            layouter.assign_region(
                || "assign range16 gate",
                |mut region| {
                    config
                        .range16_config
                        .assign_halves_vector(&mut region, 0, &assigned_inputs)
                },
            )
        }
    }

    #[test]
    fn test_range16() {
        let mut rng = ChaCha8Rng::from_entropy();
        let random_array: [[bool; 16]; 10] = std::array::from_fn(|_| {
            std::array::from_fn(|_| rng.gen_bool(0.5)) // 50% chance for `true`
                                                       // or `false`
        });

        let circuit = TestCircuit {
            inputs: random_array,
        };

        let prover = match MockProver::<Fp>::run(12, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };

        prover.assert_satisfied();
    }
}
