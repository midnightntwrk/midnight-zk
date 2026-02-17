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

//! Prover implementation for the LogUp lookup argument.
//!
//! Constructs and commits to three polynomials:
//! - **Multiplicities `m(X)`**: Counts how many times each table entry is
//!   looked up
//! - **Helper `h(X)`**: Aggregates at each row `Σⱼ 1/(fⱼ(X) + β)`, where j
//!   iterates over columns
//! - **Accumulator `Z(X)`**: Running sum of log-derivative differences

use std::{hash::Hash, iter};

use ff::{BatchInvert, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand_core::{CryptoRng, RngCore};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    plonk::{
        evaluation::evaluate,
        logup::{self, FlattenedArgument},
        Error, Expression, ProvingKey,
    },
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, LagrangeCoeff, Polynomial, ProverQuery,
        Rotation,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::{eval_polynomial, parallelize},
};

/// Committed LogUp polynomials in coefficient form.
#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField> {
    pub(crate) multiplicities: Polynomial<F, Coeff>,
    pub(crate) helper_poly: Polynomial<F, Coeff>,
    pub(crate) aggregator_poly: Polynomial<F, Coeff>,
}

/// Computed multiplicities.
///
/// This structure holds the multiplicity counts computed from compressing
/// input and table expressions.
#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct ComputedMultiplicities<F: PrimeField> {
    pub(crate) multiplicities: Polynomial<F, LagrangeCoeff>,
    pub(crate) compressed_input_expression: Vec<Polynomial<F, LagrangeCoeff>>,
    pub(crate) compressed_table_expression: Polynomial<F, LagrangeCoeff>,
}

/// Committed polynomials after evaluation at challenge point.
pub(crate) struct Evaluated<F: PrimeField> {
    pub(crate) constructed: Committed<F>,
    pub(crate) evaluated: logup::Evaluated<F>,
}

impl<F: WithSmallOrderMulGroup<3> + Hash> FlattenedArgument<F> {
    /// Compresses input and table expressions and computes multiplicities.
    ///
    /// This method evaluates and compresses the input/table expressions using
    /// θ-batching, then counts how many times each table entry appears in the
    /// inputs.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_multiplicities<'a, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        &self,
        pk: &ProvingKey<F, CS>,
        params: &CS::Parameters,
        theta: F,
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
        challenges: &'a [F],
        transcript: &mut T,
    ) -> Result<ComputedMultiplicities<F>, Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let domain = pk.vk.get_domain();
        let n = domain.n as usize;
        let eval_expressions =
            |expressions: &[Expression<F>]| -> Vec<Polynomial<F, LagrangeCoeff>> {
                expressions
                    .iter()
                    .map(|expression| {
                        pk.vk.domain.lagrange_from_vec(evaluate(
                            expression,
                            n,
                            1,
                            fixed_values,
                            advice_values,
                            instance_values,
                            challenges,
                        ))
                    })
                    .collect()
            };

        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<F>]| {
            let compressed_expression = eval_expressions(expressions)
                .iter()
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * theta + expression
                });
            compressed_expression
        };

        let compressed_input_expression = self
            .input_expressions
            .iter()
            .map(|chunk| compress_expressions(chunk))
            .collect::<Vec<_>>();
        let compressed_table_expression = compress_expressions(&self.table_expressions);

        let usable_rows = n - pk.vk.cs.blinding_factors() - 1;
        let multiplicities = compute_multiplicities(
            &compressed_input_expression,
            &compressed_table_expression,
            usable_rows,
        );

        let multiplicities = pk.vk.domain.lagrange_from_vec(multiplicities);
        let multiplicities_commitment = CS::commit_lagrange(params, &multiplicities);
        transcript.write(&multiplicities_commitment)?;

        Ok(ComputedMultiplicities {
            multiplicities,
            compressed_input_expression,
            compressed_table_expression,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3> + Hash> ComputedMultiplicities<F> {
    /// Constructs and commits to the LogUp prover polynomials.
    ///
    /// Compresses input expressions via θ-batching, computes the helper
    /// polynomial using batch inversion, builds the running sum
    /// accumulator, and commits all three to the transcript.
    pub(crate) fn commit_logderivative<CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        self,
        pk: &ProvingKey<F, CS>,
        params: &CS::Parameters,
        beta: F,
        mut rng: impl RngCore + CryptoRng,
        transcript: &mut T,
    ) -> Result<Committed<F>, Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let blinding_factors = pk.vk.cs.blinding_factors();
        let domain = pk.vk.get_domain();
        let n = domain.n as usize;

        // We need to compute the helper polynomial, for which we need to do batch
        // inversion for the table.
        // T(X) = 1 / (t(X) + beta)
        let mut table_denoms = vec![F::ZERO; n];
        parallelize(&mut table_denoms, |input, start| {
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                *input = beta + self.compressed_table_expression.values[i];
            }
        });
        table_denoms.iter_mut().batch_invert();

        // F(X) = 1 / (f(X) + beta)
        // Invert each column independently in parallel, then sum across columns
        // to form the helper polynomial Σⱼ 1/(fⱼ(X) + β).
        let inverted_columns: Vec<Vec<F>> = self
            .compressed_input_expression
            .par_iter()
            .map(|col| {
                let mut denoms: Vec<F> = col.iter().map(|v| beta + v).collect();
                denoms.iter_mut().batch_invert();
                denoms
            })
            .collect();

        let mut helper_poly = vec![F::ZERO; n];
        parallelize(&mut helper_poly, |chunk, start| {
            for (i, val) in chunk.iter_mut().enumerate() {
                let row = i + start;
                for col in &inverted_columns {
                    *val += col[row];
                }
            }
        });

        // Polynomial over which we compute the running sum
        // logderivative_poly = h(X) - m(X)/(t(X) + β)
        let mut logderivative_poly = vec![F::ZERO; n];
        parallelize(&mut logderivative_poly, |poly, start| {
            for (i, coeff) in poly.iter_mut().enumerate() {
                let i = i + start;
                *coeff = helper_poly[i] - self.multiplicities[i] * table_denoms[i];
            }
        });

        let aggregator_poly = iter::once(F::ZERO)
            .chain(logderivative_poly)
            .scan(F::ZERO, |state, cur| {
                *state += cur;
                Some(*state)
            })
            // Take all rows including the "last" row.
            .take(n - blinding_factors)
            // Chain random blinding factors.
            .chain((0..blinding_factors).map(|_| F::random(&mut rng)))
            .collect::<Vec<_>>();

        let helper_poly = pk.vk.domain.lagrange_from_vec(helper_poly);
        let aggregator_poly = pk.vk.domain.lagrange_from_vec(aggregator_poly);

        #[cfg(debug_assertions)]
        {
            let u = n - (blinding_factors + 1);

            // l_0(X) * z(X) = 0
            assert_eq!(aggregator_poly[0], F::ZERO);

            // Running sum must be zero at last active row for LogUp to be sound
            assert_eq!(aggregator_poly[u], F::ZERO);
        }

        let helper_commitment = CS::commit_lagrange(params, &helper_poly);
        transcript.write(&helper_commitment)?;

        let aggregator_commitment = CS::commit_lagrange(params, &aggregator_poly);
        transcript.write(&aggregator_commitment)?;

        let multiplicities = pk.vk.domain.lagrange_to_coeff(self.multiplicities);
        let helper_poly = pk.vk.domain.lagrange_to_coeff(helper_poly);
        let aggregator_poly = pk.vk.domain.lagrange_to_coeff(aggregator_poly);

        Ok(Committed {
            multiplicities,
            helper_poly,
            aggregator_poly,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Committed<F> {
    /// Evaluates `m(x)`, `h(x)`, `Z(x)`, and `Z(ωx)`, writing them to the
    /// transcript.
    pub(crate) fn evaluate<T: Transcript, CS: PolynomialCommitmentScheme<F>>(
        self,
        pk: &ProvingKey<F, CS>,
        x: F,
        transcript: &mut T,
    ) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let domain = &pk.vk.domain;
        let x_next = domain.rotate_omega(x, Rotation::next());

        let multiplicities_eval = eval_polynomial(&self.multiplicities, x);
        let helper_eval = eval_polynomial(&self.helper_poly, x);
        let accumulator_eval = eval_polynomial(&self.aggregator_poly, x);
        let accumulator_next_eval = eval_polynomial(&self.aggregator_poly, x_next);
        for eval in [
            &multiplicities_eval,
            &helper_eval,
            &accumulator_eval,
            &accumulator_next_eval,
        ] {
            transcript.write(eval)?;
        }

        Ok(Evaluated {
            constructed: self,
            evaluated: logup::Evaluated {
                multiplicities_eval,
                helper_eval,
                accumulator_eval,
                accumulator_next_eval,
            },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluated<F> {
    /// Returns opening queries.
    pub(crate) fn open<'a, CS: PolynomialCommitmentScheme<F>>(
        &'a self,
        pk: &'a ProvingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = ProverQuery<'a, F>> + Clone {
        let x_next = pk.vk.domain.rotate_omega(x, Rotation::next());

        [
            ProverQuery {
                point: x,
                poly: &self.constructed.multiplicities,
            },
            ProverQuery {
                point: x,
                poly: &self.constructed.helper_poly,
            },
            ProverQuery {
                point: x,
                poly: &self.constructed.aggregator_poly,
            },
            ProverQuery {
                point: x_next,
                poly: &self.constructed.aggregator_poly,
            },
        ]
        .into_iter()
    }
}

/// Computes the multiplicity of each value in the polynomial.
///
/// Returns a vector where `result[i]` is the number of times `table[i]` appears
/// in `values`.
///
/// When a value appears multiple times in the table, the multiplicity is
/// normalized: if a value is looked up `k` times and appears `t` times in the
/// table, each table position gets multiplicity `k/t`.
///
/// Only values in the first `usable_rows` are counted for both inputs and
/// table. Blinding rows are excluded from the counting but still get a
/// multiplicity value (zero for values not in the active region).
pub(crate) fn compute_multiplicities<F>(
    values: &[Polynomial<F, LagrangeCoeff>],
    table: &Polynomial<F, LagrangeCoeff>,
    usable_rows: usize,
) -> Vec<F>
where
    F: PrimeField + std::hash::Hash + Eq,
{
    use rustc_hash::FxHashMap;

    // Count how many times each value appears in the table (active rows only)
    let mut table_counts: FxHashMap<F, u32> = FxHashMap::default();
    for v in table.iter().take(usable_rows) {
        *table_counts.entry(*v).or_default() += 1;
    }

    // Count how many times each value appears in inputs (active rows only)
    let mut input_counts: FxHashMap<F, u32> = table_counts.keys().map(|v| (*v, 0)).collect();
    for value in values.iter() {
        for v in value.iter().take(usable_rows) {
            *input_counts.get_mut(v).expect("input value not found in lookup table") += 1;
        }
    }

    // Build vector of table counts for batch inversion (only for active table
    // values)
    let mut table_count_inverses: Vec<F> = table
        .iter()
        .enumerate()
        .map(|(i, value)| {
            if i < usable_rows {
                F::from(*table_counts.get(value).unwrap_or(&1) as u64)
            } else {
                F::ONE // Blinding rows - will be multiplied by zero input count
                       // anyway
            }
        })
        .collect();
    table_count_inverses.iter_mut().batch_invert();

    // Compute normalized multiplicities: input_count / table_count
    // For blinding rows, multiplicity is 0 (input count is 0 for random blinding
    // values)
    table
        .iter()
        .enumerate()
        .zip(table_count_inverses)
        .map(|((i, value), table_count_inv)| {
            if i < usable_rows {
                let input_count = *input_counts.get(value).unwrap_or(&0);
                F::from(input_count as u64) * table_count_inv
            } else {
                F::ZERO
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use ff::Field;
    use midnight_curves::Fq;

    use super::*;

    fn poly_from_vec(values: Vec<Fq>) -> Polynomial<Fq, LagrangeCoeff> {
        Polynomial {
            values,
            _marker: PhantomData,
        }
    }

    #[test]
    fn test_compute_multiplicities() {
        // Table with unique values: [1, 2, 3, 4]
        let table = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(3u64),
            Fq::from(4u64),
        ]);

        // Two input polynomials to test aggregation across multiple inputs
        // input1: [1, 2, 3, 3]
        // input2: [2, 2, 3, 4]
        let input1 = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(3u64),
            Fq::from(3u64),
        ]);
        let input2 = poly_from_vec(vec![
            Fq::from(2u64),
            Fq::from(2u64),
            Fq::from(3u64),
            Fq::from(4u64),
        ]);

        // Expected counts across both inputs (all 4 rows are usable):
        // - 1 appears 1 time
        // - 2 appears 3 times (1 in input1, 2 in input2)
        // - 3 appears 3 times (2 in input1, 1 in input2)
        // - 4 appears 1 time

        let result = compute_multiplicities(&[input1, input2], &table, 4);

        assert_eq!(result.len(), 4);
        assert_eq!(result[0], Fq::from(1u64)); // table[0]=1 -> count 1
        assert_eq!(result[1], Fq::from(3u64)); // table[1]=2 -> count 3
        assert_eq!(result[2], Fq::from(3u64)); // table[2]=3 -> count 3
        assert_eq!(result[3], Fq::from(1u64)); // table[3]=4 -> count 1
    }

    #[test]
    #[should_panic]
    fn test_compute_multiplicities_value_not_in_table() {
        // Table with values: [1, 2, 3, 4]
        let table = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(3u64),
            Fq::from(4u64),
        ]);

        // Input contains value 5, which is NOT in the table
        let input = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(5u64),
            Fq::from(3u64),
        ]);

        // Should panic because input value 5 is not found in the table
        compute_multiplicities(&[input], &table, 4);
    }

    #[test]
    fn test_compute_multiplicities_with_duplicate_table_values() {
        // Table: [1, 2, 2, 3] - value 2 appears twice
        let table = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(2u64),
            Fq::from(3u64),
        ]);

        // Input looks up: 1 once, 2 twice, 3 once
        let input = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(2u64),
            Fq::from(3u64),
        ]);

        let result = compute_multiplicities(&[input], &table, 4);

        assert_eq!(result.len(), 4);
        assert_eq!(result[0], Fq::from(1u64)); // table[0]=1 -> 1/1 = 1
                                               // Value 2: looked up 2 times, appears 2 times in table -> each gets 2/2 = 1
        assert_eq!(result[1], Fq::from(1u64)); // table[1]=2 -> 2/2 = 1
        assert_eq!(result[2], Fq::from(1u64)); // table[2]=2 -> 2/2 = 1
        assert_eq!(result[3], Fq::from(1u64)); // table[3]=3 -> 1/1 = 1
    }

    #[test]
    fn test_compute_multiplicities_with_blinding_rows() {
        // Table: [1, 2, 0, 0] - last 2 rows are "blinding" with default 0
        // Only first 2 rows are usable
        let table = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(0u64),
            Fq::from(0u64),
        ]);

        // Input: [1, 2, random, random] - but we only count first 2 rows
        let input = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(999u64), // "random" blinding value
            Fq::from(888u64), // "random" blinding value
        ]);

        let result = compute_multiplicities(&[input], &table, 2);

        assert_eq!(result.len(), 4);
        assert_eq!(result[0], Fq::from(1u64)); // table[0]=1 -> 1/1 = 1
        assert_eq!(result[1], Fq::from(1u64)); // table[1]=2 -> 1/1 = 1
        assert_eq!(result[2], Fq::ZERO); // blinding row -> 0
        assert_eq!(result[3], Fq::ZERO); // blinding row -> 0
    }
}
