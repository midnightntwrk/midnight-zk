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
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    plonk::{Error, Expression, ProvingKey, evaluation::evaluate, logup::ChunkedArgument},
    poly::{LagrangeCoeff, Polynomial, commitment::PolynomialCommitmentScheme},
    utils::arithmetic::parallelize,
};

/// Computed multiplicities.
///
/// This structure holds the multiplicity counts computed from compressing
/// input and table expressions.
#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct ComputedMultiplicities<F: PrimeField> {
    pub(crate) argument_index: usize,
    pub(crate) selector: Polynomial<F, LagrangeCoeff>,
    pub(crate) chunked_compressed_inputs: Vec<Vec<Polynomial<F, LagrangeCoeff>>>,
    pub(crate) compressed_table_expression: Polynomial<F, LagrangeCoeff>,
}

/// Intermediate result from logderivative computation, before transcript
/// write and FFT conversion to coefficient form.
pub(crate) struct ComputedLogderivative<F: PrimeField> {
    pub(crate) argument_index: usize,
    pub(crate) helper_polys_lagrange: Vec<Vec<F>>,
    pub(crate) aggregator_poly: Polynomial<F, LagrangeCoeff>,
}

impl<F: WithSmallOrderMulGroup<3> + Hash> ChunkedArgument<F> {
    /// Compresses input and table expressions and computes the multiplicities.
    /// The multiplicities are neither committed nor written to the transcript:
    /// the caller commits them as part of the phase1 argument group.
    ///
    /// `blinding_values` are pre-generated random field elements for the
    /// blinding rows, so this method does not need `&mut rng` and can be
    /// called in parallel across lookups.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compute_multiplicities_parallel<'a, CS: PolynomialCommitmentScheme<F>>(
        &self,
        argument_index: usize,
        pk: &ProvingKey<F, CS>,
        theta: F,
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
        blinding_values: &[F],
    ) -> Result<(ComputedMultiplicities<F>, Polynomial<F, LagrangeCoeff>), Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        assert_eq!(blinding_values.len(), pk.vk.cs.blinding_factors() + 1);
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
                            0,
                            fixed_values,
                            advice_values,
                            instance_values,
                        ))
                    })
                    .collect()
            };

        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<F>]| {
            eval_expressions(expressions)
                .iter()
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * theta + expression
                })
        };

        let chunked_compressed_inputs: Vec<Vec<Polynomial<F, LagrangeCoeff>>> = self
            .input_expression_chunks
            .iter()
            .map(|chunk| chunk.iter().map(|exprs| compress_expressions(exprs)).collect())
            .collect();

        let all_compressed_inputs: Vec<&Polynomial<F, LagrangeCoeff>> =
            chunked_compressed_inputs.iter().flat_map(|v| v.iter()).collect();

        let compressed_table_expression = compress_expressions(&self.table_expressions);

        let selector = eval_expressions(std::slice::from_ref(&self.selector)).swap_remove(0);

        let usable_rows = n - pk.vk.cs.blinding_factors() - 1;
        let multiplicities = compute_multiplicities(
            &selector,
            &all_compressed_inputs,
            &compressed_table_expression,
            usable_rows,
            blinding_values,
        );

        let multiplicities = pk.vk.domain.lagrange_from_vec(multiplicities);

        Ok((
            ComputedMultiplicities {
                argument_index,
                selector,
                chunked_compressed_inputs,
                compressed_table_expression,
            },
            multiplicities,
        ))
    }
}

impl<F: WithSmallOrderMulGroup<3> + Hash> ComputedMultiplicities<F> {
    /// Constructs and commits to the LogUp prover polynomials, but does NOT
    /// write to the transcript or convert to coefficient form. The caller
    /// handles transcript ordering and can batch the FFTs.
    ///
    /// `blinding_values` must contain exactly `blinding_factors` random field
    /// elements. They are provided externally so the caller can pre-generate
    /// them from `&mut rng` and then invoke multiple lookups in parallel.
    ///
    /// `multiplicities` is borrowed from the phase1 argument group, which owns
    /// it once it has been committed.
    pub(crate) fn compute_logderivative<CS: PolynomialCommitmentScheme<F>>(
        self,
        pk: &ProvingKey<F, CS>,
        multiplicities: &Polynomial<F, LagrangeCoeff>,
        beta: F,
        blinding_values: Vec<F>,
    ) -> Result<ComputedLogderivative<F>, Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let blinding_factors = pk.vk.cs.blinding_factors();
        assert_eq!(blinding_values.len(), blinding_factors);
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
        let helper_polys_lagrange: Vec<Vec<F>> = self
            .chunked_compressed_inputs
            .par_iter()
            .map(|compressed_inputs| {
                let inverted_columns: Vec<Vec<F>> = compressed_inputs
                    .par_iter()
                    .map(|col| {
                        let mut denoms: Vec<F> = col.iter().map(|v| beta + v).collect();
                        denoms.iter_mut().batch_invert();
                        denoms
                    })
                    .collect();

                let mut helper = vec![F::ZERO; n];
                parallelize(&mut helper, |chunk, start| {
                    for (i, val) in chunk.iter_mut().enumerate() {
                        let row = i + start;
                        for col in &inverted_columns {
                            *val += col[row];
                        }
                    }
                });
                helper
            })
            .collect();

        // Helper polynomial commitments are deferred to the caller.

        // Polynomial over which we compute the running sum:
        //   logderivative_poly[i] = selector[i]·h[i] - m[i]/(t[i]+β)
        //
        // The selector applies only to the input side (h), not to the multiplicities
        // (m). m[i] counts how many selected inputs reference the table value
        // t[i], so it lives on table rows — not input rows. Gating m by the
        // selector would incorrectly exclude those table contributions,
        // breaking the logup balance.
        let mut logderivative_poly = vec![F::ZERO; n];
        parallelize(&mut logderivative_poly, |poly, start| {
            for (i, coeff) in poly.iter_mut().enumerate() {
                let i = i + start;
                let sum_helpers: F = helper_polys_lagrange.iter().map(|h| h[i]).sum();
                *coeff = self.selector[i] * sum_helpers - multiplicities[i] * table_denoms[i];
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
            .chain(blinding_values)
            .collect::<Vec<_>>();

        let aggregator_poly = pk.vk.domain.lagrange_from_vec(aggregator_poly);

        #[cfg(debug_assertions)]
        {
            let u = n - (blinding_factors + 1);

            // l_0(X) * z(X) = 0
            assert_eq!(aggregator_poly[0], F::ZERO);

            // Running sum must be zero at last active row for LogUp to be sound
            assert_eq!(aggregator_poly[u], F::ZERO);
        }

        Ok(ComputedLogderivative {
            argument_index: self.argument_index,
            helper_polys_lagrange,
            aggregator_poly,
        })
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
///
/// # Panics
///
/// Panics if any selected input value (where the selector is non-zero) is not
/// present in `table`.
pub(crate) fn compute_multiplicities<F>(
    selector: &Polynomial<F, LagrangeCoeff>,
    values: &[&Polynomial<F, LagrangeCoeff>],
    table: &Polynomial<F, LagrangeCoeff>,
    usable_rows: usize,
    blinding_values: &[F],
) -> Vec<F>
where
    F: PrimeField + std::hash::Hash + Eq,
{
    assert_eq!(blinding_values.len(), table.len() - usable_rows);
    use rustc_hash::FxHashMap;

    // Count how many times each value appears in the table (active rows only)
    let mut table_counts: FxHashMap<F, u32> = FxHashMap::default();
    for v in table.iter().take(usable_rows) {
        *table_counts.entry(*v).or_default() += 1;
    }

    // Count how many times each value appears in inputs (only where the selector is
    // non-zero).
    let mut input_counts: FxHashMap<F, u32> = table_counts.keys().map(|v| (*v, 0)).collect();
    for value in values.iter() {
        value
            .iter()
            .zip(selector.iter())
            .take(usable_rows)
            .filter(|(_, sel)| !sel.is_zero_vartime())
            .for_each(|(v, _)| {
                *input_counts
                    .get_mut(v)
                    .unwrap_or_else(|| panic!("input value {v:?} not found in lookup table")) += 1;
            });
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
                F::ONE // Random blinding factors will be applied later
            }
        })
        .collect();
    table_count_inverses.iter_mut().batch_invert();

    // Compute normalized multiplicities: input_count / table_count
    // Blinding rows get random values to ensure ZK.
    table
        .iter()
        .enumerate()
        .zip(table_count_inverses)
        .map(|((i, value), table_count_inv)| {
            if i < usable_rows {
                let input_count = *input_counts.get(value).unwrap_or(&0);
                F::from(input_count as u64) * table_count_inv
            } else {
                blinding_values[i - usable_rows]
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

        let result = compute_multiplicities(
            &poly_from_vec(vec![Fq::ONE; 4]),
            &[&input1, &input2],
            &table,
            4,
            &[],
        );

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
        compute_multiplicities(&poly_from_vec(vec![Fq::ONE; 4]), &[&input], &table, 4, &[]);
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

        let result =
            compute_multiplicities(&poly_from_vec(vec![Fq::ONE; 4]), &[&input], &table, 4, &[]);

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

        let blinding = [Fq::from(42u64), Fq::from(43u64)];
        let result = compute_multiplicities(
            &poly_from_vec(vec![Fq::ONE; 4]),
            &[&input],
            &table,
            2,
            &blinding,
        );

        assert_eq!(result.len(), 4);
        assert_eq!(result[0], Fq::from(1u64)); // table[0]=1 -> 1/1 = 1
        assert_eq!(result[1], Fq::from(1u64)); // table[1]=2 -> 1/1 = 1
        assert_eq!(result[2], blinding[0]); // blinding row
        assert_eq!(result[3], blinding[1]); // blinding row
    }
}
