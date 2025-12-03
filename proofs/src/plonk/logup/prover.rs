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
//! - **Multiplicities `m(X)`**: Counts how many times each table entry is looked up
//! - **Helper `h(X)`**: Aggregates `Σⱼ 1/(fⱼ(X) + β)` at each row
//! - **Accumulator `Z(X)`**: Running sum of log-derivative differences

use std::{hash::Hash, iter};

use ff::{BatchInvert, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{evaluation::evaluate, Error, Expression, ProvingKey},
    poly::{
        commitment::PolynomialCommitmentScheme, Coeff, LagrangeCoeff, Polynomial,
        ProverQuery, Rotation,
    },
    transcript::{Hashable, Transcript},
    utils::arithmetic::{eval_polynomial, parallelize},
};
use crate::plonk::logup::FlattenArgument;

/// Committed LogUp polynomials in coefficient form.
#[cfg_attr(feature = "bench-internal", derive(Clone))]
#[derive(Debug)]
pub(crate) struct Committed<F: PrimeField> {
    pub(crate) multiplicities: Polynomial<F, Coeff>,
    pub(crate) helper_poly: Polynomial<F, Coeff>,
    pub(crate) aggregator_poly: Polynomial<F, Coeff>,
}

/// Committed polynomials after evaluation at challenge point.
pub(crate) struct Evaluated<F: PrimeField> {
    pub(crate) constructed: Committed<F>,
}

impl<F: WithSmallOrderMulGroup<3> + Hash> FlattenArgument<F> {
    /// Constructs and commits to the LogUp prover polynomials.
    ///
    /// Compresses input expressions via θ-batching, computes multiplicities and
    /// the helper polynomial using batch inversion, builds the running sum
    /// accumulator, and commits all three to the transcript.
    pub(crate) fn commit_logderivative<'a, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        self,
        pk: &ProvingKey<F, CS>,
        params: &CS::Parameters,
        beta: F,
        theta: F,
        advice_values: &'a [Polynomial<F, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<F, LagrangeCoeff>],
        instance_values: &'a [Polynomial<F, LagrangeCoeff>],
        challenges: &'a [F],
        transcript: &mut T,
    ) -> Result<Committed<F>, Error>
    where
        F: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        CS::Commitment: Hashable<T::Hash>,
    {
        let domain = pk.vk.get_domain();
        let n = domain.n as usize;
        let eval_expressions = |expressions: &[Expression<F>]| -> Vec<Polynomial<F, LagrangeCoeff>> {
            expressions.iter().map(|expression| {
                pk.vk.domain.lagrange_from_vec(evaluate(
                    expression,
                    n,
                    1,
                    fixed_values,
                    advice_values,
                    instance_values,
                    challenges,
                ))
            }).collect()
        };

        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<F>]| {
            let compressed_expression = eval_expressions(expressions).iter()
                .fold(domain.empty_lagrange(), |acc, expression| {
                    acc * theta + expression
                });
            compressed_expression
        };

        let compressed_input_expression = self.input_expressions.iter().map(|chunk| compress_expressions(chunk))
            .collect::<Vec<_>>();
        let compressed_table_expression = compress_expressions(&self.table_expressions);

        let multiplicities =
            compute_multiplicities(&compressed_input_expression, &compressed_table_expression);

        // We need to compute the helper polynomial, for which we need to do batch
        // inversion for the table.
        // T(X)   = 1 / (t(X)   + beta)
        let mut table_denoms = vec![F::ZERO; n];
        parallelize(&mut table_denoms, |input, start| {
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                *input = beta + compressed_table_expression.values[i];
            }
        });
        table_denoms.iter_mut().batch_invert();

        // F(X)   = 1 / (f(X)   + beta)
        // We compute a single vector for all advice columns
        // to compute a single `bach_invert`.
        let input_len = compressed_input_expression.len();
        let mut input_denoms = vec![F::ZERO; input_len * n];
        parallelize(&mut input_denoms, |input, start| {
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                *input = beta + compressed_input_expression[i / n].values[i % n];
            }
        });

        // Helper polynomials Σⱼ 1/(fⱼ(X) + β)
        input_denoms.iter_mut().batch_invert();
        let mut helper_poly = vec![F::ZERO; n];
        parallelize(&mut helper_poly, |input, start| {
            for (i, input) in input.iter_mut().enumerate() {
                let i = i + start;
                for j in 0..input_len {
                    *input += input_denoms[i + j * n];
                }
            }
        });

        // Polynomial over which we compute the running sum
        // logderivative_poly = h(X) - m(X)/(t(X) + β)
        let mut logderivative_poly = vec![F::ZERO; n];
        parallelize(&mut logderivative_poly, |poly, start| {
            for (i, coeff) in poly.iter_mut().enumerate() {
                let i = i + start;
                *coeff = helper_poly[i] - multiplicities[i] * table_denoms[i];
            }
        });

        // We take n-1 elements because the last row is verified by the identity check.
        let aggregator_poly = iter::once(F::ZERO)
            .chain(logderivative_poly.iter().cloned().take(n - 1))
            .scan(F::ZERO, |state, cur| {
                *state += cur;
                Some(*state)
            })
            .collect::<Vec<F>>();

        let multiplicities = pk.vk.domain.lagrange_from_vec(multiplicities);
        let helper_poly = pk.vk.domain.lagrange_from_vec(helper_poly);
        let aggregator_poly = pk.vk.domain.lagrange_from_vec(aggregator_poly);

        let multiplicities_commitment = CS::commit_lagrange(params, &multiplicities);
        transcript.write(&multiplicities_commitment)?;

        let helper_commitment = CS::commit_lagrange(params, &helper_poly);
        transcript.write(&helper_commitment)?;

        let aggregator_commitment = CS::commit_lagrange(params, &aggregator_poly);
        transcript.write(&aggregator_commitment)?;

        let multiplicities = pk.vk.domain.lagrange_to_coeff(multiplicities);
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
    /// Evaluates `m(x)`, `h(x)`, `Z(x)`, and `Z(ωx)`, writing them to the transcript.
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
        let logderivative_eval = eval_polynomial(&self.helper_poly, x);
        let aggregator_eval = eval_polynomial(&self.aggregator_poly, x);
        let aggregator_eval_next = eval_polynomial(&self.aggregator_poly, x_next);

        for eval in iter::once(multiplicities_eval)
            .chain(Some(logderivative_eval))
            .chain(Some(aggregator_eval))
            .chain(Some(aggregator_eval_next))
        {
            transcript.write(&eval)?;
        }

        Ok(Evaluated { constructed: self })
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

        iter::empty()
            // We need to open the aggregator at 1 (which should evaluate to zero)
            .chain(Some(ProverQuery {
                point: F::ONE,
                poly: &self.constructed.aggregator_poly,
            }))
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.multiplicities,
            }))
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.helper_poly,
            }))
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.constructed.aggregator_poly,
            }))
            .chain(Some(ProverQuery {
                point: x_next,
                poly: &self.constructed.aggregator_poly,
            }))
    }
}

/// Computes the multiplicity of each value in the polynomial.
///
/// Returns a vector where `result[i]` is the number of times `table[i]` appears
/// in `values`.
pub(crate) fn compute_multiplicities<F>(
    values: &[Polynomial<F, LagrangeCoeff>],
    table: &Polynomial<F, LagrangeCoeff>,
) -> Vec<F>
where
    F: PrimeField + std::hash::Hash + Eq,
{
    use std::collections::HashMap;

    let mut counts: HashMap<F, u32> = table.values.iter().map(|v| (*v, 0)).collect();
    for value in values {
        for v in value.iter() {
            *counts.entry(*v).or_insert(0) += 1;
        }
    }

    table.iter().map(|value| F::from(*counts.get(value).unwrap() as u64)).collect()
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

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
        // Table with a repeated value: [1, 2, 2, 3]
        // This tests that duplicate table entries get the same multiplicity
        let table = poly_from_vec(vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(2u64),
            Fq::from(3u64),
        ]);

        // Two input polynomials to test aggregation across multiple inputs
        // input1: [1, 2, 3, 3]
        // input2: [2, 2, 3, 4]
        // Note: 4 is NOT in the table - tests that extra values don't cause issues
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

        // Expected counts across both inputs:
        // - 1 appears 1 time
        // - 2 appears 3 times (1 in input1, 2 in input2)
        // - 3 appears 3 times (2 in input1, 1 in input2)
        // - 4 appears 1 time but is not in table

        let result = compute_multiplicities(&[input1, input2], &table);

        assert_eq!(result.len(), 4);
        assert_eq!(result[0], Fq::from(1u64)); // table[0]=1 -> count 1
        assert_eq!(result[1], Fq::from(3u64)); // table[1]=2 -> count 3
        assert_eq!(result[2], Fq::from(3u64)); // table[2]=2 -> count 3 (same as table[1])
        assert_eq!(result[3], Fq::from(3u64)); // table[3]=3 -> count 3
    }
}
