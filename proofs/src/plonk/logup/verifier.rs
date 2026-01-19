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

//! Verifier implementation for the LogUp lookup argument.

use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{
    plonk::{logup::FlattenArgument, Error, VerifyingKey},
    poly::{commitment::PolynomialCommitmentScheme, Rotation, VerifierQuery},
    transcript::{Hashable, Transcript},
};

/// Commitments to the LogUp polynomials, read from the transcript.
#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    multiplicities: CS::Commitment,
    helper_poly: CS::Commitment,
    accumulator: CS::Commitment,
}

/// Commitments plus evaluations at challenge point.
pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    committed: Committed<F, CS>,
    multiplicities_eval: F,
    helper_eval: F,
    accumulator_eval: F,
    accumulator_next_eval: F,
}

impl<F: WithSmallOrderMulGroup<3>> FlattenArgument<F> {
    /// Reads the prover's commitments from the transcript.
    pub(in crate::plonk) fn read_commitment<T: Transcript, CS: PolynomialCommitmentScheme<F>>(
        &self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let multiplicities = transcript.read()?;
        let helper_poly = transcript.read()?;
        let accumulator = transcript.read()?;

        Ok(Committed {
            multiplicities,
            helper_poly,
            accumulator,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    /// Reads polynomial evaluations from the transcript.
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let multiplicities_eval = transcript.read()?;
        let helper_eval = transcript.read()?;
        let accumulator_eval = transcript.read()?;
        let accumulator_next_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            multiplicities_eval,
            helper_eval,
            accumulator_eval,
            accumulator_next_eval,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    /// Computes the constraint expressions.
    ///
    /// Checks two identities:
    /// - **Helper constraint**: `h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)`
    /// - **Accumulator constraint**: `Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) +
    ///   β) - m(x)`
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_last: F,
        l_blind: F,
        argument: &'a FlattenArgument<F>,
        theta: F,
        beta: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        use crate::plonk::circuit::Expression;

        let active_rows = F::ONE - (l_last + l_blind);
        // Evaluate expressions the same way the prover does
        let evaluate_expressions = |expressions: &[Expression<F>]| {
            expressions
                .iter()
                .map(|expression| {
                    expression.evaluate(
                        &|scalar| scalar,
                        &|_| panic!("virtual selectors are removed during optimization"),
                        &|query| fixed_evals[query.index.unwrap()],
                        &|query| advice_evals[query.index.unwrap()],
                        &|query| instance_evals[query.index.unwrap()],
                        &|challenge| challenges[challenge.index()],
                        &|a| -a,
                        &|a, b| a + b,
                        &|a, b| a * b,
                        &|a, scalar| a * scalar,
                    )
                })
                .collect::<Vec<_>>()
        };
        // Compress expressions the same way the prover does
        let compress_expressions = |expressions: &[Expression<F>]| {
            evaluate_expressions(expressions)
                .iter()
                .fold(F::ZERO, |acc, eval| acc * theta + eval)
        };

        let compressed_table = compress_expressions(&argument.table_expressions);

        let compressed_inputs_with_beta = argument
            .input_expressions
            .iter()
            .map(|input| {
                let compressed = compress_expressions(input);
                compressed + beta
            })
            .collect::<Vec<_>>();

        let partial_products: Vec<F> = (0..compressed_inputs_with_beta.len())
            .map(|i| {
                let mut acc = F::ONE;
                for (j, input) in compressed_inputs_with_beta.iter().enumerate() {
                    if j != i {
                        acc *= input;
                    }
                }
                acc
            })
            .collect();

        // Helper polynomial constraint: h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)
        // This ensures the helper polynomial has the correct structure for LogUp
        // soundness. Note: This must hold everywhere (as a polynomial
        // identity), not just at active rows.
        let product: F = compressed_inputs_with_beta.iter().product();
        let sum: F = partial_products.iter().sum();
        let helper_expression = || self.helper_eval * product - sum;

        // LogUp accumulator constraint: Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) + β) -
        // m(x) Rearranging: Z(ωx)·(t(x) + β) - (Z(x) + h(x))·(t(x) + β) + m(x)
        // = 0
        let accumulator_constraint = || {
            let diff = self.accumulator_next_eval * (compressed_table + beta)
                - (self.accumulator_eval + self.helper_eval) * (compressed_table + beta)
                + self.multiplicities_eval;
            diff * active_rows
        };

        std::iter::empty()
            .chain(Some(helper_expression()))
            .chain(Some(accumulator_constraint()))
    }

    /// Returns verification queries.
    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone {
        let x_next = vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            // Z(1) = 0
            .chain(Some(VerifierQuery::new(
                F::ONE,
                &self.committed.accumulator,
                F::ZERO,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                &self.committed.multiplicities,
                self.multiplicities_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                &self.committed.helper_poly,
                self.helper_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                &self.committed.accumulator,
                self.accumulator_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x_next,
                &self.committed.accumulator,
                self.accumulator_next_eval,
            )))
    }
}
