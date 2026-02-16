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
    plonk::{Error, VerifyingKey, logup::FlattenedArgument},
    poly::{CommitmentLabel, Rotation, VerifierQuery, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Transcript},
};

/// Commitment to LogUp multiplicities
pub struct CommittedMultiplicities<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    multiplicities: CS::Commitment,
}

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

impl<F: WithSmallOrderMulGroup<3>> FlattenedArgument<F> {
    /// Reads the multiplicities commitment from the transcript.
    pub(in crate::plonk) fn read_multiplicities<T: Transcript, CS: PolynomialCommitmentScheme<F>>(
        &self,
        transcript: &mut T,
    ) -> Result<CommittedMultiplicities<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let multiplicities = transcript.read()?;
        Ok(CommittedMultiplicities { multiplicities })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>
    CommittedMultiplicities<F, CS>
{
    /// Reads the prover's commitments from the transcript.
    pub(in crate::plonk) fn read_commitment<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let helper_poly = transcript.read()?;
        let accumulator = transcript.read()?;

        Ok(Committed {
            multiplicities: self.multiplicities,
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
    /// When a lookup involves multiple columns, `theta` is used as a random
    /// challenge to compress them into a single value via a random linear
    /// combination. That is, given expressions `(e₁, ..., eₗ)`, the compressed
    /// value is `e₁·θˡ⁻¹ + e₂·θˡ⁻² + ... + eₗ`. Both the input values `fⱼ`
    /// and the table value `t` are compressed this way before being
    /// substituted into the LogUp identities.
    ///
    /// Checks two identities (where `fⱼ` and `t` denote the compressed values):
    /// - **Helper constraint**: `h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)`
    /// - **Accumulator constraint**: `Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) +
    ///   β) - m(x)`
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_0: F,
        l_last: F,
        l_blind: F,
        argument: &'a FlattenedArgument<F>,
        theta: F,
        beta: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        use crate::plonk::circuit::Expression;

        let active_rows = F::ONE - (l_last + l_blind);
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

        // Helper polynomial constraint: h(x) · ∏ⱼ(fⱼ(x) + β) = Σⱼ ∏_{k≠j}(fₖ(x) + β)
        // This ensures the helper polynomial has the correct structure for LogUp
        // soundness. Note: This must hold everywhere (as a polynomial
        // identity), not just at active rows.
        let product: F = compressed_inputs_with_beta.iter().product();

        // Compute partial products:
        // ∏_{k≠j}(fₖ(x) + β) = product / (fⱼ(x) + β)
        let partial_products: Vec<F> = compressed_inputs_with_beta
            .iter()
            .map(|input| product * input.invert().unwrap())
            .collect();
        let sum: F = partial_products.iter().sum();
        let helper_expression = || self.helper_eval * product - sum;

        // LogUp accumulator constraint:
        // Z(ωx)·(t(x) + β) = (Z(x) + h(x))·(t(x) + β) - m(x)
        // Rearranging: (Z(ωx) - Z(x) - h(x)) · (t(x) + β) + m(x) = 0
        let accumulator_constraint = || {
            let diff = (self.accumulator_next_eval - self.accumulator_eval - self.helper_eval)
                * (compressed_table + beta)
                + self.multiplicities_eval;
            diff * active_rows
        };

        [
            (l_0 + l_last) * self.accumulator_eval,
            helper_expression(),
            accumulator_constraint(),
        ]
        .into_iter()
    }

    /// Returns verification queries.
    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        let x_next = vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.multiplicities,
                self.multiplicities_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.helper_poly,
                self.helper_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.accumulator,
                self.accumulator_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x_next,
                CommitmentLabel::NoLabel,
                &self.committed.accumulator,
                self.accumulator_next_eval,
            )))
    }
}
