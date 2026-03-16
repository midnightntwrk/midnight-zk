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
    plonk::{
        logup::{self, BatchedArgument},
        Error, VerifyingKey,
    },
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, Rotation, VerifierQuery},
    transcript::{Hashable, Transcript},
};

/// Commitment to the shared multiplicity polynomial, read from the transcript.
pub struct BatchCommittedMultiplicities<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    multiplicities: CS::Commitment,
}

/// Commitments to all LogUp polynomials for a [`BatchedArgument`].
///
/// One shared `m` and `Z`, plus one `hᵢ` per flattened argument.
#[derive(Debug)]
pub struct BatchCommitted<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    multiplicities: CS::Commitment,
    /// One commitment per flattened argument.
    helper_polys: Vec<CS::Commitment>,
    accumulator: CS::Commitment,
}

/// Commitments plus evaluations at challenge point.
pub struct BatchEvaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    committed: BatchCommitted<F, CS>,
    pub(crate) evaluated: logup::BatchEvaluated<F>,
}

impl<F: WithSmallOrderMulGroup<3>> BatchedArgument<F> {
    /// Reads the shared multiplicity commitment from the transcript.
    pub(in crate::plonk) fn read_multiplicities<
        T: Transcript,
        CS: PolynomialCommitmentScheme<F>,
    >(
        &self,
        transcript: &mut T,
    ) -> Result<BatchCommittedMultiplicities<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let multiplicities = transcript.read()?;
        Ok(BatchCommittedMultiplicities { multiplicities })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>
    BatchCommittedMultiplicities<F, CS>
{
    /// Reads `nb_flattened` helper commitments and one accumulator commitment
    /// from the transcript.
    pub(in crate::plonk) fn read_commitment<T: Transcript>(
        self,
        nb_flattened: usize,
        transcript: &mut T,
    ) -> Result<BatchCommitted<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let helper_polys =
            (0..nb_flattened).map(|_| transcript.read()).collect::<Result<Vec<_>, _>>()?;
        let accumulator = transcript.read()?;

        Ok(BatchCommitted { multiplicities: self.multiplicities, helper_polys, accumulator })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> BatchCommitted<F, CS> {
    /// Reads polynomial evaluations from the transcript.
    ///
    /// Order: `m_eval`, then `hᵢ_eval` for each flattened arg, then `Z_eval`,
    /// `Z(ωx)_eval`.
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<BatchEvaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let nb_flattened = self.helper_polys.len();

        let multiplicities_eval = transcript.read()?;
        let helper_evals =
            (0..nb_flattened).map(|_| transcript.read()).collect::<Result<Vec<_>, _>>()?;
        let accumulator_eval = transcript.read()?;
        let accumulator_next_eval = transcript.read()?;

        Ok(BatchEvaluated {
            committed: self,
            evaluated: logup::BatchEvaluated {
                multiplicities_eval,
                helper_evals,
                accumulator_eval,
                accumulator_next_eval,
            },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> BatchEvaluated<F, CS> {
    /// Returns verification queries for all committed polynomials.
    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        let x_next = vk.domain.rotate_omega(x, Rotation::next());

        let m_query = iter::once(VerifierQuery::new(
            x,
            CommitmentLabel::NoLabel,
            &self.committed.multiplicities,
            self.evaluated.multiplicities_eval,
        ));

        let helper_queries = self
            .committed
            .helper_polys
            .iter()
            .zip(self.evaluated.helper_evals.iter())
            .map(move |(com, &eval)| VerifierQuery::new(x, CommitmentLabel::NoLabel, com, eval))
            .collect::<Vec<_>>();

        let z_queries = [
            VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.accumulator,
                self.evaluated.accumulator_eval,
            ),
            VerifierQuery::new(
                x_next,
                CommitmentLabel::NoLabel,
                &self.committed.accumulator,
                self.evaluated.accumulator_next_eval,
            ),
        ];

        m_query.chain(helper_queries).chain(z_queries)
    }
}
