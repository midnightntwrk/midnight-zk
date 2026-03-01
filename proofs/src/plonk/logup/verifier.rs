// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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
        logup::{self, FlattenedArgument},
        Error, VerifyingKey,
    },
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, Rotation, VerifierQuery},
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
    pub(crate) evaluated: logup::Evaluated<F>,
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
            evaluated: logup::Evaluated {
                multiplicities_eval,
                helper_eval,
                accumulator_eval,
                accumulator_next_eval,
            },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
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
                self.evaluated.multiplicities_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.helper_poly,
                self.evaluated.helper_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x,
                CommitmentLabel::NoLabel,
                &self.committed.accumulator,
                self.evaluated.accumulator_eval,
            )))
            .chain(Some(VerifierQuery::new(
                x_next,
                CommitmentLabel::NoLabel,
                &self.committed.accumulator,
                self.evaluated.accumulator_next_eval,
            )))
    }
}
