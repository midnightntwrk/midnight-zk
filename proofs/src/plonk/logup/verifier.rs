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
        logup::{self, ChunkedArgument},
        Error, VerifyingKey,
    },
    poly::{
        commitment::{Labelable, PolynomialCommitmentScheme},
        PolynomialLabel, Rotation, VerifierQuery,
    },
    transcript::{Hashable, Transcript},
};

/// Commitment to the shared multiplicity polynomial, read from the transcript.
pub struct CommittedMultiplicities<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    multiplicities: CS::Commitment,
}

/// Commitments to all LogUp polynomials for a [`ChunkedArgument`].
///
/// One shared `m` and `Z`, plus one `hᵢ` per chunk.
#[derive(Debug)]
pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    name: String,
    multiplicities: CS::Commitment,
    /// One commitment per chunk of the batched argument.
    helper_polys: Vec<CS::Commitment>,
    accumulator: CS::Commitment,
}

/// Commitments plus evaluations at the challenge point.
pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    committed: Committed<F, CS>,
    pub(crate) evaluated: logup::Evaluated<F>,
}

/// Reads the **batched** multiplicities commitment for all logup arguments
/// in one transcript entry and hands each argument a clone of the shared
/// commitment. The shared object carries the full label list (one
/// `LogupMultiplicities(name)` per arg); per-arg queries route to the
/// correct sub-bundle via `find_bundle`.
pub(in crate::plonk) fn read_all_multiplicities<F, CS, T>(
    args: &[ChunkedArgument<F>],
    transcript: &mut T,
) -> Result<Vec<CommittedMultiplicities<F, CS>>, Error>
where
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    if args.is_empty() {
        return Ok(Vec::new());
    }
    let labels: Vec<_> = args
        .iter()
        .map(|a| PolynomialLabel::LogupMultiplicities(a.name.clone()))
        .collect();
    let shared = transcript.read::<CS::Commitment>()?.label(labels);
    Ok(args
        .iter()
        .map(|_| CommittedMultiplicities {
            multiplicities: shared.clone(),
        })
        .collect())
}

/// Reads the **batched** helper commitments for all logup arguments in one
/// transcript entry. Each helper carries a unique label
/// `LogupHelper(name, chunk_idx)`. Per-arg views (carrying the relevant
/// subset of helpers) are reconstructed by walking the args' chunk counts.
pub(in crate::plonk) fn read_all_helpers<F, CS, T>(
    args_with_multiplicities: Vec<(ChunkedArgRef, CommittedMultiplicities<F, CS>)>,
    transcript: &mut T,
) -> Result<Vec<HelpersOnly<F, CS>>, Error>
where
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    if args_with_multiplicities.is_empty() {
        return Ok(Vec::new());
    }
    // Build the full label set in (arg, chunk) order, matching the prover's
    // flat iteration.
    let mut labels: Vec<PolynomialLabel> = Vec::new();
    for (arg, _) in &args_with_multiplicities {
        for chunk_idx in 0..arg.num_chunks {
            labels.push(PolynomialLabel::LogupHelper(arg.name.clone(), chunk_idx));
        }
    }
    if labels.is_empty() {
        // No helpers across any arg — prover skipped the write.
        return Ok(args_with_multiplicities
            .into_iter()
            .map(|(arg, m)| HelpersOnly {
                name: arg.name,
                multiplicities: m.multiplicities,
                helper_polys: Vec::new(),
            })
            .collect());
    }
    let shared = transcript.read::<CS::Commitment>()?.label(labels);

    // Hand each arg its own clone of the shared commitment. Each clone
    // carries the full label list; `find_bundle` routes per-chunk queries
    // to the right sub-bundle.
    Ok(args_with_multiplicities
        .into_iter()
        .map(|(arg, m)| {
            let helper_polys = vec![shared.clone(); arg.num_chunks];
            HelpersOnly {
                name: arg.name,
                multiplicities: m.multiplicities,
                helper_polys,
            }
        })
        .collect())
}

/// Lightweight per-arg view passed into [`read_all_helpers`] — just the name
/// and chunk count, both reconstructible from the verifying key.
pub(in crate::plonk) struct ChunkedArgRef {
    pub(in crate::plonk) name: String,
    pub(in crate::plonk) num_chunks: usize,
}

/// Partial state between per-arg helper reads and the batched aggregator read.
pub(in crate::plonk) struct HelpersOnly<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    name: String,
    multiplicities: CS::Commitment,
    helper_polys: Vec<CS::Commitment>,
}

/// Reads the **batched** aggregator commitment for all logup arguments and
/// assembles one [`Committed`] per arg, each holding a clone of the shared
/// aggregator commitment.
pub(in crate::plonk) fn read_all_aggregators<F, CS, T>(
    helpers: Vec<HelpersOnly<F, CS>>,
    transcript: &mut T,
) -> Result<Vec<Committed<F, CS>>, Error>
where
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: Hashable<T::Hash>,
    T: Transcript,
{
    if helpers.is_empty() {
        return Ok(Vec::new());
    }
    let labels: Vec<_> = helpers
        .iter()
        .map(|h| PolynomialLabel::LogupAggregator(h.name.clone()))
        .collect();
    let shared_agg = transcript.read::<CS::Commitment>()?.label(labels);
    Ok(helpers
        .into_iter()
        .map(|h| Committed {
            name: h.name,
            multiplicities: h.multiplicities,
            helper_polys: h.helper_polys,
            accumulator: shared_agg.clone(),
        })
        .collect())
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    /// Reads the polynomial evaluations from the transcript.
    ///
    /// Order: `m_eval`, then `hᵢ_eval` for each batched chunk, then `Z_eval`,
    /// `Z(ωx)_eval`.
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash>,
    {
        let nb_chunks = self.helper_polys.len();

        let multiplicities_eval = transcript.read()?;
        let helper_evals =
            (0..nb_chunks).map(|_| transcript.read()).collect::<Result<Vec<_>, _>>()?;
        let accumulator_eval = transcript.read()?;
        let accumulator_next_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            evaluated: logup::Evaluated {
                multiplicities_eval,
                helper_evals,
                accumulator_eval,
                accumulator_next_eval,
            },
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    /// Returns verification queries for all committed polynomials.
    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<'_, F, CS>> + Clone {
        let x_next = vk.domain.rotate_omega(x, Rotation::next());
        let name = self.committed.name.clone();

        let m_query = iter::once(VerifierQuery::new(
            x,
            &self.committed.multiplicities,
            self.evaluated.multiplicities_eval,
            PolynomialLabel::LogupMultiplicities(name.clone()),
        ));

        let helper_queries = self
            .committed
            .helper_polys
            .iter()
            .zip(self.evaluated.helper_evals.iter())
            .enumerate()
            .map(move |(chunk_idx, (com, &eval))| {
                VerifierQuery::new(
                    x,
                    com,
                    eval,
                    PolynomialLabel::LogupHelper(name.clone(), chunk_idx),
                )
            })
            .collect::<Vec<_>>();

        let name = self.committed.name.clone();
        let z_queries = [
            VerifierQuery::new(
                x,
                &self.committed.accumulator,
                self.evaluated.accumulator_eval,
                PolynomialLabel::LogupAggregator(name.clone()),
            ),
            VerifierQuery::new(
                x_next,
                &self.committed.accumulator,
                self.evaluated.accumulator_next_eval,
                PolynomialLabel::LogupAggregator(name),
            ),
        ];

        m_query.chain(helper_queries).chain(z_queries)
    }
}
