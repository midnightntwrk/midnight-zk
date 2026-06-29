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

//! In-circuit lookup argument verification.
//!
//! This is the in-circuit analog of `proofs/src/plonk/logup/verifier.rs`.
//! The constraint expressions are implemented in `expressions/lookup.rs`.

use midnight_proofs::{circuit::Layouter, plonk::Error, poly::PolynomialLabel};

use crate::{
    field::AssignedNative,
    verifier::{
        kzg::VerifierQuery, transcript_gadget::TranscriptGadget, utils::AssignedBoundedScalar,
        AssignedCommitment, SelfEmulation,
    },
};

/// Commitment to the multiplicity columns, read from the transcript.
#[derive(Clone, Debug)]
pub(crate) struct CommittedMultiplicities<S: SelfEmulation> {
    multiplicities: AssignedCommitment<S>,
}

#[derive(Clone, Debug)]
pub(crate) struct LookupEvaluated<S: SelfEmulation> {
    pub(crate) multiplicities_eval: AssignedNative<S::F>,
    pub(crate) helper_evals: Vec<AssignedNative<S::F>>,
    pub(crate) accumulator_eval: AssignedNative<S::F>,
    pub(crate) accumulator_next_eval: AssignedNative<S::F>,
}

/// Commitments to the LogUp polynomials, read from the transcript.
#[derive(Clone, Debug)]
pub(crate) struct Committed<S: SelfEmulation> {
    multiplicities: AssignedCommitment<S>,
    helper_polys: Vec<AssignedCommitment<S>>,
    accumulator: AssignedCommitment<S>,
}

/// Commitments plus evaluations at challenge point.
#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation> {
    committed: Committed<S>,
    pub(crate) evaluated: LookupEvaluated<S>,
}

/// Reads the **batched** multiplicities commitment for all logup arguments.
/// Mirrors the off-circuit `logup::verifier::read_all_multiplicities`: one
/// `[u32 len=n][n points]` blob, where each point is the multiplicities
/// commitment for one arg.
pub(crate) fn read_all_multiplicities<S: SelfEmulation>(
    names: &[String],
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Vec<CommittedMultiplicities<S>>, Error> {
    if names.is_empty() {
        return Ok(Vec::new());
    }
    let points = transcript_gadget.read_batched_commitment(layouter, names.len())?;
    Ok(points
        .into_iter()
        .zip(names.iter())
        .map(|(p, name)| CommittedMultiplicities {
            multiplicities: AssignedCommitment::new(
                p,
                vec![PolynomialLabel::LogupMultiplicities(name.clone())],
            ),
        })
        .collect())
}

/// Partial state between per-arg helper reads and the batched aggregator
/// read.
#[derive(Clone, Debug)]
pub(crate) struct HelpersOnly<S: SelfEmulation> {
    name: String,
    multiplicities: AssignedCommitment<S>,
    helper_polys: Vec<AssignedCommitment<S>>,
}

/// Reads the **batched** helper commitments for all logup arguments in one
/// transcript entry, one point per (arg, chunk). Each point is labeled with
/// its unique `LogupHelper(name, chunk_idx)`; per-arg views are
/// reconstructed by walking the `(name, num_chunks)` pairs in input order.
/// Mirrors the off-circuit `logup::verifier::read_all_helpers`.
pub(crate) fn read_all_helpers<S: SelfEmulation>(
    args_with_multiplicities: Vec<(String, usize, CommittedMultiplicities<S>)>,
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Vec<HelpersOnly<S>>, Error> {
    let total: usize = args_with_multiplicities.iter().map(|(_, n, _)| *n).sum();
    if total == 0 {
        // No helpers anywhere — prover skipped the write.
        return Ok(args_with_multiplicities
            .into_iter()
            .map(|(name, _, m)| HelpersOnly {
                name,
                multiplicities: m.multiplicities,
                helper_polys: Vec::new(),
            })
            .collect());
    }
    let points = transcript_gadget.read_batched_commitment(layouter, total)?;
    // Distribute the points across args in input order.
    let mut points_iter = points.into_iter();
    Ok(args_with_multiplicities
        .into_iter()
        .map(|(name, nb_chunks, m)| {
            let helper_polys: Vec<_> = (0..nb_chunks)
                .map(|chunk_idx| {
                    let p = points_iter.next().expect("helper point count mismatch");
                    AssignedCommitment::new(
                        p,
                        vec![PolynomialLabel::LogupHelper(name.clone(), chunk_idx)],
                    )
                })
                .collect();
            HelpersOnly {
                name,
                multiplicities: m.multiplicities,
                helper_polys,
            }
        })
        .collect())
}

/// Reads the **batched** aggregator commitment for all logup arguments
/// and assembles one [`Committed`] per arg. Mirrors the off-circuit
/// `logup::verifier::read_all_aggregators`.
pub(crate) fn read_all_aggregators<S: SelfEmulation>(
    helpers: Vec<HelpersOnly<S>>,
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Vec<Committed<S>>, Error> {
    if helpers.is_empty() {
        return Ok(Vec::new());
    }
    let points = transcript_gadget.read_batched_commitment(layouter, helpers.len())?;
    Ok(points
        .into_iter()
        .zip(helpers)
        .map(|(p, h)| Committed {
            multiplicities: h.multiplicities,
            helper_polys: h.helper_polys,
            accumulator: AssignedCommitment::new(p, vec![PolynomialLabel::LogupAggregator(h.name)]),
        })
        .collect())
}

impl<S: SelfEmulation> Committed<S> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S>, Error> {
        let nb_flattened = self.helper_polys.len();
        let multiplicities_eval = transcript_gadget.read_scalar(layouter)?;
        let helper_evals = (0..nb_flattened)
            .map(|_| transcript_gadget.read_scalar(layouter))
            .collect::<Result<Vec<_>, Error>>()?;
        let accumulator_eval = transcript_gadget.read_scalar(layouter)?;
        let accumulator_next_eval = transcript_gadget.read_scalar(layouter)?;

        Ok(Evaluated {
            committed: self,
            evaluated: LookupEvaluated {
                multiplicities_eval,
                helper_evals,
                accumulator_eval,
                accumulator_next_eval,
            },
        })
    }
}

// "expressions" is implemented in `expressions/lookup.rs`

impl<S: SelfEmulation> Evaluated<S> {
    pub(crate) fn queries(
        &self,
        one: &AssignedBoundedScalar<S::F>, // 1
        x: &AssignedNative<S::F>,          // evaluation point x
        x_next: &AssignedNative<S::F>,     // ωx
    ) -> Vec<VerifierQuery<S>> {
        let mut queries = vec![
            // Open lookup product commitment at x
            VerifierQuery::new(
                one,
                x,
                &self.committed.multiplicities,
                &self.evaluated.multiplicities_eval,
            ),
        ];
        // Open lookup input commitments at x
        for (h_commit, h_eval) in
            self.committed.helper_polys.iter().zip(self.evaluated.helper_evals.iter())
        {
            queries.push(VerifierQuery::new(one, x, h_commit, h_eval));
        }
        // Open lookup table commitments at x
        queries.push(VerifierQuery::new(
            one,
            x,
            &self.committed.accumulator,
            &self.evaluated.accumulator_eval,
        ));
        // Open lookup product commitment at \omega x
        queries.push(VerifierQuery::new(
            one,
            x_next,
            &self.committed.accumulator,
            &self.evaluated.accumulator_next_eval,
        ));
        queries
    }
}
