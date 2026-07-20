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

use midnight_proofs::{
    circuit::Layouter,
    plonk::Error,
    poly::{commitment::Labelable, PolynomialLabel},
};

use crate::{
    field::AssignedNative,
    verifier::{
        pcs::{InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
        SelfEmulation,
    },
};

/// Commitment to the multiplicity columns, read from the transcript.
#[derive(Clone, Debug)]
pub(crate) struct CommittedMultiplicities<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    multiplicities: PCS::AssignedCommitment,
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
pub(crate) struct Committed<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    argument_index: usize,
    multiplicities: PCS::AssignedCommitment,
    helper_polys: Vec<PCS::AssignedCommitment>,
    accumulator: PCS::AssignedCommitment,
}

/// Commitments plus evaluations at challenge point.
#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    committed: Committed<S, PCS>,
    pub(crate) evaluated: LookupEvaluated<S>,
}

/// Reads the batched multiplicities commitment for all logup arguments in one
/// transcript entry and hands each argument a clone of the shared commitment
/// (which carries one `LogupMultiplicities(arg)` label per arg; per-arg queries
/// route to the right sub-bundle via the label). Mirrors the off-circuit
/// `logup::verifier::read_multiplicities`.
pub(crate) fn read_multiplicities<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    num_args: usize,
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Vec<CommittedMultiplicities<S, PCS>>, Error> {
    if num_args == 0 {
        return Ok(Vec::new());
    }
    let labels: Vec<_> = (0..num_args).map(PolynomialLabel::LogupMultiplicities).collect();
    let shared = PCS::read_commitment(transcript_gadget, layouter, num_args)?.label(&labels);
    Ok((0..num_args)
        .map(|_| CommittedMultiplicities {
            multiplicities: shared.clone(),
        })
        .collect())
}

/// Partial state between the batched helper read and the batched aggregator
/// read.
#[derive(Clone, Debug)]
pub(crate) struct HelpersOnly<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    argument_index: usize,
    multiplicities: PCS::AssignedCommitment,
    helper_polys: Vec<PCS::AssignedCommitment>,
}

/// Reads the **batched** helper commitments for all logup arguments in one
/// transcript entry (one point per (arg, chunk)). Each arg receives a clone of
/// the shared commitment for each of its chunks; the unique
/// `LogupHelper(arg, chunk_idx)` label routes each query. Mirrors the
/// off-circuit `logup::verifier::read_helpers`.
pub(crate) fn read_helpers<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    args_with_multiplicities: Vec<(usize, usize, CommittedMultiplicities<S, PCS>)>,
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Vec<HelpersOnly<S, PCS>>, Error> {
    let total: usize = args_with_multiplicities.iter().map(|(_, n, _)| *n).sum();
    if total == 0 {
        // No helpers anywhere — prover skipped the write.
        return Ok(args_with_multiplicities
            .into_iter()
            .map(|(argument_index, _, m)| HelpersOnly {
                argument_index,
                multiplicities: m.multiplicities,
                helper_polys: Vec::new(),
            })
            .collect());
    }
    // Build the full label set in (arg, chunk) order, matching the prover's
    // flat iteration, then read the single batched helper commitment.
    let mut labels: Vec<PolynomialLabel> = Vec::new();
    for (arg, nb_chunks, _) in &args_with_multiplicities {
        for chunk_idx in 0..*nb_chunks {
            labels.push(PolynomialLabel::LogupHelper(*arg, chunk_idx));
        }
    }
    let shared = PCS::read_commitment(transcript_gadget, layouter, total)?.label(&labels);
    // Hand each arg its own clone of the shared commitment, one per chunk;
    // `LogupHelper(arg, chunk)` routes each query to the right sub-bundle.
    Ok(args_with_multiplicities
        .into_iter()
        .map(|(argument_index, nb_chunks, m)| HelpersOnly {
            argument_index,
            multiplicities: m.multiplicities,
            helper_polys: vec![shared.clone(); nb_chunks],
        })
        .collect())
}

/// Reads the **batched** aggregator commitment for all logup arguments
/// and assembles one [`Committed`] per arg. Mirrors the off-circuit
/// `logup::verifier::read_aggregators`.
pub(crate) fn read_aggregators<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    helpers: Vec<HelpersOnly<S, PCS>>,
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Vec<Committed<S, PCS>>, Error> {
    if helpers.is_empty() {
        return Ok(Vec::new());
    }
    let labels: Vec<_> = helpers
        .iter()
        .map(|h| PolynomialLabel::LogupAggregator(h.argument_index))
        .collect();
    let shared_agg =
        PCS::read_commitment(transcript_gadget, layouter, helpers.len())?.label(&labels);
    Ok(helpers
        .into_iter()
        .map(|h| Committed {
            argument_index: h.argument_index,
            multiplicities: h.multiplicities,
            helper_polys: h.helper_polys,
            accumulator: shared_agg.clone(),
        })
        .collect())
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> Committed<S, PCS> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S, PCS>, Error> {
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

impl<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> Evaluated<S, PCS> {
    pub(crate) fn queries(
        &'a self,
        x: &AssignedNative<S::F>,      // evaluation point x
        x_next: &AssignedNative<S::F>, // ωx
    ) -> Vec<VerifierQuery<'a, S, PCS>> {
        let arg = self.committed.argument_index;
        let mut queries = vec![
            // Open lookup product commitment at x
            VerifierQuery::new(
                x,
                &self.committed.multiplicities,
                PolynomialLabel::LogupMultiplicities(arg),
                &self.evaluated.multiplicities_eval,
            ),
        ];
        // Open lookup input commitments at x
        for (j, (h_commit, h_eval)) in self
            .committed
            .helper_polys
            .iter()
            .zip(self.evaluated.helper_evals.iter())
            .enumerate()
        {
            queries.push(VerifierQuery::new(
                x,
                h_commit,
                PolynomialLabel::LogupHelper(arg, j),
                h_eval,
            ));
        }
        // Open lookup table commitments at x
        queries.push(VerifierQuery::new(
            x,
            &self.committed.accumulator,
            PolynomialLabel::LogupAggregator(arg),
            &self.evaluated.accumulator_eval,
        ));
        // Open lookup product commitment at \omega x
        queries.push(VerifierQuery::new(
            x_next,
            &self.committed.accumulator,
            PolynomialLabel::LogupAggregator(arg),
            &self.evaluated.accumulator_next_eval,
        ));
        queries
    }
}
