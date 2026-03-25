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

use midnight_proofs::{circuit::Layouter, plonk::Error, poly::CommitmentLabel};

use crate::{
    field::AssignedNative,
    verifier::{
        kzg::VerifierQuery, transcript_gadget::TranscriptGadget, utils::AssignedBoundedScalar,
        SelfEmulation,
    },
};

/// Commitment to the multiplicity columns, read from the transcript.
#[derive(Clone, Debug)]
pub(crate) struct CommittedMultiplicities<S: SelfEmulation> {
    multiplicities: S::AssignedPoint,
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
    multiplicities: S::AssignedPoint,
    helper_polys: Vec<S::AssignedPoint>,
    accumulator: S::AssignedPoint,
}

/// Commitments plus evaluations at challenge point.
#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation> {
    committed: Committed<S>,
    pub(crate) evaluated: LookupEvaluated<S>,
}

/// Reads the prover's commitments from the transcript.
pub(crate) fn read_multiplicities<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<CommittedMultiplicities<S>, Error> {
    let multiplicities = transcript_gadget.read_point(layouter)?;

    Ok(CommittedMultiplicities { multiplicities })
}

impl<S: SelfEmulation> CommittedMultiplicities<S> {
    pub(crate) fn read_commitment(
        self,
        num_flattened: usize,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Committed<S>, Error> {
        let helper_polys = (0..num_flattened)
            .map(|_| transcript_gadget.read_point(layouter))
            .collect::<Result<Vec<_>, Error>>()?;
        let accumulator = transcript_gadget.read_point(layouter)?;

        Ok(Committed {
            multiplicities: self.multiplicities,
            helper_polys,
            accumulator,
        })
    }
}

impl<S: SelfEmulation> Committed<S> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S>, Error> {
        let num_flattened = self.helper_polys.len();
        let multiplicities_eval = transcript_gadget.read_scalar(layouter)?;
        let helper_evals = (0..num_flattened)
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
                CommitmentLabel::NoLabel,
                &self.committed.multiplicities,
                &self.evaluated.multiplicities_eval,
            ),
        ];
        // Open lookup input commitments at x
        for (h_commit, h_eval) in
            self.committed.helper_polys.iter().zip(self.evaluated.helper_evals.iter())
        {
            queries.push(VerifierQuery::new(
                one,
                x,
                CommitmentLabel::NoLabel,
                h_commit,
                h_eval,
            ));
        }
        // Open lookup table commitments at x
        queries.push(VerifierQuery::new(
            one,
            x,
            CommitmentLabel::NoLabel,
            &self.committed.accumulator,
            &self.evaluated.accumulator_eval,
        ));
        // Open lookup product commitment at \omega x
        queries.push(VerifierQuery::new(
            one,
            x_next,
            CommitmentLabel::NoLabel,
            &self.committed.accumulator,
            &self.evaluated.accumulator_next_eval,
        ));
        queries
    }
}
