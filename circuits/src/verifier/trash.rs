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

//! A module for in-circuit trash arguments. It is the in-circuit analog
//! of file proofs/src/plonk/lookup/verifier.rs.
//!
//! The "expressions" part is dealt with in our `expressions/` directory.

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

#[derive(Clone, Debug)]
pub(crate) struct TrashEvaluated<S: SelfEmulation> {
    pub(crate) trash_eval: AssignedNative<S::F>,
}

#[derive(Clone, Debug)]
pub(crate) struct Committed<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    argument_index: usize,
    trash_commitment: PCS::AssignedCommitment,
}

#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    committed: Committed<S, PCS>,
    pub(crate) evaluated: TrashEvaluated<S>,
}

pub(crate) fn read_committed<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    argument_index: usize,
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Committed<S, PCS>, Error> {
    let trash_commitment = PCS::read_commitment(transcript_gadget, layouter, 1)
        .map(|c| c.label(&[PolynomialLabel::Trash(argument_index)]))?;

    Ok(Committed {
        argument_index,
        trash_commitment,
    })
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> Committed<S, PCS> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S, PCS>, Error> {
        let trash_eval = transcript_gadget.read_scalar(layouter)?;

        Ok(Evaluated {
            committed: self,
            evaluated: TrashEvaluated { trash_eval },
        })
    }
}

// "expressions" is implemented in `expressions/trash.rs`

impl<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> Evaluated<S, PCS> {
    pub(crate) fn queries(
        &'a self,
        x: &AssignedNative<S::F>, // evaluation point x
    ) -> Vec<VerifierQuery<'a, S, PCS>> {
        vec![VerifierQuery::new(
            x,
            &self.committed.trash_commitment,
            PolynomialLabel::Trash(self.committed.argument_index),
            &self.evaluated.trash_eval,
        )]
    }
}
