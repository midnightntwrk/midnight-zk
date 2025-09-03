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

//! A module for in-circuit trash arguments. It is the in-circuit analog
//! of file proofs/src/plonk/lookup/verifier.rs.
//!
//! The "expressions" part is dealt with in our `expressions/` directory.

use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    field::AssignedNative,
    verifier::{
        kzg::VerifierQuery, transcript_gadget::TranscriptGadget, utils::AssignedBoundedScalar,
        SelfEmulation,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct Committed<S: SelfEmulation> {
    trash_commitment: S::AssignedPoint,
}

#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation> {
    committed: Committed<S>,
    pub(crate) trash_eval: AssignedNative<S::F>,
}

pub(crate) fn read_committed<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Committed<S>, Error> {
    let trash_commitment = transcript_gadget.read_point(layouter)?;

    Ok(Committed { trash_commitment })
}

impl<S: SelfEmulation> Committed<S> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S>, Error> {
        let trash_eval = transcript_gadget.read_scalar(layouter)?;

        Ok(Evaluated {
            committed: self,
            trash_eval,
        })
    }
}

// "expressions" is implemented in `expressions/trash.rs`

impl<S: SelfEmulation> Evaluated<S> {
    pub(crate) fn queries(
        &self,
        one: &AssignedBoundedScalar<S::F>, // 1
        x: &AssignedNative<S::F>,          // evaluation point x
    ) -> Vec<VerifierQuery<S>> {
        vec![VerifierQuery::new(
            one,
            x,
            &self.committed.trash_commitment,
            &self.trash_eval,
        )]
    }
}
