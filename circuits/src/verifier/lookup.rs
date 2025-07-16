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

//! A module for in-circuit lookup arguments. It is the in-circuit analog
//! of file src/plonk/lookup/verifier.rs from halo2.
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
pub(crate) struct PermutationCommitments<S: SelfEmulation> {
    permuted_input_commitment: S::AssignedPoint,
    permuted_table_commitment: S::AssignedPoint,
}

#[derive(Clone, Debug)]
pub(crate) struct Committed<S: SelfEmulation> {
    permuted: PermutationCommitments<S>,
    product_commitment: S::AssignedPoint,
}

#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation> {
    committed: Committed<S>,
    pub(crate) product_eval: AssignedNative<S::F>,
    pub(crate) product_next_eval: AssignedNative<S::F>,
    pub(crate) permuted_input_eval: AssignedNative<S::F>,
    pub(crate) permuted_input_inv_eval: AssignedNative<S::F>,
    pub(crate) permuted_table_eval: AssignedNative<S::F>,
}

pub(crate) fn read_permuted_commitments<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<PermutationCommitments<S>, Error> {
    let permuted_input_commitment = transcript_gadget.read_point(layouter)?;
    let permuted_table_commitment = transcript_gadget.read_point(layouter)?;

    Ok(PermutationCommitments {
        permuted_input_commitment,
        permuted_table_commitment,
    })
}

impl<S: SelfEmulation> PermutationCommitments<S> {
    pub(crate) fn read_product_commitment(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Committed<S>, Error> {
        let product_commitment = transcript_gadget.read_point(layouter)?;

        Ok(Committed {
            permuted: self,
            product_commitment,
        })
    }
}

impl<S: SelfEmulation> Committed<S> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S>, Error> {
        let product_eval = transcript_gadget.read_scalar(layouter)?;
        let product_next_eval = transcript_gadget.read_scalar(layouter)?;
        let permuted_input_eval = transcript_gadget.read_scalar(layouter)?;
        let permuted_input_inv_eval = transcript_gadget.read_scalar(layouter)?;
        let permuted_table_eval = transcript_gadget.read_scalar(layouter)?;

        Ok(Evaluated {
            committed: self,
            product_eval,
            product_next_eval,
            permuted_input_eval,
            permuted_input_inv_eval,
            permuted_table_eval,
        })
    }
}

// "expressions" is implemented in `expressions/lookup.rs`

impl<S: SelfEmulation> Evaluated<S> {
    pub(crate) fn queries(
        &self,
        one: &AssignedBoundedScalar<S::F>, // 1
        x: &AssignedNative<S::F>,          // evaluation point x
        x_next: &AssignedNative<S::F>,     // x * \omega
        x_prev: &AssignedNative<S::F>,     // x * \omega^(-1)
    ) -> Vec<VerifierQuery<S>> {
        vec![
            VerifierQuery::new(
                one,
                x,
                &self.committed.product_commitment,
                &self.product_eval,
            ),
            VerifierQuery::new(
                one,
                x,
                &self.committed.permuted.permuted_input_commitment,
                &self.permuted_input_eval,
            ),
            VerifierQuery::new(
                one,
                x,
                &self.committed.permuted.permuted_table_commitment,
                &self.permuted_table_eval,
            ),
            VerifierQuery::new(
                one,
                x_prev,
                &self.committed.permuted.permuted_input_commitment,
                &self.permuted_input_inv_eval,
            ),
            VerifierQuery::new(
                one,
                x_next,
                &self.committed.product_commitment,
                &self.product_next_eval,
            ),
        ]
    }
}
