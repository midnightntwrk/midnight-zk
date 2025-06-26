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

use crate::verifier::{
    kzg::VerifierQuery,
    transcript_gadget::TranscriptGadget,
    types::{AssignedPoint, AssignedScalar, SelfEmulationCurve},
    utils::AssignedBoundedScalar,
};

#[derive(Clone, Debug)]
pub(crate) struct PermutationCommitments<C: SelfEmulationCurve> {
    permuted_input_commitment: AssignedPoint<C>,
    permuted_table_commitment: AssignedPoint<C>,
}

#[derive(Clone, Debug)]
pub(crate) struct Committed<C: SelfEmulationCurve> {
    permuted: PermutationCommitments<C>,
    product_commitment: AssignedPoint<C>,
}

#[derive(Clone, Debug)]
pub(crate) struct Evaluated<C: SelfEmulationCurve> {
    committed: Committed<C>,
    pub(crate) product_eval: AssignedScalar<C>,
    pub(crate) product_next_eval: AssignedScalar<C>,
    pub(crate) permuted_input_eval: AssignedScalar<C>,
    pub(crate) permuted_input_inv_eval: AssignedScalar<C>,
    pub(crate) permuted_table_eval: AssignedScalar<C>,
}

pub(crate) fn read_permuted_commitments<C: SelfEmulationCurve>(
    layouter: &mut impl Layouter<C::ScalarExt>,
    transcript_gadget: &mut TranscriptGadget<C>,
) -> Result<PermutationCommitments<C>, Error> {
    let permuted_input_commitment = transcript_gadget.read_point(layouter)?;
    let permuted_table_commitment = transcript_gadget.read_point(layouter)?;

    Ok(PermutationCommitments {
        permuted_input_commitment,
        permuted_table_commitment,
    })
}

impl<C: SelfEmulationCurve> PermutationCommitments<C> {
    pub(crate) fn read_product_commitment(
        self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        transcript_gadget: &mut TranscriptGadget<C>,
    ) -> Result<Committed<C>, Error> {
        let product_commitment = transcript_gadget.read_point(layouter)?;

        Ok(Committed {
            permuted: self,
            product_commitment,
        })
    }
}

impl<C: SelfEmulationCurve> Committed<C> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        transcript_gadget: &mut TranscriptGadget<C>,
    ) -> Result<Evaluated<C>, Error> {
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

impl<C: SelfEmulationCurve> Evaluated<C> {
    pub(crate) fn queries(
        &self,
        one: &AssignedBoundedScalar<C>, // 1
        x: &AssignedScalar<C>,          // evaluation point x
        x_next: &AssignedScalar<C>,     // x * \omega
        x_prev: &AssignedScalar<C>,     // x * \omega^(-1)
    ) -> Vec<VerifierQuery<C>> {
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
