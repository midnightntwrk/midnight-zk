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

//! A module for the in-circuit permutation argument. It is the in-circuit
//! analog of file src/plonk/permutation/verifier.rs from halo2.
//!
//! The "expressions" part is dealt with in our `expressions/` directory.

use midnight_proofs::{
    circuit::Layouter,
    plonk::{ConstraintSystem, Error},
};

use crate::verifier::{
    kzg::VerifierQuery,
    transcript_gadget::TranscriptGadget,
    types::{AssignedPoint, AssignedScalar, SelfEmulationCurve},
    utils::AssignedBoundedScalar,
};

#[derive(Clone, Debug)]
pub(crate) struct Committed<C: SelfEmulationCurve> {
    permutation_product_commitments: Vec<AssignedPoint<C>>,
}

#[derive(Clone, Debug)]
pub(crate) struct EvaluatedSet<C: SelfEmulationCurve> {
    permutation_product_commitment: AssignedPoint<C>,
    pub(crate) permutation_product_eval: AssignedScalar<C>,
    pub(crate) permutation_product_next_eval: AssignedScalar<C>,
    pub(crate) permutation_product_last_eval: Option<AssignedScalar<C>>,
}

#[derive(Clone, Debug)]
pub(crate) struct CommonEvaluated<C: SelfEmulationCurve> {
    pub(crate) permutation_evals: Vec<AssignedScalar<C>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Evaluated<C: SelfEmulationCurve> {
    pub(crate) sets: Vec<EvaluatedSet<C>>,
}

pub(crate) fn read_product_commitments<C: SelfEmulationCurve>(
    layouter: &mut impl Layouter<C::ScalarExt>,
    transcript_gadget: &mut TranscriptGadget<C>,
    cs: &ConstraintSystem<C::ScalarExt>,
) -> Result<Committed<C>, Error> {
    let chunk_len = cs.degree() - 2;

    let permutation_product_commitments = cs
        .permutation()
        .get_columns()
        .chunks(chunk_len)
        .map(|_| transcript_gadget.read_point(layouter))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(Committed {
        permutation_product_commitments,
    })
}

/// This is the in-circuit analog of `evaluate` implemented for `VerifyingKey`
/// in halo2 src/plonk/permutation/verifier.rs.
///
/// Instead of evaluating it for the `VerifyingKey`, we directly require the
/// `nb_perm_commitments` as an argument.
pub(crate) fn evaluate_permutation_common<C: SelfEmulationCurve>(
    layouter: &mut impl Layouter<C::ScalarExt>,
    transcript_gadget: &mut TranscriptGadget<C>,
    nb_perm_commitments: usize,
) -> Result<CommonEvaluated<C>, Error> {
    let permutation_evals = (0..nb_perm_commitments)
        .map(|_| transcript_gadget.read_scalar(layouter))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(CommonEvaluated { permutation_evals })
}

impl<C: SelfEmulationCurve> Committed<C> {
    pub(crate) fn evaluate(
        self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        transcript_gadget: &mut TranscriptGadget<C>,
    ) -> Result<Evaluated<C>, Error> {
        let mut sets = vec![];

        let mut iter = self.permutation_product_commitments.into_iter();

        while let Some(permutation_product_commitment) = iter.next() {
            let permutation_product_eval = transcript_gadget.read_scalar(layouter)?;
            let permutation_product_next_eval = transcript_gadget.read_scalar(layouter)?;
            let permutation_product_last_eval = if iter.len() > 0 {
                Some(transcript_gadget.read_scalar(layouter)?)
            } else {
                None
            };

            sets.push(EvaluatedSet {
                permutation_product_commitment,
                permutation_product_eval,
                permutation_product_next_eval,
                permutation_product_last_eval,
            });
        }

        Ok(Evaluated { sets })
    }
}

// "expressions" is implemented in `expressions/permutation.rs`

impl<C: SelfEmulationCurve> Evaluated<C> {
    pub(crate) fn queries(
        &self,
        one: &AssignedBoundedScalar<C>, // 1
        x: &AssignedScalar<C>,          // evaluation point x
        x_next: &AssignedScalar<C>,     // x * \omega
        x_last: &AssignedScalar<C>,     // x * \omega^(-blinding_factors + 1)
    ) -> Vec<VerifierQuery<C>> {
        let mut queries = vec![];
        for set in self.sets.iter() {
            // Open permutation product commitments at x and \omega^{-1} x
            // Open permutation product commitments at x and \omega x
            queries.push(VerifierQuery::new(
                one,
                x,
                &set.permutation_product_commitment,
                &set.permutation_product_eval,
            ));
            queries.push(VerifierQuery::new(
                one,
                x_next,
                &set.permutation_product_commitment,
                &set.permutation_product_next_eval,
            ));
        }

        // Open it at \omega^{last} x for all but the last set
        for set in self.sets.iter().rev().skip(1) {
            queries.push(VerifierQuery::new(
                one,
                x_last,
                &set.permutation_product_commitment,
                &set.clone().permutation_product_last_eval.unwrap(),
            ));
        }

        queries
    }
}

impl<C: SelfEmulationCurve> CommonEvaluated<C> {
    /// This function differs from the halo2 one because we deal with fixed
    /// commitments off-circuit. Thus, we do not require the actual permutation
    /// common commitments, but their names.
    pub(crate) fn queries(
        &self,
        commitment_names: &[String],
        one: &AssignedBoundedScalar<C>, // 1
        x: &AssignedScalar<C>,          // evaluation point x
    ) -> Vec<VerifierQuery<C>> {
        assert_eq!(commitment_names.len(), self.permutation_evals.len());

        commitment_names
            .iter()
            .zip(self.permutation_evals.iter())
            .map(|(com_name, eval)| VerifierQuery::new_fixed(one, x, com_name, eval))
            .collect()
    }
}
