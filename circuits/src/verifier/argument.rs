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

//! A module for in-circuit generic arguments. It is the in-circuit analog of
//! file proofs/src/plonk/argument.rs and its `verifier` submodule.
//!
//! A group of polynomials committed together, identified by their labels, is
//! read from the transcript as a single commitment and opened at the points
//! that [eval_points] assigns to each label. The arguments that own those
//! polynomials recover their evaluations from [Evaluated::evals_map], keyed by
//! label; the corresponding identities live in our `expressions/` directory.

use std::collections::{BTreeMap, BTreeSet};

use midnight_proofs::{circuit::Layouter, plonk::Error, poly::PolynomialLabel};

use crate::{
    field::AssignedNative,
    verifier::{
        SelfEmulation,
        pcs::{InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
    },
};

/// The evaluation of a polynomial at a point, both assigned in-circuit.
#[derive(Clone, Debug)]
pub(crate) struct Evaluation<S: SelfEmulation> {
    point: AssignedNative<S::F>,
    eval: AssignedNative<S::F>,
}

impl<S: SelfEmulation> Evaluation<S> {
    /// The claimed evaluation.
    pub(crate) fn eval(&self) -> &AssignedNative<S::F> {
        &self.eval
    }
}

/// The evaluation points at which the polynomial of the given label needs to be
/// evaluated.
///
/// The opening points are argument-specific, but they are all listed here so
/// that a single implementation serves the whole group, with no trait to
/// dispatch on: `PolynomialLabel` is defined outside the arguments and already
/// names their specifics, so the label alone decides.
///
/// It must agree with its off-circuit counterpart in
/// proofs/src/plonk/argument.rs, which takes `omega` and forms `omega * x`
/// itself. Here `x_next` is passed in already assigned, so that the rotation
/// costs one multiplication for the whole group rather than one per label.
fn eval_points<S: SelfEmulation>(
    label: &PolynomialLabel,
    x: &AssignedNative<S::F>,
    x_next: &AssignedNative<S::F>,
) -> Vec<AssignedNative<S::F>> {
    match label {
        PolynomialLabel::LogupMultiplicities(_) => vec![x.clone()],
        PolynomialLabel::LogupHelper(_, _) => vec![x.clone()],
        PolynomialLabel::LogupAggregator(_) => vec![x.clone(), x_next.clone()],
        PolynomialLabel::Trash(_) => vec![x.clone()],
        _ => unreachable!(),
    }
}

/// A group of polynomials read from the transcript as a single commitment.
#[derive(Clone, Debug)]
pub(crate) struct Committed<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    commitment: PCS::AssignedCommitment,
    polynomial_labels: BTreeSet<PolynomialLabel>,
}

/// Reads the commitment to the polynomials of the given labels, or `None` if
/// there are none: the prover commits to nothing in that case, so there is
/// nothing in the transcript to read.
///
/// TODO: drop this function, and the `Option` it forces on the phase groups of
/// [crate::verifier::traces::VerifierTrace], once every phase group is
/// guaranteed to hold at least one polynomial. [read_committed] then becomes
/// the only entry point.
pub(crate) fn read_committed_group<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    labels: &[PolynomialLabel],
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Option<Committed<S, PCS>>, Error> {
    if labels.is_empty() {
        return Ok(None);
    }
    read_committed(labels, layouter, transcript_gadget).map(Some)
}

/// Reads the commitment to the polynomials of the given labels.
pub(crate) fn read_committed<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    labels: &[PolynomialLabel],
    layouter: &mut impl Layouter<S::F>,
    transcript_gadget: &mut TranscriptGadget<S>,
) -> Result<Committed<S, PCS>, Error> {
    Ok(Committed {
        commitment: PCS::read_commitment(transcript_gadget, layouter, labels)?,
        polynomial_labels: BTreeSet::from_iter(labels.iter().cloned()),
    })
}

/// A [Committed] group whose polynomials have been opened at their evaluation
/// points.
#[derive(Clone, Debug)]
pub(crate) struct Evaluated<S: SelfEmulation, PCS: InCircuitPCS<S>> {
    committed: Committed<S, PCS>,
    pub(crate) evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<S>>>,
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> Committed<S, PCS> {
    /// Reads the evaluation of every polynomial of the group at each of its
    /// evaluation points.
    pub(crate) fn evaluate(
        self,
        x: &AssignedNative<S::F>,
        x_next: &AssignedNative<S::F>,
        layouter: &mut impl Layouter<S::F>,
        transcript_gadget: &mut TranscriptGadget<S>,
    ) -> Result<Evaluated<S, PCS>, Error> {
        let mut evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<S>>> = BTreeMap::new();

        for label in &self.polynomial_labels {
            let eval_points = eval_points::<S>(label, x, x_next);
            let mut evals = Vec::with_capacity(eval_points.len());
            for point in eval_points {
                evals.push(Evaluation {
                    point,
                    eval: transcript_gadget.read_scalar(layouter)?,
                });
            }

            if evals_map.insert(label.clone(), evals).is_some() {
                return Err(Error::DuplicatedLabel);
            }
        }

        Ok(Evaluated {
            committed: self,
            evals_map,
        })
    }
}

// "expressions" are implemented in our `expressions/` directory.

impl<'a, S: SelfEmulation, PCS: InCircuitPCS<S>> Evaluated<S, PCS> {
    /// The queries that the multi-open argument checks for this group.
    pub(crate) fn queries(&'a self) -> Vec<VerifierQuery<'a, S, PCS>> {
        self.evals_map
            .iter()
            .flat_map(|(label, evaluations)| {
                evaluations.iter().map(|evaluation| {
                    VerifierQuery::new(
                        &evaluation.point,
                        &self.committed.commitment,
                        label.clone(),
                        &evaluation.eval,
                    )
                })
            })
            .collect()
    }
}
