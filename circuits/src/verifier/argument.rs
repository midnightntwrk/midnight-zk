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

use midnight_proofs::{
    circuit::Layouter,
    plonk::{ConstraintSystem, Error},
    poly::{PolynomialLabel, Rotation},
    transcript::Hashable,
};

use crate::{
    CircuitField,
    field::AssignedNative,
    verifier::{
        ScalarChip,
        absorbed_vk::AbsorbedVk,
        pcs::{AssignedCommitment, InCircuitPCS, VerifierQuery},
        transcript_gadget::InCircuitTranscript,
    },
};

/// The evaluation of a polynomial at a point, both assigned in-circuit.
#[derive(Clone, Debug)]
pub(crate) struct Evaluation<F: CircuitField> {
    point: AssignedNative<F>,
    eval: AssignedNative<F>,
}

impl<F: CircuitField> Evaluation<F> {
    /// The claimed evaluation.
    pub(crate) fn eval(&self) -> &AssignedNative<F> {
        &self.eval
    }
}

/// Every rotation of `x` at which a polynomial of `cs` is opened: those
/// [eval_points] may use, and those of the instance and fixed queries.
pub(crate) fn rotations<F: CircuitField>(cs: &ConstraintSystem<F>) -> BTreeSet<Rotation> {
    [
        Rotation::cur(),
        Rotation::next(),
        Rotation(-((cs.blinding_factors() + 1) as i32)),
    ]
    .into_iter()
    .chain(cs.advice_queries().iter().map(|&(_, rotation)| rotation))
    .chain(cs.instance_queries().iter().map(|&(_, rotation)| rotation))
    .chain(cs.fixed_queries().iter().map(|&(_, rotation)| rotation))
    .collect()
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
/// proofs/src/plonk/argument.rs.
fn eval_points<F: CircuitField>(
    cs: &ConstraintSystem<F>,
    label: &PolynomialLabel,
    x_rotations: &BTreeMap<Rotation, AssignedNative<F>>,
) -> Vec<AssignedNative<F>> {
    let at = |rotation: Rotation| x_rotations[&rotation].clone();
    match label {
        PolynomialLabel::Fixed(i) => cs
            .fixed_queries()
            .iter()
            .filter(|(column, _)| column.index() == *i)
            .map(|&(_, rotation)| at(rotation))
            .collect(),
        PolynomialLabel::Advice(i) => cs
            .advice_queries()
            .iter()
            .filter(|(column, _)| column.index() == *i)
            .map(|&(_, rotation)| at(rotation))
            .collect(),
        PolynomialLabel::PermutationFixed(_) => vec![at(Rotation::cur())],
        PolynomialLabel::PermutationAccumulator(i) => {
            // Every set but the last is also opened at the last usable row, to
            // chain it to the next one.
            if i + 1 < cs.permutation().num_sets(cs.degree()) {
                vec![
                    at(Rotation::cur()),
                    at(Rotation::next()),
                    at(Rotation(-((cs.blinding_factors() + 1) as i32))),
                ]
            } else {
                vec![at(Rotation::cur()), at(Rotation::next())]
            }
        }
        PolynomialLabel::LogupMultiplicities(_) => vec![at(Rotation::cur())],
        PolynomialLabel::LogupHelper(_, _) => vec![at(Rotation::cur())],
        PolynomialLabel::LogupAggregator(_) => vec![at(Rotation::cur()), at(Rotation::next())],
        PolynomialLabel::Trash(_) => vec![at(Rotation::cur())],
        // The verifier derives h_0(x) from nu(x) rather than reading it; see
        // the `insert` of each `Evaluated`.
        PolynomialLabel::QuotientPiece(0) => vec![],
        PolynomialLabel::QuotientPiece(_) => vec![at(Rotation::cur())],
        _ => unreachable!(),
    }
}

/// A group of polynomials read from the transcript as a single commitment.
#[derive(Clone, Debug)]
pub(crate) struct Committed<F: CircuitField, PCS: InCircuitPCS<F>> {
    commitment: AssignedCommitment<F, PCS>,
    polynomial_labels: Vec<PolynomialLabel>,
}

/// Builds the fixed group of the absorbed verifying key, which binds it to the
/// transcript as reading a commitment from the proof does.
pub(crate) fn committed_from_key<F: CircuitField, PCS: InCircuitPCS<F>>(
    vk: &AbsorbedVk<'_, F, PCS>,
) -> Committed<F, PCS> {
    Committed {
        commitment: vk.phase0_commitment().clone(),
        polynomial_labels: vk.phase0_labels(),
    }
}

/// Reads the commitment to the polynomials of the given labels.
pub(crate) fn read_committed<F, PCS, T>(
    layouter: &mut impl Layouter<F>,
    commitment_chip: &PCS::CommitmentChip,
    labels: &[PolynomialLabel],
    transcript: &mut T,
) -> Result<Committed<F, PCS>, Error>
where
    F: CircuitField,
    PCS: InCircuitPCS<F>,
    PCS::Commitment: Hashable<T::Hash>,
    T: InCircuitTranscript<F>,
{
    Ok(Committed {
        commitment: <PCS as InCircuitPCS<F>>::read_commitment(
            layouter,
            commitment_chip,
            transcript,
            labels,
        )?,
        polynomial_labels: labels.to_vec(),
    })
}

/// A [Committed] group whose polynomials have been opened at their evaluation
/// points.
#[derive(Clone, Debug)]
pub(crate) struct Evaluated<F: CircuitField, PCS: InCircuitPCS<F>> {
    committed: Committed<F, PCS>,
    pub(crate) evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>>,
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> Committed<F, PCS> {
    /// Reads the evaluation of every polynomial of the group at each of its
    /// evaluation points.
    pub(crate) fn evaluate<T>(
        self,
        layouter: &mut impl Layouter<F>,
        scalar_chip: &ScalarChip<F>,
        cs: &ConstraintSystem<F>,
        x_rotations: &BTreeMap<Rotation, AssignedNative<F>>,
        transcript: &mut T,
    ) -> Result<Evaluated<F, PCS>, Error>
    where
        F: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
        let mut evals_map: BTreeMap<PolynomialLabel, Vec<Evaluation<F>>> = BTreeMap::new();

        for label in &self.polynomial_labels {
            let eval_points = eval_points::<F>(cs, label, x_rotations);
            let mut evals = Vec::with_capacity(eval_points.len());
            for point in eval_points {
                evals.push(Evaluation {
                    point,
                    eval: transcript.read(layouter, scalar_chip, &())?,
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

impl<'a, F: CircuitField, PCS: InCircuitPCS<F>> Evaluated<F, PCS> {
    /// Adds the evaluation `eval` at `point` of the group's polynomial `label`,
    /// one derived rather than read from the proof.
    pub(crate) fn insert(
        &mut self,
        label: PolynomialLabel,
        point: AssignedNative<F>,
        eval: AssignedNative<F>,
    ) {
        self.evals_map.insert(label, vec![Evaluation { point, eval }]);
    }

    /// The queries that the multi-open argument checks for this group.
    pub(crate) fn queries(&'a self) -> Vec<VerifierQuery<'a, F, PCS>> {
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
