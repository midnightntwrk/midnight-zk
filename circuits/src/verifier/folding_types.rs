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

//! Assigned data of the in-circuit folding verifier: the in-circuit analogs of
//! `midnight_proofs::plonk::protogalaxy`'s [`Challenges`], `FoldingInstance`
//! and [`Accumulator`], their shape, their transcript encoding and their
//! public-input encoding.

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        ConstraintSystem, Error,
        protogalaxy::{Accumulator, Challenges, folding_degree},
    },
    poly::PolynomialLabel,
};

use crate::{
    field::AssignedNative,
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::Instantiable,
    verifier::{
        AssignedKZGCommitment, AssignedKZGMultiCommitment, AssignedPoint, CommitmentBases,
        InCircuitPCS, SelfEmulation,
        argument::{phase1_labels, phase2_labels},
        transcript_gadget::TranscriptGadget,
    },
};

/// The off-circuit accumulator that [`AssignedFoldingAccumulator`] assigns.
pub type NativeAccumulator<S> = Accumulator<
    <S as SelfEmulation>::F,
    <<S as SelfEmulation>::PCS as InCircuitPCS<S>>::OffCircuitPCS,
>;

/// Everything the folding verifier circuit needs to know about the folded
/// relation, fixed at circuit-configuration time.
#[derive(Clone, Debug)]
pub struct FoldingShape {
    /// `log n`, the length of `β⃗`.
    pub(crate) log_n: usize,
    /// Labels of the curve points of the phase-1 commitment (one per chunk).
    pub(crate) phase1_labels: Vec<PolynomialLabel>,
    /// Labels of the curve points of the phase-2 commitment (one per chunk).
    pub(crate) phase2_labels: Vec<PolynomialLabel>,
    /// Number of public inputs per instance column.
    pub(crate) instance_lens: Vec<usize>,
    pub(crate) nb_theta: usize,
    pub(crate) nb_trash: usize,
    pub(crate) nb_y: usize,
    /// `d`, the [`folding_degree`] of the relation.
    pub(crate) degree: usize,
}

impl FoldingShape {
    /// The shape of the folding of instances of the (finalized) constraint
    /// system `cs` over a domain of `2^log_n` rows, with `instance_lens`
    /// public inputs per instance column.
    ///
    /// # Panics
    ///
    /// If `instance_lens` does not have one entry per instance column of `cs`.
    pub fn new<S: SelfEmulation>(
        cs: &ConstraintSystem<S::F>,
        log_n: u32,
        instance_lens: &[usize],
    ) -> Self {
        assert_eq!(cs.num_instance_columns(), instance_lens.len());
        Self {
            log_n: log_n as usize,
            phase1_labels: S::PCS::fixed_base_labels(&phase1_labels(cs)),
            phase2_labels: S::PCS::fixed_base_labels(&phase2_labels(cs)),
            instance_lens: instance_lens.to_vec(),
            nb_theta: cs.nb_theta_challenges(),
            nb_trash: cs.nb_trash_challenges(),
            nb_y: cs.nb_y_challenges(),
            degree: folding_degree(cs),
        }
    }

    /// The number of folded curve points (the chunks of both commitments).
    pub fn nb_points(&self) -> usize {
        self.phase1_labels.len() + self.phase2_labels.len()
    }

    /// The number of curve points of the phase-1 and phase-2 commitments.
    pub fn nb_phase_points(&self) -> [usize; 2] {
        [self.phase1_labels.len(), self.phase2_labels.len()]
    }

    /// The number of challenges: `θ⃗, β, γ, trash⃗, y⃗`.
    fn nb_challenges(&self) -> usize {
        self.nb_theta + 2 + self.nb_trash + self.nb_y
    }
}

/// In-circuit [`Challenges`]: `θ⃗, β, γ, trash⃗, y⃗`.
#[derive(Clone, Debug)]
pub struct AssignedChallenges<S: SelfEmulation> {
    pub(crate) theta: Vec<AssignedNative<S::F>>,
    pub(crate) beta: AssignedNative<S::F>,
    pub(crate) gamma: AssignedNative<S::F>,
    pub(crate) trash: Vec<AssignedNative<S::F>>,
    pub(crate) y: Vec<AssignedNative<S::F>>,
}

impl<S: SelfEmulation> AssignedChallenges<S> {
    /// The challenges in absorption order: `θ⃗, β, γ, trash⃗, y⃗`.
    pub(crate) fn scalars(&self) -> impl Iterator<Item = &AssignedNative<S::F>> {
        (self.theta.iter())
            .chain([&self.beta, &self.gamma])
            .chain(&self.trash)
            .chain(&self.y)
    }

    /// Rebuilds the challenges from scalars in [`Self::scalars`] order.
    ///
    /// # Panics
    ///
    /// If there are fewer scalars than `shape` needs.
    fn from_scalars(
        shape: &FoldingShape,
        mut scalars: impl Iterator<Item = AssignedNative<S::F>>,
    ) -> Self {
        let mut next = || scalars.next().expect("enough challenges");
        let theta = (0..shape.nb_theta).map(|_| next()).collect();
        let (beta, gamma) = (next(), next());
        let trash = (0..shape.nb_trash).map(|_| next()).collect();
        let y = (0..shape.nb_y).map(|_| next()).collect();
        Self {
            theta,
            beta,
            gamma,
            trash,
            y,
        }
    }
}

/// In-circuit `FoldingInstance`: the phase-1 and phase-2 commitments (one
/// labelled curve point per chunk), the public inputs and the challenges.
#[derive(Clone, Debug)]
pub struct AssignedFoldingInstance<S: SelfEmulation> {
    pub(crate) phase1_commitment: AssignedKZGMultiCommitment<S>,
    pub(crate) phase2_commitment: AssignedKZGMultiCommitment<S>,
    pub(crate) instances: Vec<Vec<AssignedNative<S::F>>>,
    pub(crate) challenges: AssignedChallenges<S>,
}

/// In-circuit [`Accumulator`]: a folded instance, `β⃗` and `e`.
#[derive(Clone, Debug)]
pub struct AssignedFoldingAccumulator<S: SelfEmulation> {
    pub(crate) instance: AssignedFoldingInstance<S>,
    pub(crate) betas: Vec<AssignedNative<S::F>>,
    pub(crate) error: AssignedNative<S::F>,
}

/// The curve points (and their labels) of a commitment read from a transcript
/// or assigned by [`assign_commitment`], in order.
pub(crate) fn points<S: SelfEmulation>(
    commitment: &AssignedKZGMultiCommitment<S>,
) -> Result<Vec<(&S::AssignedPoint, &PolynomialLabel)>, Error> {
    (commitment.0.iter())
        .map(|inner| match inner {
            AssignedKZGCommitment::Simple(AssignedPoint::Variable(p), label) => Ok((p, label)),
            _ => Err(Error::Synthesis(
                "folding needs commitments made of assigned points".into(),
            )),
        })
        .collect()
}

/// Assigns a commitment made of one point per label, as
/// `TranscriptGadget::read_commitment` does (no subgroup check).
///
/// # Panics
///
/// If the (known) value does not have one point per label.
fn assign_commitment<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    curve_chip: &S::CurveChip,
    labels: &[PolynomialLabel],
    values: Value<Vec<S::C>>,
) -> Result<AssignedKZGMultiCommitment<S>, Error> {
    let values = values.map(|v| {
        assert_eq!(
            v.len(),
            labels.len(),
            "commitment with an unexpected number of points"
        );
        v
    });
    let inners = (labels.iter().enumerate())
        .map(|(i, label)| {
            let value = values.as_ref().map(|v| v[i]);
            let point = S::assign_without_subgroup_check(layouter, curve_chip, value)?;
            Ok(AssignedKZGCommitment::simple(point, label.clone()))
        })
        .collect::<Result<_, Error>>()?;
    Ok(AssignedKZGMultiCommitment(inners))
}

/// Assigns `len` scalars (witnesses).
///
/// # Panics
///
/// If the (known) value does not have `len` scalars.
fn assign_scalars<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    len: usize,
    values: Value<Vec<S::F>>,
) -> Result<Vec<AssignedNative<S::F>>, Error> {
    let values = values.map(|v| {
        assert_eq!(v.len(), len, "unexpected number of scalars");
        v
    });
    (0..len)
        .map(|i| scalar_chip.assign(layouter, values.as_ref().map(|v| v[i])))
        .collect()
}

/// The curve points of a native commitment, in order.
fn native_points<C>(commitment: &impl CommitmentBases<C>) -> Vec<C> {
    commitment.bases().into_iter().map(|(_, p)| p).collect()
}

/// The native challenges in the order of [`AssignedChallenges::scalars`].
fn native_challenges<F: Copy>(c: &Challenges<F>) -> Vec<F> {
    (c.theta.iter())
        .chain([&c.beta, &c.gamma])
        .chain(&c.trash)
        .chain(&c.y)
        .copied()
        .collect()
}

impl<S: SelfEmulation> AssignedFoldingAccumulator<S> {
    /// Assigns an off-circuit accumulator of the given shape as a witness, its
    /// points without subgroup check. The caller binds it (e.g. to a hash in
    /// the public input).
    ///
    /// # Panics
    ///
    /// If the (known) accumulator does not have the given shape.
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        shape: &FoldingShape,
        acc: Value<&NativeAccumulator<S>>,
    ) -> Result<Self, Error> {
        let instance = acc.map(|acc| acc.instance());
        let phase1_commitment = assign_commitment(
            layouter,
            curve_chip,
            &shape.phase1_labels,
            instance.map(|i| native_points(i.phase1_commitment())),
        )?;
        let phase2_commitment = assign_commitment(
            layouter,
            curve_chip,
            &shape.phase2_labels,
            instance.map(|i| native_points(i.phase2_commitment())),
        )?;
        let instances = (shape.instance_lens.iter().enumerate())
            .map(|(j, len)| {
                let values = instance.map(|i| i.instances()[j].clone());
                assign_scalars::<S>(layouter, scalar_chip, *len, values)
            })
            .collect::<Result<_, Error>>()?;
        let challenges = assign_scalars::<S>(
            layouter,
            scalar_chip,
            shape.nb_challenges(),
            instance.map(|i| native_challenges(i.challenges())),
        )?;
        let betas = assign_scalars::<S>(
            layouter,
            scalar_chip,
            shape.log_n,
            acc.map(|acc| acc.betas().to_vec()),
        )?;
        let error = scalar_chip.assign(layouter, acc.map(|acc| acc.error()))?;
        Ok(Self {
            instance: AssignedFoldingInstance {
                phase1_commitment,
                phase2_commitment,
                instances,
                challenges: AssignedChallenges::from_scalars(shape, challenges.into_iter()),
            },
            betas,
            error,
        })
    }

    /// The accumulator as field elements: the points of the phase-1 and
    /// phase-2 commitments (in public-input format), the public inputs,
    /// `θ⃗, β, γ, trash⃗, y⃗`, `β⃗`, `e`. In-circuit analog of
    /// [`accumulator_as_public_input`].
    pub fn as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        let inst = &self.instance;
        let mut out = Vec::new();
        let phase1 = points::<S>(&inst.phase1_commitment)?;
        let phase2 = points::<S>(&inst.phase2_commitment)?;
        for (point, _) in phase1.into_iter().chain(phase2) {
            out.extend(curve_chip.as_public_input(layouter, point)?);
        }
        out.extend(inst.instances.iter().flatten().cloned());
        out.extend(inst.challenges.scalars().cloned());
        out.extend(self.betas.iter().cloned());
        out.push(self.error.clone());
        Ok(out)
    }
}

/// Off-circuit encoding of [`AssignedFoldingAccumulator::as_public_input`].
pub fn accumulator_as_public_input<S: SelfEmulation>(acc: &NativeAccumulator<S>) -> Vec<S::F> {
    let inst = acc.instance();
    let points = native_points(inst.phase1_commitment())
        .into_iter()
        .chain(native_points(inst.phase2_commitment()));
    points
        .flat_map(|p| S::AssignedPoint::as_public_input(&p))
        .chain(inst.instances().iter().flatten().copied())
        .chain(native_challenges(inst.challenges()))
        .chain(acc.betas().iter().copied())
        .chain([acc.error()])
        .collect()
}

impl<S: SelfEmulation> AssignedFoldingInstance<S> {
    /// Absorbs the commitments and the public inputs: phase-1 commitment,
    /// phase-2 commitment, then every public input, column by column. Mirrors
    /// the native `FoldingInstance::absorb_commitments_and_instances`.
    pub fn absorb_commitments_and_instances(
        &self,
        layouter: &mut impl Layouter<S::F>,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<(), Error> {
        transcript.common_commitment(layouter, &self.phase1_commitment)?;
        transcript.common_commitment(layouter, &self.phase2_commitment)?;
        (self.instances.iter().flatten()).try_for_each(|pi| transcript.common_scalar(layouter, pi))
    }
}
