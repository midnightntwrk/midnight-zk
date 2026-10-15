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

//! Assigned data of the in-circuit folding verifier ([`super::FoldingGadget`]):
//! the in-circuit analogs of `midnight_proofs::plonk::protogalaxy`'s
//! [`Challenges`], `FoldingInstance` and [`Accumulator`], their shape, their
//! transcript encoding and their public-input encoding.

use ff::Field;
use midnight_curves::pairing::Engine;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        ConstraintSystem, Error,
        protogalaxy::{Accumulator, Challenges, folding_degree},
    },
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
    transcript::Hashable,
};

use crate::{
    field::AssignedNative,
    hash::poseidon::{PoseidonState, constants::PoseidonField},
    instructions::{ArithInstructions, AssignmentInstructions, PublicInputInstructions},
    types::Instantiable,
    verifier::{
        AssignedG1, AssignedKZGCommitment, AssignedKZGMultiCommitment, AssignedPoint,
        CommitmentBases, CurveChip, InCircuitKZGEngine, InCircuitPCS, InCircuitTranscript,
        PoseidonTranscriptGadget, ScalarChip,
        argument::{phase1_labels, phase2_labels},
    },
};

/// A pairing engine whose field and G1 points can be hashed by the in-circuit
/// Poseidon transcript, as the folding verifier does.
pub trait FoldingEngine:
    InCircuitKZGEngine<Fr: FoldingField, G1: Hashable<PoseidonState<<Self as Engine>::Fr>>>
{
}

impl<E> FoldingEngine for E where
    E: InCircuitKZGEngine<Fr: FoldingField, G1: Hashable<PoseidonState<<E as Engine>::Fr>>>
{
}

/// A field the in-circuit Poseidon transcript absorbs.
pub trait FoldingField: PoseidonField + Hashable<PoseidonState<Self>> {}

impl<F: PoseidonField + Hashable<PoseidonState<F>>> FoldingField for F {}

/// The off-circuit accumulator folded by [`super::FoldingGadget`].
pub type NativeAccumulator<E, PCS> = Accumulator<<E as Engine>::Fr, PCS>;

/// Everything the folding verifier circuit needs to know about the folded
/// relation, fixed at circuit-configuration time.
#[derive(Clone, Debug)]
pub struct FoldingShape {
    /// `log n`, the length of `β⃗` and the degree of the perturbator `F`.
    pub(crate) log_n: usize,
    /// `d_total`, the degree of `G` (`d_total − 1` coefficients of `K`).
    pub(crate) d_total: usize,
    /// Labels of the curve points of the phase-1 commitment (one per chunk).
    pub(crate) phase1_labels: Vec<PolynomialLabel>,
    /// Labels of the curve points of the phase-2 commitment (one per chunk).
    pub(crate) phase2_labels: Vec<PolynomialLabel>,
    /// Number of public inputs per instance column.
    pub(crate) instance_lens: Vec<usize>,
    pub(crate) nb_theta: usize,
    /// Number of powers of the trash challenge (`cs.max_trash_terms()`).
    pub(crate) nb_trash: usize,
    pub(crate) nb_y: usize,
}

impl FoldingShape {
    /// The shape of the folding of instances of the (finalized) constraint
    /// system `cs` over a domain of `2^log_n` rows, with `instance_lens`
    /// public inputs per instance column.
    pub fn new<E, PCS>(cs: &ConstraintSystem<E::Fr>, log_n: u32, instance_lens: &[usize]) -> Self
    where
        E: InCircuitKZGEngine,
        PCS: InCircuitPCS<E::Fr>,
    {
        assert_eq!(cs.num_instance_columns(), instance_lens.len());
        Self {
            log_n: log_n as usize,
            d_total: folding_degree(cs),
            phase1_labels: PCS::fixed_base_labels(&phase1_labels(cs)),
            phase2_labels: PCS::fixed_base_labels(&phase2_labels(cs, cs.degree())),
            instance_lens: instance_lens.to_vec(),
            nb_theta: cs.nb_theta_challenges(),
            nb_trash: cs.max_trash_terms(),
            nb_y: cs.nb_y_challenges(),
        }
    }

    /// `c_var`, the number of folded curve points.
    pub fn nb_points(&self) -> usize {
        self.phase1_labels.len() + self.phase2_labels.len()
    }

    /// The number of curve points of the phase-1 and of the phase-2
    /// commitment (one per chunk).
    pub fn nb_phase_points(&self) -> [usize; 2] {
        [self.phase1_labels.len(), self.phase2_labels.len()]
    }
}

/// In-circuit [`Challenges`]: `θ⃗, β, γ, trash⃗, y⃗`.
#[derive(Clone, Debug)]
pub struct AssignedChallenges<E: InCircuitKZGEngine> {
    pub(crate) theta: Vec<AssignedNative<E::Fr>>,
    pub(crate) beta: AssignedNative<E::Fr>,
    pub(crate) gamma: AssignedNative<E::Fr>,
    pub(crate) trash_powers: Vec<AssignedNative<E::Fr>>,
    pub(crate) y: Vec<AssignedNative<E::Fr>>,
}

impl<E: InCircuitKZGEngine> AssignedChallenges<E> {
    /// The challenges in absorption order: `θ⃗, β, γ, trash, y⃗`.
    pub(crate) fn scalars(&self) -> impl Iterator<Item = &AssignedNative<E::Fr>> {
        (self.theta.iter())
            .chain([&self.beta, &self.gamma])
            .chain(&self.trash_powers)
            .chain(&self.y)
    }

    /// Rebuilds the challenges from scalars in [`Self::scalars`] order.
    pub(crate) fn from_scalars(
        shape: &FoldingShape,
        mut scalars: impl Iterator<Item = AssignedNative<E::Fr>>,
    ) -> Self {
        let mut next = || scalars.next().expect("enough challenges");
        let theta = (0..shape.nb_theta).map(|_| next()).collect();
        let (beta, gamma) = (next(), next());
        let trash_powers = (0..shape.nb_trash).map(|_| next()).collect();
        let y = (0..shape.nb_y).map(|_| next()).collect();
        Self {
            theta,
            beta,
            gamma,
            trash_powers,
            y,
        }
    }
}

/// `(1, c, ..., c^{m-1})` for the trash challenge `c`: in-circuit analog of
/// the powers a fresh instance carries (`m - 1` multiplications).
pub(crate) fn trash_powers<E: FoldingEngine>(
    layouter: &mut impl Layouter<E::Fr>,
    scalar_chip: &ScalarChip<E::Fr>,
    c: &AssignedNative<E::Fr>,
    m: usize,
) -> Result<Vec<AssignedNative<E::Fr>>, Error> {
    if m == 0 {
        return Ok(vec![]);
    }
    let mut powers = vec![scalar_chip.assign_fixed(layouter, E::Fr::ONE)?];
    for i in 1..m {
        let next = if i == 1 {
            c.clone()
        } else {
            scalar_chip.mul(layouter, &powers[i - 1], c, None)?
        };
        powers.push(next);
    }
    Ok(powers)
}

/// In-circuit `FoldingInstance`: the phase-1 and phase-2 commitments (one
/// curve point per chunk), the public inputs and the challenges.
#[derive(Clone, Debug)]
pub struct AssignedFoldingInstance<E: InCircuitKZGEngine> {
    pub(crate) phase1: AssignedKZGMultiCommitment<E>,
    pub(crate) phase2: AssignedKZGMultiCommitment<E>,
    pub(crate) instances: Vec<Vec<AssignedNative<E::Fr>>>,
    pub(crate) challenges: AssignedChallenges<E>,
}

/// In-circuit [`Accumulator`]: a folded instance, `β⃗` and `e`.
#[derive(Clone, Debug)]
pub struct AssignedFoldingAccumulator<E: InCircuitKZGEngine> {
    pub(crate) instance: AssignedFoldingInstance<E>,
    pub(crate) betas: Vec<AssignedNative<E::Fr>>,
    pub(crate) error: AssignedNative<E::Fr>,
}

/// The curve points of a commitment read from a transcript or assigned by
/// [`assign_commitment`], in order.
pub(crate) fn points<E: InCircuitKZGEngine>(
    commitment: &AssignedKZGMultiCommitment<E>,
) -> Result<Vec<(&AssignedG1<E>, &PolynomialLabel)>, Error> {
    (commitment.0.iter())
        .map(|inner| match inner {
            AssignedKZGCommitment::Simple(AssignedPoint::Variable(p), label) => Ok((p, label)),
            _ => Err(Error::Synthesis(
                "folding needs commitments made of assigned points".into(),
            )),
        })
        .collect()
}

/// Assigns a commitment made of one point per label (no subgroup check).
fn assign_commitment<E: InCircuitKZGEngine>(
    layouter: &mut impl Layouter<E::Fr>,
    curve_chip: &CurveChip<E>,
    labels: &[PolynomialLabel],
    values: Value<Vec<E::G1>>,
) -> Result<AssignedKZGMultiCommitment<E>, Error> {
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
            AssignedKZGCommitment::assign(layouter, curve_chip, value, label.clone())
        })
        .collect::<Result<_, Error>>()?;
    Ok(AssignedKZGMultiCommitment(inners))
}

/// Assigns `len` scalars (witnesses).
fn assign_scalars<E: InCircuitKZGEngine>(
    layouter: &mut impl Layouter<E::Fr>,
    scalar_chip: &ScalarChip<E::Fr>,
    len: usize,
    values: Value<Vec<E::Fr>>,
) -> Result<Vec<AssignedNative<E::Fr>>, Error> {
    let values = values.map(|v| {
        assert_eq!(v.len(), len, "unexpected number of scalars");
        v
    });
    (0..len)
        .map(|i| scalar_chip.assign(layouter, values.as_ref().map(|v| v[i])))
        .collect()
}

fn native_points<C>(commitment: &impl CommitmentBases<C>) -> Vec<C> {
    commitment.bases().into_iter().map(|(_, p)| p).collect()
}

fn native_challenges<F: Copy>(c: &Challenges<F>) -> Vec<F> {
    (c.theta.iter())
        .chain([&c.beta, &c.gamma])
        .chain(&c.trash_powers)
        .chain(&c.y)
        .copied()
        .collect()
}

impl<E: InCircuitKZGEngine> AssignedFoldingAccumulator<E> {
    /// Assigns an off-circuit accumulator of the given shape as a witness,
    /// its points without subgroup check. The caller binds it (e.g. to a hash
    /// in the public input).
    pub fn assign<PCS>(
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
        shape: &FoldingShape,
        acc: Value<&NativeAccumulator<E, PCS>>,
    ) -> Result<Self, Error>
    where
        PCS: PolynomialCommitmentScheme<E::Fr>,
        PCS::Commitment: CommitmentBases<E::G1>,
    {
        let instance = acc.map(|acc| acc.instance());
        let phase1 = assign_commitment(
            layouter,
            curve_chip,
            &shape.phase1_labels,
            instance.map(|i| native_points(i.phase1_commitment())),
        )?;
        let phase2 = assign_commitment(
            layouter,
            curve_chip,
            &shape.phase2_labels,
            instance.map(|i| native_points(i.phase2_commitment())),
        )?;
        let instances = (shape.instance_lens.iter().enumerate())
            .map(|(j, len)| {
                let values = instance.map(|i| i.instances()[j].clone());
                assign_scalars::<E>(layouter, scalar_chip, *len, values)
            })
            .collect::<Result<_, Error>>()?;
        let nb_challenges = shape.nb_theta + 2 + shape.nb_trash + shape.nb_y;
        let challenges = instance.map(|i| native_challenges(i.challenges()));
        let challenges = assign_scalars::<E>(layouter, scalar_chip, nb_challenges, challenges)?;
        let betas = acc.map(|acc| acc.betas().to_vec());
        Ok(Self {
            instance: AssignedFoldingInstance {
                phase1,
                phase2,
                instances,
                challenges: AssignedChallenges::from_scalars(shape, challenges.into_iter()),
            },
            betas: assign_scalars::<E>(layouter, scalar_chip, shape.log_n, betas)?,
            error: scalar_chip.assign(layouter, acc.map(|acc| acc.error()))?,
        })
    }

    /// The accumulator as field elements: the points of the phase-1 and
    /// phase-2 commitments (in public-input format), the public inputs,
    /// `θ⃗, β, γ, trash⃗, y⃗`, `β⃗`, `e`. In-circuit analog of
    /// [`accumulator_as_public_input`]; hash these to bind an accumulator.
    pub fn as_public_input(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
    ) -> Result<Vec<AssignedNative<E::Fr>>, Error> {
        let mut out = Vec::new();
        let inst = &self.instance;
        for (point, _) in points(&inst.phase1)?.into_iter().chain(points(&inst.phase2)?) {
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
pub fn accumulator_as_public_input<E, PCS>(acc: &NativeAccumulator<E, PCS>) -> Vec<E::Fr>
where
    E: InCircuitKZGEngine,
    PCS: PolynomialCommitmentScheme<E::Fr>,
    PCS::Commitment: CommitmentBases<E::G1>,
{
    let inst = acc.instance();
    let points = native_points(inst.phase1_commitment())
        .into_iter()
        .chain(native_points(inst.phase2_commitment()));
    points
        .flat_map(|p| <AssignedG1<E> as Instantiable<E::Fr>>::as_public_input(&p))
        .chain(inst.instances().iter().flatten().copied())
        .chain(native_challenges(inst.challenges()))
        .chain(acc.betas().iter().copied())
        .chain([acc.error()])
        .collect()
}

impl<E: FoldingEngine> AssignedFoldingInstance<E> {
    /// Absorbs the commitments and the public inputs: phase-1 commitment,
    /// phase-2 commitment, then every public input, column by column.
    pub(crate) fn absorb(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
        transcript: &mut PoseidonTranscriptGadget<E::Fr>,
    ) -> Result<(), Error> {
        transcript.common(layouter, curve_chip, &self.phase1)?;
        transcript.common(layouter, curve_chip, &self.phase2)?;
        (self.instances.iter().flatten())
            .try_for_each(|pi| transcript.common(layouter, scalar_chip, pi))
    }
}

impl<E: FoldingEngine> AssignedFoldingAccumulator<E> {
    /// Absorbs the whole accumulator: the instance (see
    /// [`AssignedFoldingInstance::absorb`]), `θ⃗, β, γ, trash⃗, y⃗`, `β⃗`, `e`.
    pub(crate) fn absorb(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
        transcript: &mut PoseidonTranscriptGadget<E::Fr>,
    ) -> Result<(), Error> {
        self.instance.absorb(layouter, curve_chip, scalar_chip, transcript)?;
        (self.instance.challenges.scalars())
            .chain(&self.betas)
            .chain([&self.error])
            .try_for_each(|s| transcript.common(layouter, scalar_chip, s))
    }
}
