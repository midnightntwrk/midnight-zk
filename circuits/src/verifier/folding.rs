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

//! In-circuit Protogalaxy folding verifier: the in-circuit analog of
//! `Accumulator::{init, fold}` and `read_instance` of
//! `midnight_proofs::plonk::protogalaxy` (see its module documentation for
//! the protocol). It replays exactly the same transcripts, so that the
//! accumulator computed in-circuit equals the native one.
//!
//! # Fresh transcript per round
//! Like the native verifier, every round (and the initialisation) starts a
//! fresh transcript seeded only by the round's data: the accumulator, the
//! fresh instance and the folding messages. The challenges of a round are
//! bound to that round's data, which is what the error-term argument needs,
//! but not to the history of the chain: binding the chain is the job of the
//! step circuit's public input (typically a hash of the accumulator, see
//! [`AssignedFoldingAccumulator::as_public_input`]). Do not use this gadget
//! where that binding is absent.
//!
//! # Commitment folding
//! Every curve point of the phase-1 and phase-2 commitments (one per fflonk
//! chunk) is folded as `acc + [γ](C − acc)`: one complete addition for the
//! difference, one in-circuit scalar multiplication by `γ` (a 128-bit
//! truncated scalar, one GLV base)
//! and one complete addition. Complete additions handle `C = acc` and the
//! identity, and the scalar multiplication accepts an identity base.
//! Points are assigned without subgroup check (subgroup checks out of scope).

use std::marker::PhantomData;

use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    transcript::Hashable,
};

use crate::{
    field::AssignedNative,
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ecc::EccInstructions,
    },
    verifier::{
        AssignedKZGCommitment, AssignedKZGMultiCommitment, AssignedVk, CommitmentBases, CurveChip,
        InCircuitPCS, InCircuitTranscript, PoseidonTranscriptGadget, ScalarChip, VerifierGadget,
        folding_types::{
            AssignedChallenges, AssignedFoldingAccumulator, AssignedFoldingInstance, FoldingEngine,
            FoldingShape, NativeAccumulator, points,
        },
        utils::{AssignedBoundedScalar, eval_polynomial, mul_add},
    },
};

/// In-circuit folding verifier (scalar-error Protogalaxy, 2-to-1).
#[derive(Clone, Debug)]
pub struct FoldingGadget<E: FoldingEngine, PCS> {
    curve_chip: CurveChip<E>,
    scalar_chip: ScalarChip<E::Fr>,
    sponge_chip: PoseidonChip<E::Fr>,
    shape: FoldingShape,
    _pcs: PhantomData<PCS>,
}

impl<E, PCS> FoldingGadget<E, PCS>
where
    E: FoldingEngine,
    PCS: InCircuitPCS<
            E::Fr,
            AssignedCommitment = AssignedKZGMultiCommitment<E>,
            CommitmentChip = CurveChip<E>,
        >,
    PCS::Commitment: CommitmentBases<E::G1> + Hashable<PoseidonState<E::Fr>>,
{
    /// Creates a folding gadget for relations of the given shape.
    pub fn new(
        curve_chip: &CurveChip<E>,
        scalar_chip: &ScalarChip<E::Fr>,
        sponge_chip: &PoseidonChip<E::Fr>,
        shape: FoldingShape,
    ) -> Self {
        assert!(shape.d_total >= 2, "folding needs d_total ≥ 2");
        Self {
            curve_chip: curve_chip.clone(),
            scalar_chip: scalar_chip.clone(),
            sponge_chip: sponge_chip.clone(),
            shape,
            _pcs: PhantomData,
        }
    }

    /// The shape of the folded relation.
    pub fn shape(&self) -> &FoldingShape {
        &self.shape
    }

    fn new_transcript(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        proof: Value<Vec<u8>>,
    ) -> Result<PoseidonTranscriptGadget<E::Fr>, Error> {
        let mut transcript = PoseidonTranscriptGadget::new(&self.sponge_chip);
        transcript.init_with_proof(layouter, proof)?;
        Ok(transcript)
    }

    /// Reads a fresh instance (the partial proof of one step: the commit
    /// phases only) for the public inputs `instances`, replaying its own
    /// transcript as `read_instance` does: verifying key, public inputs,
    /// phase-1 commitment, `θ⃗, β, γ, trash`, phase-2 commitment, `y⃗`.
    /// Constrains the key's `k` to the shape's `log n`.
    pub fn read_instance(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        vk: &AssignedVk<E::Fr, PCS>,
        instances: &[&[AssignedNative<E::Fr>]],
        partial_proof: Value<Vec<u8>>,
    ) -> Result<AssignedFoldingInstance<E>, Error> {
        let log_n = E::Fr::from(self.shape.log_n as u64);
        self.scalar_chip.assert_equal_to_fixed(layouter, vk.k(), log_n)?;
        let lens: Vec<usize> = instances.iter().map(|i| i.len()).collect();
        assert_eq!(
            lens, self.shape.instance_lens,
            "public inputs of an unexpected shape"
        );

        let verifier = VerifierGadget::<E::Fr, PCS>::new(&self.curve_chip, &self.scalar_chip);
        let mut transcript = self.new_transcript(layouter, partial_proof)?;
        let trace = verifier.parse_trace(layouter, vk, &[], instances, &mut transcript)?;
        Ok(AssignedFoldingInstance {
            phase1: trace.phase1_committed.commitment().clone(),
            phase2: trace.phase2_committed.commitment().clone(),
            instances: instances.iter().map(|i| i.to_vec()).collect(),
            challenges: AssignedChallenges {
                theta: trace.theta,
                beta: trace.beta,
                gamma: trace.gamma,
                trash_challenge: trace.trash_challenge,
                y: trace.y,
            },
        })
    }

    /// Assigns an off-circuit accumulator (witness, no subgroup check). The
    /// caller binds it, e.g. to a hash in the public input.
    pub fn assign_accumulator(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: Value<&NativeAccumulator<E, PCS>>,
    ) -> Result<AssignedFoldingAccumulator<E>, Error> {
        AssignedFoldingAccumulator::assign(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
            &self.shape,
            acc,
        )
    }

    /// The first accumulator (`Accumulator::init`): the fresh instance itself,
    /// `e = 0` and `β⃗ = (β, β², β⁴, …)` for a `β` squeezed from a fresh
    /// transcript after absorbing the instance.
    pub fn init(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        fresh: AssignedFoldingInstance<E>,
    ) -> Result<AssignedFoldingAccumulator<E>, Error> {
        let mut transcript = self.new_transcript(layouter, Value::known(vec![]))?;
        fresh.absorb(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
            &mut transcript,
        )?;
        let beta = transcript.squeeze_challenge(layouter)?;
        Ok(AssignedFoldingAccumulator {
            instance: fresh,
            betas: self.squares(layouter, &beta)?,
            error: self.scalar_chip.assign_fixed(layouter, E::Fr::ZERO)?,
        })
    }

    /// Folds `fresh` into `acc` (`Accumulator::fold`), reading the folding
    /// messages (`F_1 … F_{log n}`, then `K_0 … K_{d−2}`) from
    /// `folding_proof`.
    pub fn fold(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: &AssignedFoldingAccumulator<E>,
        fresh: &AssignedFoldingInstance<E>,
        folding_proof: Value<Vec<u8>>,
    ) -> Result<AssignedFoldingAccumulator<E>, Error> {
        let (mut next, gamma) = self.fold_scalars(layouter, acc, fresh, folding_proof)?;
        let inst = &acc.instance;
        next.instance.phase1 =
            self.fold_commitment(layouter, &inst.phase1, &fresh.phase1, &gamma)?;
        next.instance.phase2 =
            self.fold_commitment(layouter, &inst.phase2, &fresh.phase2, &gamma)?;
        Ok(next)
    }

    /// [`Self::fold`] without the commitment folding: replays the folding
    /// transcript and folds every scalar. Returns the next accumulator with
    /// `acc`'s (unfolded) commitments, and the folding challenge `γ`.
    pub(crate) fn fold_scalars(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: &AssignedFoldingAccumulator<E>,
        fresh: &AssignedFoldingInstance<E>,
        folding_proof: Value<Vec<u8>>,
    ) -> Result<(AssignedFoldingAccumulator<E>, AssignedBoundedScalar<E::Fr>), Error> {
        let chip = &self.scalar_chip;
        let mut transcript = self.new_transcript(layouter, folding_proof)?;
        acc.absorb(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
            &mut transcript,
        )?;
        fresh.absorb(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
            &mut transcript,
        )?;

        let delta = transcript.squeeze_challenge(layouter)?;
        let deltas = self.squares(layouter, &delta)?;
        let mut f_coeffs = vec![acc.error.clone()];
        for _ in 0..self.shape.log_n {
            f_coeffs.push(transcript.read::<AssignedNative<E::Fr>>(
                layouter,
                &self.scalar_chip,
                &(),
            )?);
        }

        let alpha = transcript.squeeze_challenge(layouter)?;
        let k_coeffs = (0..self.shape.d_total - 1)
            .map(|_| transcript.read::<AssignedNative<E::Fr>>(layouter, &self.scalar_chip, &()))
            .collect::<Result<Vec<_>, Error>>()?;

        let gamma = transcript.squeeze_challenge(layouter)?;
        let gamma = crate::verifier::utils::truncate::<E::Fr>(layouter, chip, &gamma)?;
        let g = &gamma.scalar;

        // β⃗* = β⃗ + α·δ⃗.
        let betas = (acc.betas.iter().zip(&deltas))
            .map(|(beta, delta)| mul_add(layouter, chip, &alpha, delta, beta))
            .collect::<Result<_, Error>>()?;

        // e' = F(α)·(1 − γ) + γ(γ − 1)·K(γ).
        let f_alpha =
            eval_polynomial(layouter, chip, &f_coeffs.iter().collect::<Vec<_>>(), &alpha)?;
        let k_gamma = eval_polynomial(layouter, chip, &k_coeffs.iter().collect::<Vec<_>>(), g)?;
        let l0 = chip.linear_combination(layouter, &[(-E::Fr::ONE, g.clone())], E::Fr::ONE)?;
        let z = chip.add_and_mul(
            layouter,
            (-E::Fr::ONE, g),
            (E::Fr::ZERO, g),
            (E::Fr::ZERO, g),
            E::Fr::ZERO,
            E::Fr::ONE,
        )?;
        let f_l0 = chip.mul(layouter, &f_alpha, &l0, None)?;
        let error = mul_add(layouter, chip, &z, &k_gamma, &f_l0)?;

        // Public inputs and challenges: acc + γ·(fresh − acc).
        let (a, f) = (&acc.instance, fresh);
        let instances = (a.instances.iter().zip(&f.instances))
            .map(|(a, f)| self.fold_all(layouter, a.iter(), f.iter(), g))
            .collect::<Result<_, Error>>()?;
        let challenges =
            self.fold_all(layouter, a.challenges.scalars(), f.challenges.scalars(), g)?;

        let next = AssignedFoldingAccumulator {
            instance: AssignedFoldingInstance {
                phase1: a.phase1.clone(),
                phase2: a.phase2.clone(),
                instances,
                challenges: AssignedChallenges::from_scalars(&self.shape, challenges.into_iter()),
            },
            betas,
            error,
        };
        Ok((next, gamma))
    }

    /// `acc + [γ](fresh − acc)`, point by point.
    pub(crate) fn fold_commitment(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: &AssignedKZGMultiCommitment<E>,
        fresh: &AssignedKZGMultiCommitment<E>,
        gamma: &AssignedBoundedScalar<E::Fr>,
    ) -> Result<AssignedKZGMultiCommitment<E>, Error> {
        let (acc, fresh) = (points(acc)?, points(fresh)?);
        assert_eq!(
            acc.len(),
            fresh.len(),
            "folding commitments of different groups"
        );
        let scalar = (gamma.scalar.clone(), gamma.bound.bits() as usize);
        let curve_chip = &self.curve_chip;
        let inners = (acc.into_iter().zip(fresh))
            .map(|((a, label), (f, _))| {
                let minus_a = curve_chip.negate(layouter, a)?;
                let diff = curve_chip.add(layouter, f, &minus_a)?;
                let scaled = curve_chip.msm_by_bounded_scalars(
                    layouter,
                    std::slice::from_ref(&scalar),
                    &[diff],
                )?;
                let folded = curve_chip.add(layouter, a, &scaled)?;
                Ok(AssignedKZGCommitment::simple(folded, label.clone()))
            })
            .collect::<Result<_, Error>>()?;
        Ok(AssignedKZGMultiCommitment(inners))
    }

    /// `a + x·(b − a)` for every pair.
    fn fold_all<'a>(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        a: impl Iterator<Item = &'a AssignedNative<E::Fr>>,
        b: impl Iterator<Item = &'a AssignedNative<E::Fr>>,
        x: &AssignedNative<E::Fr>,
    ) -> Result<Vec<AssignedNative<E::Fr>>, Error> {
        (a.zip(b))
            .map(|(a, b)| {
                let diff = self.scalar_chip.sub(layouter, b, a)?;
                mul_add(layouter, &self.scalar_chip, x, &diff, a)
            })
            .collect()
    }

    /// `(x, x², x⁴, …)`, `log n` entries.
    fn squares(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        x: &AssignedNative<E::Fr>,
    ) -> Result<Vec<AssignedNative<E::Fr>>, Error> {
        let mut out = vec![x.clone()];
        while out.len() < self.shape.log_n {
            let last = out.last().unwrap();
            out.push(self.scalar_chip.mul(layouter, last, last, None)?);
        }
        Ok(out)
    }
}
