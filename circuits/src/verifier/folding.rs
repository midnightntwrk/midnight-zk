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
//! scalar under `truncated-challenges`, one GLV base; full-width otherwise)
//! and one complete addition. Complete additions handle `C = acc` and the
//! identity, and the scalar multiplication accepts an identity base.
//! Points are assigned without subgroup check (subgroup checks out of scope).

use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssertionInstructions, AssignmentInstructions},
    verifier::{
        AssignedKZGCommitment, AssignedKZGMultiCommitment, AssignedVk, InCircuitPCS, SelfEmulation,
        VerifierGadget,
        folding_types::{
            AssignedChallenges, AssignedFoldingAccumulator, AssignedFoldingInstance, FoldingShape,
            NativeAccumulator, points, trash_powers,
        },
        transcript_gadget::TranscriptGadget,
        utils::{AssignedBoundedScalar, eval_polynomial, mul_add},
    },
};

/// In-circuit folding verifier (scalar-error Protogalaxy, 2-to-1).
#[derive(Clone, Debug)]
pub struct FoldingGadget<S: SelfEmulation> {
    curve_chip: S::CurveChip,
    scalar_chip: S::ScalarChip,
    sponge_chip: S::SpongeChip,
    shape: FoldingShape,
}

impl<S> FoldingGadget<S>
where
    S: SelfEmulation,
    S::PCS: InCircuitPCS<S, AssignedCommitment = AssignedKZGMultiCommitment<S>>,
{
    /// Creates a folding gadget for relations of the given shape.
    pub fn new(
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        sponge_chip: &S::SpongeChip,
        shape: FoldingShape,
    ) -> Self {
        assert!(shape.d_total >= 2, "folding needs d_total ≥ 2");
        Self {
            curve_chip: curve_chip.clone(),
            scalar_chip: scalar_chip.clone(),
            sponge_chip: sponge_chip.clone(),
            shape,
        }
    }

    /// The shape of the folded relation.
    pub fn shape(&self) -> &FoldingShape {
        &self.shape
    }

    fn new_transcript(
        &self,
        layouter: &mut impl Layouter<S::F>,
        proof: Value<Vec<u8>>,
    ) -> Result<TranscriptGadget<S>, Error> {
        let mut transcript =
            TranscriptGadget::new(&self.scalar_chip, &self.curve_chip, &self.sponge_chip);
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
        layouter: &mut impl Layouter<S::F>,
        vk: &AssignedVk<S>,
        instances: &[&[AssignedNative<S::F>]],
        partial_proof: Value<Vec<u8>>,
    ) -> Result<AssignedFoldingInstance<S>, Error> {
        let log_n = S::F::from(self.shape.log_n as u64);
        self.scalar_chip.assert_equal_to_fixed(layouter, vk.k(), log_n)?;
        let lens: Vec<usize> = instances.iter().map(|i| i.len()).collect();
        assert_eq!(
            lens, self.shape.instance_lens,
            "public inputs of an unexpected shape"
        );

        let verifier =
            VerifierGadget::<S>::new(&self.curve_chip, &self.scalar_chip, &self.sponge_chip);
        let (trace, _) = verifier.parse_trace(layouter, vk, &[], instances, partial_proof)?;
        let trash_powers = trash_powers::<S>(
            layouter,
            &self.scalar_chip,
            &trace.trash_challenge,
            self.shape.nb_trash,
        )?;
        Ok(AssignedFoldingInstance {
            phase1: trace.phase1_committed.commitment().clone(),
            phase2: trace.phase2_committed.commitment().clone(),
            instances: instances.iter().map(|i| i.to_vec()).collect(),
            challenges: AssignedChallenges {
                theta: trace.theta,
                beta: trace.beta,
                gamma: trace.gamma,
                trash_powers,
                y: trace.y,
            },
        })
    }

    /// Assigns an off-circuit accumulator (witness, no subgroup check). The
    /// caller binds it, e.g. to a hash in the public input.
    pub fn assign_accumulator(
        &self,
        layouter: &mut impl Layouter<S::F>,
        acc: Value<&NativeAccumulator<S>>,
    ) -> Result<AssignedFoldingAccumulator<S>, Error> {
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
        layouter: &mut impl Layouter<S::F>,
        fresh: AssignedFoldingInstance<S>,
    ) -> Result<AssignedFoldingAccumulator<S>, Error> {
        let mut transcript = self.new_transcript(layouter, Value::known(vec![]))?;
        fresh.absorb(layouter, &mut transcript)?;
        let beta = transcript.squeeze_challenge(layouter)?;
        Ok(AssignedFoldingAccumulator {
            instance: fresh,
            betas: self.squares(layouter, &beta)?,
            error: self.scalar_chip.assign_fixed(layouter, S::F::ZERO)?,
        })
    }

    /// Folds `fresh` into `acc` (`Accumulator::fold`), reading the folding
    /// messages (`F_1 … F_{log n}`, then `K_0 … K_{d−2}`) from
    /// `folding_proof`.
    pub fn fold(
        &self,
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedFoldingAccumulator<S>,
        fresh: &AssignedFoldingInstance<S>,
        folding_proof: Value<Vec<u8>>,
    ) -> Result<AssignedFoldingAccumulator<S>, Error> {
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
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedFoldingAccumulator<S>,
        fresh: &AssignedFoldingInstance<S>,
        folding_proof: Value<Vec<u8>>,
    ) -> Result<(AssignedFoldingAccumulator<S>, AssignedBoundedScalar<S::F>), Error> {
        let chip = &self.scalar_chip;
        let mut transcript = self.new_transcript(layouter, folding_proof)?;
        acc.absorb(layouter, &mut transcript)?;
        fresh.absorb(layouter, &mut transcript)?;

        let delta = transcript.squeeze_challenge(layouter)?;
        let deltas = self.squares(layouter, &delta)?;
        let mut f_coeffs = vec![acc.error.clone()];
        for _ in 0..self.shape.log_n {
            f_coeffs.push(transcript.read_scalar(layouter)?);
        }

        let alpha = transcript.squeeze_challenge(layouter)?;
        let k_coeffs = (0..self.shape.d_total - 1)
            .map(|_| transcript.read_scalar(layouter))
            .collect::<Result<Vec<_>, Error>>()?;

        let gamma = transcript.squeeze_challenge(layouter)?;
        #[cfg(feature = "truncated-challenges")]
        let gamma = crate::verifier::utils::truncate::<S::F>(layouter, chip, &gamma)?;
        #[cfg(not(feature = "truncated-challenges"))]
        let gamma = AssignedBoundedScalar::new(&gamma, None);
        let g = &gamma.scalar;

        // β⃗* = β⃗ + α·δ⃗.
        let betas = (acc.betas.iter().zip(&deltas))
            .map(|(beta, delta)| mul_add(layouter, chip, &alpha, delta, beta))
            .collect::<Result<_, Error>>()?;

        // e' = F(α)·(1 − γ) + γ(γ − 1)·K(γ).
        let f_alpha =
            eval_polynomial(layouter, chip, &f_coeffs.iter().collect::<Vec<_>>(), &alpha)?;
        let k_gamma = eval_polynomial(layouter, chip, &k_coeffs.iter().collect::<Vec<_>>(), g)?;
        let l0 = chip.linear_combination(layouter, &[(-S::F::ONE, g.clone())], S::F::ONE)?;
        let z = chip.add_and_mul(
            layouter,
            (-S::F::ONE, g),
            (S::F::ZERO, g),
            (S::F::ZERO, g),
            S::F::ZERO,
            S::F::ONE,
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
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedKZGMultiCommitment<S>,
        fresh: &AssignedKZGMultiCommitment<S>,
        gamma: &AssignedBoundedScalar<S::F>,
    ) -> Result<AssignedKZGMultiCommitment<S>, Error> {
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
                let minus_a = S::negate(layouter, curve_chip, a)?;
                let diff = S::add(layouter, curve_chip, f, &minus_a)?;
                let scaled = S::msm(layouter, curve_chip, std::slice::from_ref(&scalar), &[diff])?;
                let folded = S::add(layouter, curve_chip, a, &scaled)?;
                Ok(AssignedKZGCommitment::simple(folded, label.clone()))
            })
            .collect::<Result<_, Error>>()?;
        Ok(AssignedKZGMultiCommitment(inners))
    }

    /// `a + x·(b − a)` for every pair.
    fn fold_all<'a>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        a: impl Iterator<Item = &'a AssignedNative<S::F>>,
        b: impl Iterator<Item = &'a AssignedNative<S::F>>,
        x: &AssignedNative<S::F>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
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
        layouter: &mut impl Layouter<S::F>,
        x: &AssignedNative<S::F>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        let mut out = vec![x.clone()];
        while out.len() < self.shape.log_n {
            let last = out.last().unwrap();
            out.push(self.scalar_chip.mul(layouter, last, last, None)?);
        }
        Ok(out)
    }
}
