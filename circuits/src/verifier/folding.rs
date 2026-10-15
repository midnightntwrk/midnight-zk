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
//! Every curve point `A` of the phase-1 and phase-2 commitments (one per
//! fflonk chunk) is folded as `A + R` with `R = [γ](F − A)` read from the
//! folding proof (the prover computes it) and absorbed after `γ`. One check
//! covers all points: for challenges `ρ_1 = 1, ρ_2, …` squeezed after the
//! `R_i`, `Σ_i ρ_i (R_i + [γ](A_i − F_i)) = O` in a single MSM, which holds
//! for all `i` except with negligible probability (the `R_i` are fixed before
//! `ρ`). Every scalar of the MSM has at most 128 bits: `γ, ρ_i` are truncated
//! and `γρ_i` is split with GLV, so one 128-step ladder serves all points,
//! against one per point for `[γ](F − A)`. Complete additions handle equal,
//! opposite and identity points. Points are assigned without subgroup check
//! (out of scope).

use std::marker::PhantomData;

use ff::{Field, PrimeField};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    transcript::Hashable,
};

use crate::{
    field::AssignedNative,
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        ecc::EccInstructions,
    },
    types::AssignedBit,
    verifier::{
        AssignedKZGCommitment, AssignedKZGMultiCommitment, AssignedVk, CommitmentBases, CurveChip,
        InCircuitPCS, InCircuitTranscript, PoseidonTranscriptGadget, ScalarChip, VerifierGadget,
        folding_types::{
            AssignedChallenges, AssignedFoldingAccumulator, AssignedFoldingInstance, FoldingEngine,
            FoldingShape, NativeAccumulator, points, trash_powers,
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
        let trash_powers = trash_powers::<E>(
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
    /// messages (`F_1 … F_{log n}`, then `K_0 … K_{d−2}`) and the commitment
    /// products from `folding_proof`.
    ///
    /// The transcript absorbs `acc_hash` (one element) instead of the
    /// accumulator: it must be the hash that binds `acc`, e.g. the one in the
    /// previous step's public input (the native fold takes it as `acc_hash`).
    ///
    /// The products are checked (the circuit is unsatisfiable on a wrong
    /// one), unless `discarded` is set: for a caller that throws the result
    /// away in some cases (a genesis step, with no real fold to prove), it
    /// waives the check there, so that a dummy `folding_proof` is accepted.
    pub fn fold(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: &AssignedFoldingAccumulator<E>,
        acc_hash: &AssignedNative<E::Fr>,
        fresh: &AssignedFoldingInstance<E>,
        folding_proof: Value<Vec<u8>>,
        discarded: Option<&AssignedBit<E::Fr>>,
    ) -> Result<AssignedFoldingAccumulator<E>, Error> {
        let (mut next, gamma, mut transcript) =
            self.fold_scalars(layouter, acc, acc_hash, fresh, folding_proof)?;
        let (phase1, phase2) = self.fold_commitments(
            layouter,
            &acc.instance,
            fresh,
            &gamma,
            &mut transcript,
            discarded,
        )?;
        next.instance.phase1 = phase1;
        next.instance.phase2 = phase2;
        Ok(next)
    }

    /// [`Self::fold`] without the commitment folding: replays the folding
    /// transcript and folds every scalar. Returns the next accumulator with
    /// `acc`'s (unfolded) commitments, the folding challenge `γ` and the
    /// transcript, to continue with [`Self::fold_commitments`].
    pub(crate) fn fold_scalars(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: &AssignedFoldingAccumulator<E>,
        acc_hash: &AssignedNative<E::Fr>,
        fresh: &AssignedFoldingInstance<E>,
        folding_proof: Value<Vec<u8>>,
    ) -> Result<
        (
            AssignedFoldingAccumulator<E>,
            AssignedBoundedScalar<E::Fr>,
            PoseidonTranscriptGadget<E::Fr>,
        ),
        Error,
    > {
        let chip = &self.scalar_chip;
        let mut transcript = self.new_transcript(layouter, folding_proof)?;
        transcript.common(layouter, &self.scalar_chip, acc_hash)?;
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

        let gamma = self.squeeze_fold_challenge(layouter, &mut transcript)?;
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
        Ok((next, gamma, transcript))
    }

    /// A truncated folding challenge, as natively (`squeeze_fold_challenge`).
    fn squeeze_fold_challenge(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        transcript: &mut PoseidonTranscriptGadget<E::Fr>,
    ) -> Result<AssignedBoundedScalar<E::Fr>, Error> {
        let x = transcript.squeeze_challenge(layouter)?;
        crate::verifier::utils::truncate::<E::Fr>(layouter, &self.scalar_chip, &x)
    }

    /// The folded commitments `acc + [γ](fresh − acc)`, point by point (see
    /// the module documentation): reads the products `R_i` from the
    /// transcript, squeezes the `ρ_i` and checks them with one MSM. The check
    /// is waived when `discarded` is set.
    pub(crate) fn fold_commitments(
        &self,
        layouter: &mut impl Layouter<E::Fr>,
        acc: &AssignedFoldingInstance<E>,
        fresh: &AssignedFoldingInstance<E>,
        gamma: &AssignedBoundedScalar<E::Fr>,
        transcript: &mut PoseidonTranscriptGadget<E::Fr>,
        discarded: Option<&AssignedBit<E::Fr>>,
    ) -> Result<(AssignedKZGMultiCommitment<E>, AssignedKZGMultiCommitment<E>), Error> {
        let products = [
            transcript.read::<AssignedKZGMultiCommitment<E>>(
                layouter,
                &self.curve_chip,
                &self.shape.phase1_labels,
            )?,
            transcript.read::<AssignedKZGMultiCommitment<E>>(
                layouter,
                &self.curve_chip,
                &self.shape.phase2_labels,
            )?,
        ];
        let r = products.iter().map(points).collect::<Result<Vec<_>, _>>()?.concat();
        let a = [&acc.phase1, &acc.phase2].map(points).into_iter().collect::<Result<Vec<_>, _>>()?;
        let f = [&fresh.phase1, &fresh.phase2]
            .map(points)
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?;
        let (a, f) = (a.concat(), f.concat());
        assert_eq!(a.len(), f.len(), "folding commitments of different groups");
        assert_eq!(a.len(), r.len(), "folding products of an unexpected shape");

        let (chip, curve) = (&self.scalar_chip, &self.curve_chip);
        let mut scalars = vec![];
        let mut bases = vec![];
        let mut folded = vec![];
        for (i, (((a, label), (f, _)), (r, _))) in a.into_iter().zip(f).zip(r).enumerate() {
            // ρ_1 = 1, so `R_1` is added outside the MSM.
            let neg_f = curve.negate(layouter, f)?;
            let e = curve.add(layouter, a, &neg_f)?; // A − F
            if i == 0 {
                scalars.push((gamma.scalar.clone(), gamma.bound.bits() as usize));
                bases.push(e);
            } else {
                let rho = self.squeeze_fold_challenge(layouter, transcript)?;
                let rho_bits = rho.bound.bits() as usize;
                let gamma_rho = chip.mul(layouter, &gamma.scalar, &rho.scalar, None)?;
                let ((k1, k2), (e1, e2)) = curve.glv_split(layouter, &gamma_rho, &e)?;
                let half = (E::Fr::NUM_BITS as usize).div_ceil(2);
                scalars.extend([(k1, half), (k2, half), (rho.scalar, rho_bits)]);
                bases.extend([e1, e2, r.clone()]);
            }
            folded.push(AssignedKZGCommitment::simple(curve.add(layouter, a, r)?, label.clone()));
        }
        // The MSM covers all terms but `R_1` (`ρ_1 = 1`): it must equal `−R_1`.
        let mut lhs = curve.msm_by_bounded_scalars(layouter, &scalars, &bases)?;
        let neg_r1 = curve.negate(layouter, points(&products[0])?[0].0)?;
        if let Some(discarded) = discarded {
            lhs = curve.select(layouter, discarded, &neg_r1, &lhs)?;
        }
        curve.assert_equal(layouter, &lhs, &neg_r1)?;

        let split = self.shape.phase1_labels.len();
        let phase2 = folded.split_off(split);
        Ok((AssignedKZGMultiCommitment(folded), AssignedKZGMultiCommitment(phase2)))
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
