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
//! `R_i`, `Σ_i ρ_i (R_i + [γ](A_i − F_i)) = O`, checked as a single MSM over
//! all terms but `R_1` that must equal `−R_1`, which holds
//! for all `i` except with negligible probability (the `R_i` are fixed before
//! `ρ`). Under `truncated-challenges` every scalar of the MSM has at most 128
//! bits: `γ, ρ_i` are truncated and `γρ_i` is split with GLV, so one
//! 128-step ladder serves all points, against one per point for
//! `[γ](F − A)`. Complete additions handle equal, opposite and identity
//! points.
//!
//! No subgroup check is performed on the `R_i` or on fresh commitments
//! (project decision): a small-order component could be injected, and is
//! rejected by the decider's pairing check.

use ff::{Field, PrimeField};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    field::AssignedNative,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
    },
    types::AssignedBit,
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
    /// messages (`F_1 … F_{log n}`, then `K_0 … K_{d−2}`) and the commitment
    /// products from `folding_proof`.
    ///
    /// The transcript absorbs `acc_hash` (one element) instead of the
    /// accumulator: it must be the hash that binds `acc`, e.g. the one in the
    /// previous step's public input (the native fold takes it as `acc_hash`).
    ///
    /// WARNING: that hash must be a collision-resistant hash of the ENTIRE
    /// accumulator, computed by the caller (as the IVC does, with Poseidon over
    /// `accumulator_as_public_input`): the transcript binds only the hash, so
    /// anything else lets a prover choose the accumulator after seeing `γ`.
    ///
    /// The products are checked (the circuit is unsatisfiable on a wrong
    /// one), unless `discarded` is set: for a caller that throws the result
    /// away in some cases (a genesis step, with no real fold to prove), it
    /// waives the check there, so that a dummy `folding_proof` is accepted.
    pub fn fold(
        &self,
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedFoldingAccumulator<S>,
        acc_hash: &AssignedNative<S::F>,
        fresh: &AssignedFoldingInstance<S>,
        folding_proof: Value<Vec<u8>>,
        discarded: Option<&AssignedBit<S::F>>,
    ) -> Result<AssignedFoldingAccumulator<S>, Error> {
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
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedFoldingAccumulator<S>,
        acc_hash: &AssignedNative<S::F>,
        fresh: &AssignedFoldingInstance<S>,
        folding_proof: Value<Vec<u8>>,
    ) -> Result<
        (
            AssignedFoldingAccumulator<S>,
            AssignedBoundedScalar<S::F>,
            TranscriptGadget<S>,
        ),
        Error,
    > {
        let chip = &self.scalar_chip;
        let mut transcript = self.new_transcript(layouter, folding_proof)?;
        transcript.common_scalar(layouter, acc_hash)?;
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
        Ok((next, gamma, transcript))
    }

    /// A folding challenge: truncated under `truncated-challenges`, as
    /// natively (`squeeze_fold_challenge`).
    fn squeeze_fold_challenge(
        &self,
        layouter: &mut impl Layouter<S::F>,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedBoundedScalar<S::F>, Error> {
        let x = transcript.squeeze_challenge(layouter)?;
        #[cfg(feature = "truncated-challenges")]
        let x = crate::verifier::utils::truncate::<S::F>(layouter, &self.scalar_chip, &x)?;
        #[cfg(not(feature = "truncated-challenges"))]
        let x = AssignedBoundedScalar::new(&x, None);
        Ok(x)
    }

    /// The folded commitments `acc + [γ](fresh − acc)`, point by point (see
    /// the module documentation): reads the products `R_i` from the
    /// transcript, squeezes the `ρ_i` and checks them with one MSM.
    pub(crate) fn fold_commitments(
        &self,
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedFoldingInstance<S>,
        fresh: &AssignedFoldingInstance<S>,
        gamma: &AssignedBoundedScalar<S::F>,
        transcript: &mut TranscriptGadget<S>,
        discarded: Option<&AssignedBit<S::F>>,
    ) -> Result<(AssignedKZGMultiCommitment<S>, AssignedKZGMultiCommitment<S>), Error> {
        let products = [
            transcript.read_commitment(layouter, &self.shape.phase1_labels)?,
            transcript.read_commitment(layouter, &self.shape.phase2_labels)?,
        ];
        let r = products.iter().map(points).collect::<Result<Vec<_>, _>>()?.concat();
        let a = [&acc.phase1, &acc.phase2]
            .map(points)
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?;
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
            // ρ_1 = 1: the term of `R_1` is moved out of the MSM (see below).
            let neg_f = S::negate(layouter, curve, f)?;
            let e = S::add(layouter, curve, a, &neg_f)?; // A − F
            if i == 0 {
                scalars.push((gamma.scalar.clone(), gamma.bound.bits() as usize));
                bases.push(e);
            } else {
                let rho = self.squeeze_fold_challenge(layouter, transcript)?;
                let rho_bits = rho.bound.bits() as usize;
                let gamma_rho = chip.mul(layouter, &gamma.scalar, &rho.scalar, None)?;
                let ((k1, k2), (e1, e2)) = S::glv_split(layouter, curve, &gamma_rho, &e)?;
                let half = (S::F::NUM_BITS as usize).div_ceil(2);
                scalars.extend([(k1, half), (k2, half), (rho.scalar, rho_bits)]);
                bases.extend([e1, e2, r.clone()]);
            }
            folded.push(AssignedKZGCommitment::simple(
                S::add(layouter, curve, a, r)?,
                label.clone(),
            ));
        }
        // The MSM covers all terms but `R_1` (`ρ_1 = 1`): it must equal `−R_1`.
        let mut lhs = S::msm(layouter, curve, &scalars, &bases)?;
        let neg_r1 = S::negate(layouter, curve, points(&products[0])?[0].0)?;
        if let Some(discarded) = discarded {
            lhs = curve.select(layouter, discarded, &neg_r1, &lhs)?;
        }
        curve.assert_equal(layouter, &lhs, &neg_r1)?;

        let split = self.shape.phase1_labels.len();
        let phase2 = folded.split_off(split);
        Ok((
            AssignedKZGMultiCommitment(folded),
            AssignedKZGMultiCommitment(phase2),
        ))
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
