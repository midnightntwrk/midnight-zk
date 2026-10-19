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

//! In-circuit Protogalaxy folding verifier, for one fresh instance per round
//! (`k = 1`): the in-circuit analog of `read_instance`, `Accumulator::init`
//! and `Accumulator::fold` of `midnight_proofs::plonk::protogalaxy` (see its
//! module documentation for the protocol). It replays exactly the same
//! transcripts, so that the accumulator computed in-circuit equals the native
//! one.
//!
//! # Fresh transcript per round
//! Like the native verifier, every round (and the initialisation) starts a
//! fresh transcript seeded only by the round's data: the accumulator, the
//! fresh instance and the folding messages. The challenges of a round are
//! bound to that round's data, which is what the error-term argument needs,
//! but not to the history of the chain: binding the chain is the job of the
//! step circuit's public input (typically the accumulator, see
//! [`AssignedFoldingAccumulator::as_public_input`]). Do not use this gadget
//! where that binding is absent.
//!
//! # `k = 1`
//! The folding domain is `{0, 1}`: `L₀(γ) = 1 − γ`, `L₁(γ) = γ`,
//! `Z(γ) = γ(γ − 1)`, and `K` has `d − 1` coefficients. Everything linear
//! (public inputs, challenges, commitments) folds as `acc + γ·(fresh − acc)`.
//!
//! # Commitment folding
//! Every curve point `A_i` of the phase-1 and phase-2 commitments (one per
//! fflonk chunk) is folded as `A_i + P_i`, with the product
//! `P_i = [γ](F_i − A_i)` of the fresh point `F_i` read from the folding proof
//! (the prover computes it, after `γ`; see step 8 of the folding in the native
//! module). The `P_i` are absorbed as they are read, and the in-circuit check
//! covers all of them with a single MSM: for challenges `ρ_1 = 1, ρ_2, …`
//! squeezed (and truncated to 128 bits, like `γ`) after the `P_i`,
//! `Σ_i ρ_i·(P_i + [γ]·(A_i − F_i)) = O`.
//!
//! Soundness: the `P_i` are fixed before the `ρ_i` are known, so if some `P_i`
//! is wrong, the sum is a nonzero combination of the (nonzero) errors with
//! uniformly random coefficients, and vanishes with probability at most
//! `2⁻¹²⁸` per round. All scalars of the MSM are short: `ρ_i` has 128 bits and
//! `γ·ρ_i`, full width, is split by GLV into two half-width scalars (over
//! `±(A_i − F_i)` and `±φ(A_i − F_i)`), so one ladder serves all points,
//! against one scalar multiplication per point for `[γ](F_i − A_i)`.
//! Complete additions handle equal, opposite and identity points. Points are
//! assigned without subgroup check (out of scope).

use ff::{Field, PrimeField};
use group::Group;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::PolynomialLabel,
};

use crate::{
    field::AssignedNative,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
    },
    types::AssignedBit,
    verifier::{
        AssignedKZGCommitment, AssignedKZGMultiCommitment, AssignedVk, InCircuitPCS, SelfEmulation,
        folding_types::{
            AssignedChallenges, AssignedFoldingAccumulator, AssignedFoldingInstance, FoldingShape,
            NativeAccumulator, points,
        },
        transcript_gadget::TranscriptGadget,
        utils::{AssignedBoundedScalar, mul_add, truncate},
        verifier_gadget::VerifierGadget,
    },
};

/// In-circuit folding verifier (Protogalaxy, one fresh instance per round).
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
        assert!(shape.degree >= 2, "folding needs a degree of at least 2");
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

    /// Reads a fresh instance (the partial proof of one step: the commit
    /// phases only) for the public inputs `instances`, by parsing its trace
    /// as the native `read_instance` does. Constrains the key's `k` to the
    /// shape's `log n`.
    ///
    /// # Panics
    ///
    /// If the key or the public inputs do not have the gadget's shape.
    pub fn read_instance(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk: &AssignedVk<S>,
        instances: &[&[AssignedNative<S::F>]],
        partial_proof: Value<Vec<u8>>,
    ) -> Result<AssignedFoldingInstance<S>, Error> {
        self.scalar_chip.assert_equal_to_fixed(
            layouter,
            vk.k(),
            S::F::from(self.shape.log_n as u64),
        )?;

        let verifier =
            VerifierGadget::<S>::new(&self.curve_chip, &self.scalar_chip, &self.sponge_chip);
        let (trace, _) = verifier.parse_trace(layouter, vk, &[], instances, partial_proof)?;

        let fresh = AssignedFoldingInstance {
            phase1_commitment: trace.phase1_committed.commitment().clone(),
            phase2_commitment: trace.phase2_committed.commitment().clone(),
            instances: instances.iter().map(|i| i.to_vec()).collect(),
            challenges: AssignedChallenges {
                theta: trace.theta,
                beta: trace.beta,
                gamma: trace.gamma,
                trash: trace.trash_challenges,
                y: trace.y,
            },
        };
        self.assert_shape(&fresh);
        Ok(fresh)
    }

    /// Assigns an off-circuit accumulator (witness, no subgroup check). The
    /// caller binds it, e.g. to the public input of the step circuit.
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
        self.assert_shape(&fresh);
        let mut transcript = self.new_transcript(layouter, Value::known(vec![]))?;
        fresh.absorb_commitments_and_instances(layouter, &mut transcript)?;
        let beta = transcript.squeeze_challenge(layouter)?;
        Ok(AssignedFoldingAccumulator {
            betas: self.squares(layouter, &beta)?,
            error: self.scalar_chip.assign_fixed(layouter, S::F::ZERO)?,
            instance: fresh,
        })
    }

    /// Folds `fresh` into `acc` (`Accumulator::fold` with one fresh instance),
    /// reading the folding messages (`F₁ … F_{log n}`, then `K₀ … K_{d−2}`)
    /// and the commitment products (phase 1, then phase 2) from
    /// `folding_proof`.
    ///
    /// The products are checked (the circuit is unsatisfiable on a wrong one),
    /// unless `discarded` is a bit set to 1: for a caller that throws the
    /// result away in some cases (e.g. the first step of a chain, which folds
    /// a dummy proof), it waives the check there.
    pub fn fold(
        &self,
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedFoldingAccumulator<S>,
        fresh: &AssignedFoldingInstance<S>,
        folding_proof: Value<Vec<u8>>,
        discarded: Option<&AssignedBit<S::F>>,
    ) -> Result<AssignedFoldingAccumulator<S>, Error> {
        self.assert_shape(&acc.instance);
        self.assert_shape(fresh);
        assert_eq!(acc.betas.len(), self.shape.log_n);

        let mut transcript = self.new_transcript(layouter, folding_proof)?;
        acc.absorb(layouter, &mut transcript)?;
        fresh.absorb_commitments_and_instances(layouter, &mut transcript)?;

        let delta = transcript.squeeze_challenge(layouter)?;
        let deltas = self.squares(layouter, &delta)?;
        let mut f_coeffs = vec![acc.error.clone()];
        for _ in 0..self.shape.log_n {
            f_coeffs.push(transcript.read_scalar(layouter)?);
        }
        let alpha = transcript.squeeze_challenge(layouter)?;
        let k_coeffs = (0..self.shape.degree - 1)
            .map(|_| transcript.read_scalar(layouter))
            .collect::<Result<Vec<_>, Error>>()?;
        let gamma = self.squeeze_truncated(layouter, &mut transcript)?;

        // β⃗* = β⃗ + α·δ⃗.
        let betas = (acc.betas.iter().zip(&deltas))
            .map(|(beta, delta)| mul_add(layouter, &self.scalar_chip, &alpha, delta, beta))
            .collect::<Result<_, Error>>()?;

        let f_alpha = self.eval_polynomial(layouter, &f_coeffs, &alpha)?;
        let k_gamma = self.eval_polynomial(layouter, &k_coeffs, &gamma.scalar)?;
        let error = self.next_error(layouter, &f_alpha, &k_gamma, &gamma.scalar)?;

        let (a, f) = (&acc.instance, fresh);
        let g = &gamma.scalar;
        let instances = (a.instances.iter().zip(&f.instances))
            .map(|(a, f)| self.fold_all(layouter, a, f, g))
            .collect::<Result<_, Error>>()?;
        let (ac, fc) = (&a.challenges, &f.challenges);
        let challenges = AssignedChallenges {
            theta: self.fold_all(layouter, &ac.theta, &fc.theta, g)?,
            beta: self.fold_one(layouter, &ac.beta, &fc.beta, g)?,
            gamma: self.fold_one(layouter, &ac.gamma, &fc.gamma, g)?,
            trash: self.fold_all(layouter, &ac.trash, &fc.trash, g)?,
            y: self.fold_all(layouter, &ac.y, &fc.y, g)?,
        };
        let (phase1_commitment, phase2_commitment) =
            self.fold_commitments(layouter, a, f, &gamma, &mut transcript, discarded)?;
        Ok(AssignedFoldingAccumulator {
            instance: AssignedFoldingInstance {
                phase1_commitment,
                phase2_commitment,
                instances,
                challenges,
            },
            betas,
            error,
        })
    }

    /// A transcript over a fresh sponge, reading from `proof`.
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

    /// Panics unless `instance` has the gadget's shape.
    fn assert_shape(&self, instance: &AssignedFoldingInstance<S>) {
        let shape = &self.shape;
        let lens: Vec<_> = instance.instances.iter().map(Vec::len).collect();
        let c = &instance.challenges;
        assert_eq!(
            instance.phase1_commitment.0.len(),
            shape.phase1_labels.len()
        );
        assert_eq!(
            instance.phase2_commitment.0.len(),
            shape.phase2_labels.len()
        );
        assert_eq!(
            lens, shape.instance_lens,
            "public inputs of an unexpected shape"
        );
        assert_eq!(
            (c.theta.len(), c.trash.len(), c.y.len()),
            (shape.nb_theta, shape.nb_trash, shape.nb_y),
            "challenges of an unexpected shape"
        );
    }

    /// `e* = F(α)·(1 − γ) + γ(γ − 1)·K(γ)`, given `F(α)` and `K(γ)`.
    fn next_error(
        &self,
        layouter: &mut impl Layouter<S::F>,
        f_alpha: &AssignedNative<S::F>,
        k_gamma: &AssignedNative<S::F>,
        gamma: &AssignedNative<S::F>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let chip = &self.scalar_chip;
        let l0 = chip.linear_combination(layouter, &[(-S::F::ONE, gamma.clone())], S::F::ONE)?;
        let z = chip.add_and_mul(
            layouter,
            (-S::F::ONE, gamma),
            (S::F::ZERO, gamma),
            (S::F::ZERO, gamma),
            S::F::ZERO,
            S::F::ONE,
        )?;
        let f_l0 = chip.mul(layouter, f_alpha, &l0, None)?;
        mul_add(layouter, chip, &z, k_gamma, &f_l0)
    }

    /// A challenge truncated to 128 bits, as the native verifier does for the
    /// folding challenges.
    fn squeeze_truncated(
        &self,
        layouter: &mut impl Layouter<S::F>,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedBoundedScalar<S::F>, Error> {
        let x = transcript.squeeze_challenge(layouter)?;
        truncate::<S::F>(layouter, &self.scalar_chip, &x)
    }

    /// The folded commitments `acc + [γ](fresh − acc)` of phase 1 and phase 2,
    /// point by point (see the module documentation): reads the products `P_i`
    /// from the transcript, checks them with one MSM and returns `A_i + P_i`.
    fn fold_commitments(
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
        let p = both_phases::<S>(&products[0], &products[1])?;
        let a = both_phases::<S>(&acc.phase1_commitment, &acc.phase2_commitment)?;
        let f = both_phases::<S>(&fresh.phase1_commitment, &fresh.phase2_commitment)?;
        assert_eq!(a.len(), f.len(), "folding commitments of different groups");
        assert_eq!(a.len(), p.len(), "folding products of an unexpected shape");
        assert!(!a.is_empty(), "folding needs at least one commitment");

        let (chip, curve) = (&self.scalar_chip, &self.curve_chip);
        let half_width = (S::F::NUM_BITS as usize).div_ceil(2);
        let first_product = p[0].0;
        let (mut scalars, mut bases, mut folded) = (vec![], vec![], vec![]);
        for (i, (((a, label), (f, f_label)), (p, _))) in a.into_iter().zip(f).zip(p).enumerate() {
            assert_eq!(label, f_label, "folding commitments of different labels");
            let neg_f = S::negate(layouter, curve, f)?;
            let diff = S::add(layouter, curve, a, &neg_f)?; // A − F
            if i == 0 {
                // ρ_1 = 1: `P_1` is added outside the MSM, and `γ` is short.
                scalars.push((gamma.scalar.clone(), gamma.bound.bits() as usize));
                bases.push(diff);
            } else {
                let rho = self.squeeze_truncated(layouter, transcript)?;
                let gamma_rho = chip.mul(layouter, &gamma.scalar, &rho.scalar, None)?;
                let ((k1, k2), (d1, d2)) = S::glv_split(layouter, curve, &gamma_rho, &diff)?;
                scalars.extend([
                    (k1, half_width),
                    (k2, half_width),
                    (rho.scalar, rho.bound.bits() as usize),
                ]);
                bases.extend([d1, d2, p.clone()]);
            }
            let sum = S::add(layouter, curve, a, p)?;
            folded.push(AssignedKZGCommitment::simple(sum, label.clone()));
        }

        let msm = S::msm(layouter, curve, &scalars, &bases)?;
        let mut check = S::add(layouter, curve, &msm, first_product)?;
        if let Some(discarded) = discarded {
            let identity = curve.assign_fixed(layouter, S::C::identity())?;
            check = curve.select(layouter, discarded, &identity, &check)?;
        }
        curve.assert_equal_to_fixed(layouter, &check, S::C::identity())?;

        let phase2 = folded.split_off(self.shape.phase1_labels.len());
        Ok((
            AssignedKZGMultiCommitment(folded),
            AssignedKZGMultiCommitment(phase2),
        ))
    }

    /// `a + x·(b − a)`.
    fn fold_one(
        &self,
        layouter: &mut impl Layouter<S::F>,
        a: &AssignedNative<S::F>,
        b: &AssignedNative<S::F>,
        x: &AssignedNative<S::F>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let diff = self.scalar_chip.sub(layouter, b, a)?;
        mul_add(layouter, &self.scalar_chip, x, &diff, a)
    }

    /// `a + x·(b − a)` for every pair of the (equally long) slices.
    fn fold_all(
        &self,
        layouter: &mut impl Layouter<S::F>,
        a: &[AssignedNative<S::F>],
        b: &[AssignedNative<S::F>],
        x: &AssignedNative<S::F>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        assert_eq!(a.len(), b.len());
        (a.iter().zip(b)).map(|(a, b)| self.fold_one(layouter, a, b, x)).collect()
    }

    /// `(x, x², x⁴, …)`, `log n` entries.
    fn squares(
        &self,
        layouter: &mut impl Layouter<S::F>,
        x: &AssignedNative<S::F>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        let mut out: Vec<AssignedNative<S::F>> = Vec::with_capacity(self.shape.log_n);
        for _ in 0..self.shape.log_n {
            let next = match out.last() {
                Some(last) => self.scalar_chip.mul(layouter, last, last, None)?,
                None => x.clone(),
            };
            out.push(next);
        }
        Ok(out)
    }

    /// `Σᵢ coeffs[i]·xⁱ` by Horner, constant term first.
    ///
    /// # Panics
    ///
    /// If `coeffs` is empty.
    fn eval_polynomial(
        &self,
        layouter: &mut impl Layouter<S::F>,
        coeffs: &[AssignedNative<S::F>],
        x: &AssignedNative<S::F>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let (last, rest) = coeffs.split_last().expect("a polynomial has coefficients");
        (rest.iter().rev()).try_fold(last.clone(), |acc, c| {
            mul_add(layouter, &self.scalar_chip, &acc, x, c)
        })
    }
}

/// The points (and labels) of a phase-1 commitment followed by those of the
/// phase-2 one.
fn both_phases<'a, S: SelfEmulation>(
    phase1: &'a AssignedKZGMultiCommitment<S>,
    phase2: &'a AssignedKZGMultiCommitment<S>,
) -> Result<Vec<(&'a S::AssignedPoint, &'a PolynomialLabel)>, Error> {
    Ok(points::<S>(phase1)?.into_iter().chain(points::<S>(phase2)?).collect())
}
