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

//! A chip implementing the PLONK KZG-based verifier from our halo2 dependency.
//!
//! We assume the CS of the verified circuit defines exactly one instance
//! column. (This is the norm throughout our whole codebase anyway.)
use std::{
    collections::{BTreeMap, HashSet},
    fmt::Debug,
    iter,
};

use ff::Field;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::{EvaluationDomain, PolynomialLabel, Rotation},
};

use crate::{
    field::AssignedNative,
    instructions::{
        ArithInstructions, PublicInputInstructions, assignments::AssignmentInstructions,
    },
    verifier::{
        Accumulator, AssignedAccumulator, AssignedEvaluationDomain, AssignedVk, SelfEmulation,
        VerifyingKey, argument,
        expressions::{
            eval_expression, lookup::lookup_expressions, permutation::permutation_expressions,
            trash::trash_expressions,
        },
        pcs::{InCircuitHomomorphicCommitment, InCircuitPCS, VerifierQuery},
        traces::VerifierTrace,
        transcript_gadget::TranscriptGadget,
        utils::{evaluate_lagrange_polynomials, inner_product, pow_of_two, square_k_times, sum},
    },
};

/// A gadget for KZG-based in-circuit proof verification.
#[derive(Clone, Debug)]
#[doc(hidden)] // A bug in rustc prevents us from documenting the verifier gadget.
pub struct VerifierGadget<S: SelfEmulation> {
    pub(super) curve_chip: S::CurveChip,
    pub(super) scalar_chip: S::ScalarChip,
    pub(super) sponge_chip: S::SpongeChip,
}

impl<S: SelfEmulation> Chip<S::F> for VerifierGadget<S> {
    type Config = ();
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &()
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Creates a new verifier gadget from its underlying components.
    pub fn new(
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        sponge_chip: &S::SpongeChip,
    ) -> Self {
        Self {
            curve_chip: curve_chip.clone(),
            scalar_chip: scalar_chip.clone(),
            sponge_chip: sponge_chip.clone(),
        }
    }
}

impl<S: SelfEmulation, PCS: InCircuitPCS<S>> PublicInputInstructions<S::F, AssignedVk<S, PCS>>
    for VerifierGadget<S>
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S, PCS>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        Ok([
            self.scalar_chip.as_public_input(layouter, &assigned_vk.transcript_repr)?,
            self.scalar_chip.as_public_input(layouter, assigned_vk.k())?,
            self.scalar_chip.as_public_input(layouter, assigned_vk.omega())?,
        ]
        .concat())
    }

    fn constrain_as_public_input(
        &self,
        _layouter: &mut impl Layouter<S::F>,
        _assigned_vk: &AssignedVk<S, PCS>,
    ) -> Result<(), Error> {
        unimplemented!(
            "We intend [assign_vk_as_public_input] to be the only entry point
             for assigned verifying keys."
        )
    }

    fn assign_as_public_input(
        &self,
        _layouter: &mut impl Layouter<S::F>,
        _value: Value<VerifyingKey<S>>,
    ) -> Result<AssignedVk<S, PCS>, Error> {
        unimplemented!(
            "We intend [assign_vk_as_public_input] to be the only entry point
            for assigned verifying keys. (Note that its signature is more complex
            that this function's signature.)"
        )
    }
}

impl<S: SelfEmulation> PublicInputInstructions<S::F, AssignedAccumulator<S>> for VerifierGadget<S> {
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned: &AssignedAccumulator<S>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        Ok([
            assigned.lhs.in_circuit_as_public_input(layouter, &self.curve_chip)?,
            assigned.rhs.in_circuit_as_public_input(layouter, &self.curve_chip)?,
        ]
        .concat())
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned: &AssignedAccumulator<S>,
    ) -> Result<(), Error> {
        (assigned.lhs).constrain_as_public_input(layouter, &self.curve_chip, &self.scalar_chip)?;
        (assigned.rhs).constrain_as_public_input(layouter, &self.curve_chip, &self.scalar_chip)
    }

    fn assign_as_public_input(
        &self,
        _layouter: &mut impl Layouter<S::F>,
        _value: Value<Accumulator<S>>,
    ) -> Result<AssignedAccumulator<S>, Error> {
        unimplemented!(
            "This is intentionally unimplemented, use [constrain_as_public_input] instead"
        )
    }
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Constrains the given accumulator as a public input. The (fixed and
    /// non-fixed) scalars of its RHS are constrained in committed form (as a
    /// committed instance), whereas the rest of the accumulator is constrained
    /// as a normal instance.
    ///
    /// See [AssignedAccumulator::as_public_input_with_committed_scalars] for
    /// the off-circuit analog of this function.
    pub fn constrain_acc_as_public_input_with_committed_scalars(
        &self,
        layouter: &mut impl Layouter<S::F>,
        acc: &AssignedAccumulator<S>,
    ) -> Result<(), Error> {
        (acc.lhs).constrain_as_public_input(layouter, &self.curve_chip, &self.scalar_chip)?;
        (acc.rhs).constrain_as_public_input_with_committed_scalars(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
        )
    }

    /// Witnesses the "collapsed" form of a KZG accumulator.
    ///
    /// The expected shape is:
    /// * LHS: exactly one `Variable` entry labeled `NoLabel`.
    /// * RHS: one `Fixed` entry per label in `fixed_base_labels` plus one
    ///   `Variable` entry labeled `NoLabel`.
    ///
    /// This shape matches the invariant maintained by the KZG multiopen
    /// accumulation after `collapse()` has been called off-circuit.
    ///
    /// # Errors
    ///
    /// If the expected shape is not satisfied.
    pub fn assign_collapsed_accumulator(
        &self,
        layouter: &mut impl Layouter<S::F>,
        fixed_base_labels: &[PolynomialLabel],
        value: Value<Accumulator<S>>,
    ) -> Result<AssignedAccumulator<S>, Error> {
        let acc = AssignedAccumulator::assign(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
            &[PolynomialLabel::NoLabel],
            &[fixed_base_labels, &[PolynomialLabel::NoLabel]].concat(),
            &HashSet::new(),
            &fixed_base_labels.iter().cloned().collect(),
            value,
        )?;

        Ok(acc)
    }

    /// Accumulates several accumulators together. The resulting acc will
    /// satisfy the invariant iff all the accumulators individually do.
    pub fn accumulate(
        &self,
        layouter: &mut impl Layouter<S::F>,
        accs: &[AssignedAccumulator<S>],
    ) -> Result<AssignedAccumulator<S>, Error> {
        AssignedAccumulator::<S>::accumulate(
            layouter,
            self,
            &self.scalar_chip,
            &self.sponge_chip,
            accs,
        )
    }
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Assigns a verifying key as a public input: its `transcript_repr` and its
    /// evaluation domain (`k` and `omega`) are assigned in-circuit, the rest is
    /// taken off-circuit from `cs`. Since `cs` suffices to lay out the circuit,
    /// `vk` may be unknown (e.g. at keygen).
    ///
    /// The domain values `k` and `omega` are *trusted* at this point: this
    /// function does not check that they are consistent (i.e. that `omega` is a
    /// primitive `2^k`-th root of unity), nor that they are the ones of the
    /// verifying key identified by `transcript_repr`. It is the caller's
    /// responsibility to constrain them.
    ///
    /// `cs` must be finalized, i.e. its selectors must have been converted to
    /// fixed columns, as in the constraint system of a verifying key.
    pub fn assign_vk_as_public_input<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk: Value<&VerifyingKey<S>>,
        cs: &ConstraintSystem<S::F>,
    ) -> Result<AssignedVk<S, PCS>, Error> {
        if cs.num_selectors() != 0 {
            return Err(Error::Synthesis(
                "the constraint system has selectors, it must be finalized".into(),
            ));
        }

        let [transcript_repr_value, k_value, omega_value] = vk
            .map(|vk| {
                let domain = vk.get_domain();
                [
                    vk.transcript_repr(),
                    S::F::from(domain.k() as u64),
                    domain.get_omega(),
                ]
            })
            .transpose_array();
        let transcript_repr =
            self.scalar_chip.assign_as_public_input(layouter, transcript_repr_value)?;
        let k = self.scalar_chip.assign_as_public_input(layouter, k_value)?;
        let omega = self.scalar_chip.assign_as_public_input(layouter, omega_value)?;

        let domain = self.derive_domain(layouter, k, omega)?;

        Ok(assemble_vk(domain, cs, transcript_repr, None))
    }

    /// Assigns a verifying key as a constant. All the necessary information is
    /// available off-circuit, except for the `transcript_repr` and the
    /// evaluation domain, which are "assigned fixed".
    ///
    /// `cs` must be finalized, i.e. its selectors must have been converted to
    /// fixed columns, as in the constraint system of a verifying key.
    pub fn assign_fixed_vk<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        domain: &EvaluationDomain<S::F>,
        cs: &ConstraintSystem<S::F>,
        transcript_repr_constant: S::F,
    ) -> Result<AssignedVk<S, PCS>, Error> {
        if cs.num_selectors() != 0 {
            return Err(Error::Synthesis(
                "the constraint system has selectors, it must be finalized".into(),
            ));
        }

        let transcript_repr = self.scalar_chip.assign_fixed(layouter, transcript_repr_constant)?;
        let k = self.scalar_chip.assign_fixed(layouter, S::F::from(domain.k() as u64))?;
        let omega = self.scalar_chip.assign_fixed(layouter, domain.get_omega())?;
        let domain = self.derive_domain(layouter, k, omega)?;
        Ok(assemble_vk(domain, cs, transcript_repr, None))
    }

    /// Completes the assigned domain by deriving `omega_inv` and `n = 2^k` from
    /// assigned `k` and `omega` cells (in-circuit).
    pub(super) fn derive_domain(
        &self,
        layouter: &mut impl Layouter<S::F>,
        k: AssignedNative<S::F>,
        omega: AssignedNative<S::F>,
    ) -> Result<AssignedEvaluationDomain<S>, Error> {
        let omega_inv = self.scalar_chip.inv(layouter, &omega)?;
        let n = pow_of_two(layouter, &self.scalar_chip, &k)?;
        Ok(AssignedEvaluationDomain {
            k,
            omega,
            omega_inv,
            n,
        })
    }
}

/// Builds the [`AssignedVk`] of a finalized `cs` with the given assigned domain
/// and transcript representation.
///
/// If `bases` is `None`, the fixed and permutation commitments are
/// placeholders, resolved off-circuit by the decider. Otherwise, they are taken
/// from `bases`, which must contain one assigned point per fixed column and
/// per fixed permutation polynomial.
pub(super) fn assemble_vk<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    domain: AssignedEvaluationDomain<S>,
    cs: &ConstraintSystem<S::F>,
    transcript_repr: AssignedNative<S::F>,
    bases: Option<&BTreeMap<PolynomialLabel, S::AssignedPoint>>,
) -> AssignedVk<S, PCS> {
    AssignedVk {
        domain,
        phase0_commitment: vk_commitment::<S, PCS>(&cs.fixed_polys_labels(), bases),
        cs: cs.clone(),
        cs_degree: cs.degree(),
        transcript_repr,
    }
}

/// The commitment of a verifying key to the group of `labels`: a placeholder
/// if `bases` is `None`, or built from the assigned points in `bases`.
fn vk_commitment<S: SelfEmulation, PCS: InCircuitPCS<S>>(
    labels: &[PolynomialLabel],
    bases: Option<&BTreeMap<PolynomialLabel, S::AssignedPoint>>,
) -> PCS::AssignedCommitment {
    match bases {
        None => PCS::fixed_commitment(labels),
        Some(bases) => {
            let points: Vec<_> = labels.iter().map(|l| bases[l].clone()).collect();
            PCS::commitment_from_points(labels, &points)
        }
    }
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Given a plonk proof, this function parses it to extract the verifying
    /// trace.
    /// This function computes all Fiat-Shamir challenges, with the exception of
    /// `x`, which is computed in [Self::verify_algebraic_constraints]. It
    /// is the in-circuit analog of "parse_trace" from midnight-proofs at
    /// src/plonk/verifier.rs.
    ///
    /// The trace is considered to be valid if it satisfies the
    /// [algebraic
    /// constraints](crate::verifier::VerifierGadget::verify_algebraic_constraints),
    /// and the resulting accumulator satisfies the
    /// [invariant](crate::verifier::Accumulator::check).
    pub fn parse_trace<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S, PCS>,
        assigned_committed_instances: &[PCS::AssignedCommitment],
        assigned_instances: &[&[AssignedNative<S::F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<(VerifierTrace<S, PCS>, TranscriptGadget<S>), Error> {
        let cs = &assigned_vk.cs;

        // Check that instances matches the expected number of instance columns
        assert_eq!(
            cs.num_instance_columns(),
            assigned_committed_instances.len() + assigned_instances.len()
        );

        let mut transcript =
            TranscriptGadget::new(&self.scalar_chip, &self.curve_chip, &self.sponge_chip);

        transcript.init_with_proof(layouter, proof)?;

        // Hash verification key into transcript.
        let vk_absorbed = assigned_vk.absorb_into(layouter, &mut transcript)?;
        let phase0_committed = argument::committed_from_key(&vk_absorbed);

        assigned_committed_instances
            .iter()
            .try_for_each(|com| PCS::common_commitment(&mut transcript, layouter, com))?;

        for instance in assigned_instances {
            let n = self.scalar_chip.assign_fixed(layouter, (instance.len() as u64).into())?;
            transcript.common_scalar(layouter, &n)?;
            instance.iter().try_for_each(|pi| transcript.common_scalar(layouter, pi))?;
        }

        let logups = cs
            .lookups()
            .iter()
            .map(|l| l.chunk_by_degree(assigned_vk.cs_degree))
            .collect::<Vec<_>>();

        // The advice columns and the logup multiplicities form the phase1 group.
        let phase1_labels = (0..cs.num_advice_columns())
            .map(PolynomialLabel::Advice)
            .chain((0..logups.len()).map(PolynomialLabel::LogupMultiplicities))
            .collect::<Vec<_>>();

        let phase1_committed = argument::read_committed(&phase1_labels, layouter, &mut transcript)?;

        // Sample theta challenge for keeping lookup columns linearly independent
        let theta = transcript.squeeze_challenge(layouter)?;

        let beta = transcript.squeeze_challenge(layouter)?;
        let gamma = transcript.squeeze_challenge(layouter)?;

        let trash_challenge = transcript.squeeze_challenge(layouter)?;

        let mut phase2_labels = cs.permutation().accumulator_labels(cs.degree());

        for (argument_index, logup_argument) in logups.iter().enumerate() {
            for j in 0..logup_argument.num_chunks() {
                phase2_labels.push(PolynomialLabel::LogupHelper(argument_index, j));
            }
        }

        for argument_index in 0..logups.len() {
            phase2_labels.push(PolynomialLabel::LogupAggregator(argument_index));
        }

        for argument_index in 0..cs.trashcans().len() {
            phase2_labels.push(PolynomialLabel::Trash(argument_index));
        }

        let phase2_committed = argument::read_committed(&phase2_labels, layouter, &mut transcript)?;

        // Sample y challenge, which keeps the gates linearly independent
        let y = transcript.squeeze_challenge(layouter)?;

        Ok((
            VerifierTrace {
                phase0_committed,
                phase1_committed,
                phase2_committed,
                beta,
                gamma,
                theta,
                trash_challenge,
                y,
            },
            transcript,
        ))
    }

    /// Construct, in-circuit, the commitment to the quotient polynomial
    ///
    ///  `(h_0 + x^{n-1} * h_1 + ... + x^{l*(n-1)} * h_l) * (1 - x^n)`,
    ///
    /// where `h_k` are commitments to the limbs of the quotient polynomial. It
    /// is expected to open to `-nu(x)` at `x`.
    fn compute_quotient_commitment<PCS: InCircuitPCS<S>>(
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        xn: AssignedNative<S::F>,
        splitting_factor: AssignedNative<S::F>,
        quotient_limb_commitments: &[PCS::AssignedCommitment],
    ) -> Result<PCS::AssignedCommitment, Error> {
        let mut splitting_pow =
            scalar_chip.linear_combination(layouter, &[(-S::F::ONE, xn)], S::F::ONE)?;
        let (first_com, rest_coms) = quotient_limb_commitments
            .split_first()
            .expect("at least one quotient limb commitment");

        let init = {
            let term = first_com.clone().mul(layouter, scalar_chip, &splitting_pow)?;
            splitting_pow = scalar_chip.mul(layouter, &splitting_pow, &splitting_factor, None)?;
            term
        };

        rest_coms.iter().try_fold(init, |acc, com| {
            let term = com.clone().mul(layouter, scalar_chip, &splitting_pow)?;
            splitting_pow = scalar_chip.mul(layouter, &splitting_pow, &splitting_factor, None)?;
            acc.add(layouter, scalar_chip, term)
        })
    }

    /// Given a [VerifierTrace], this function computes the opening challenge,
    /// x, and proceeds to verify the algebraic constraints with the claimed
    /// evaluations. This function does not verify the PCS proof.
    ///
    /// The proof is considered to be valid if the resulting accumulator
    /// satisfies the [invariant](crate::verifier::Accumulator::check)
    /// with respect to the relevant `tau_in_g2`.
    pub fn verify_algebraic_constraints<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S, PCS>,
        trace: VerifierTrace<S, PCS>,
        assigned_committed_instances: &[PCS::AssignedCommitment],
        assigned_instances: &[&[AssignedNative<S::F>]],
        mut transcript: TranscriptGadget<S>,
    ) -> Result<AssignedAccumulator<S>, Error> {
        let cs = &assigned_vk.cs;
        let k = &assigned_vk.domain.k;
        let nb_committed_instances = assigned_committed_instances.len();

        let VerifierTrace {
            phase0_committed,
            phase1_committed,
            phase2_committed,
            beta,
            gamma,
            theta,
            trash_challenge,
            y,
        } = trace;

        // Read commitment(s) to the quotient polynomial h(X) = nu(X)/(X^n-1) from
        // the transcript. The prover splits h(X) into `quotient_poly_degree` limbs,
        // where `quotient_poly_degree = cs_degree - 1`.
        let nb_quotient_coms = assigned_vk.cs_degree - 1;
        let limb_commitments = {
            (0..nb_quotient_coms)
                .map(|i| {
                    PCS::read_commitment(
                        &mut transcript,
                        layouter,
                        &[PolynomialLabel::QuotientPiece(i)],
                    )
                })
                .collect::<Result<Vec<_>, Error>>()?
        };

        // Sample x challenge, which is used to ensure the circuit is satisfied with
        // high probability
        let x = transcript.squeeze_challenge(layouter)?;

        let omega = &assigned_vk.domain.omega;
        let omega_inv = &assigned_vk.domain.omega_inv;
        // `n = 2^k` is larger than the rotation bounds computed below, and than the
        // length of any instance column: rotations are compile-time constants of the
        // verified circuit's `cs`, and its instance rows must fit in its own domain.
        let n = &assigned_vk.domain.n;
        let xn = square_k_times(layouter, &self.scalar_chip, &x, k)?;
        // Shared by all calls to `evaluate_lagrange_polynomials` below.
        let n_inv = self.scalar_chip.inv(layouter, n)?;

        let instance_evals = {
            let instance_queries = cs.instance_queries();
            let min_rotation = instance_queries.iter().map(|(_, rot)| rot.0).min().unwrap();
            let max_rotation = instance_queries.iter().map(|(_, rot)| rot.0).max().unwrap();

            let max_instance_len =
                assigned_instances.iter().map(|instance| instance.len()).max().unwrap_or(0);

            let l_i_s = evaluate_lagrange_polynomials(
                layouter,
                &self.scalar_chip,
                omega,
                omega_inv,
                &n_inv,
                &x,
                &xn,
                (-max_rotation)..(max_instance_len as i32 + min_rotation.abs()),
            )?;

            instance_queries
                .iter()
                .map(|(column, rotation)| {
                    if column.index() < nb_committed_instances {
                        transcript.read_scalar(layouter)
                    } else {
                        let instances = assigned_instances[column.index() - nb_committed_instances];
                        let offset = (max_rotation - rotation.0) as usize;
                        inner_product(
                            layouter,
                            &self.scalar_chip,
                            instances,
                            &l_i_s[offset..offset + instances.len()],
                        )
                    }
                })
                .collect::<Result<Vec<_>, Error>>()?
        };

        let mut x_rotations = BTreeMap::new();
        for rotation in argument::rotations::<S>(cs) {
            let point = if rotation == Rotation::cur() {
                x.clone()
            } else {
                // `omega` is assigned in-circuit, so is its rotation.
                let (base, exp) = if rotation.0 > 0 {
                    (omega, rotation.0)
                } else {
                    (omega_inv, -rotation.0)
                };
                let rotated_omega = self.scalar_chip.pow(layouter, base, exp as u64)?;
                self.scalar_chip.mul(layouter, &x, &rotated_omega, None)?
            };
            x_rotations.insert(rotation, point);
        }

        let phase0_evaluated =
            phase0_committed.evaluate(cs, &x_rotations, layouter, &mut transcript)?;
        let phase1_evaluated =
            phase1_committed.evaluate(cs, &x_rotations, layouter, &mut transcript)?;
        let phase2_evaluated =
            phase2_committed.evaluate(cs, &x_rotations, layouter, &mut transcript)?;

        let phase0_evals = &phase0_evaluated.evals_map;
        let phase1_evals = &phase1_evaluated.evals_map;
        let phase2_evals = &phase2_evaluated.evals_map;

        // The advice evaluations in the order of `cs.advice_queries`, which is how
        // the identities index them. In the phase1 group, each column's follow the
        // order of its queries.
        let mut next = vec![0; cs.num_advice_columns()];
        let advice_evals: Vec<AssignedNative<S::F>> = cs
            .advice_queries()
            .iter()
            .map(|(column, _)| {
                let i = column.index();
                let eval = phase1_evals[&PolynomialLabel::Advice(i)][next[i]].eval().clone();
                next[i] += 1;
                eval
            })
            .collect();

        // The fixed evaluations in the order of `cs.fixed_queries`, which is
        // how the identities index them.
        let mut next = vec![0; cs.num_fixed_columns()];
        let fixed_evals: Vec<AssignedNative<S::F>> = cs
            .fixed_queries()
            .iter()
            .map(|(column, _)| {
                let i = column.index();
                let eval = phase0_evals[&PolynomialLabel::Fixed(i)][next[i]].eval().clone();
                next[i] += 1;
                eval
            })
            .collect();

        // Evaluate the identities
        let nr_blinding_factors = cs.blinding_factors();
        let l_evals = evaluate_lagrange_polynomials(
            layouter,
            &self.scalar_chip,
            omega,
            omega_inv,
            &n_inv,
            &x,
            &xn,
            (-((nr_blinding_factors + 1) as i32))..1,
        )?;
        assert_eq!(l_evals.len(), 2 + nr_blinding_factors);
        let l_last = l_evals[0].clone();
        let l_blind = sum::<S::F>(
            layouter,
            &self.scalar_chip,
            &l_evals[1..=nr_blinding_factors],
        )?;
        let l_0 = l_evals[1 + nr_blinding_factors].clone();

        let mut expressions = Vec::new();
        // Evaluate polys from (custom) gates
        for gate in cs.gates().iter() {
            for poly in gate.polynomials().iter() {
                let eval = eval_expression::<S>(
                    layouter,
                    &self.scalar_chip,
                    &advice_evals,
                    &fixed_evals,
                    &instance_evals,
                    poly,
                )?;
                expressions.push(eval);
            }
        }

        // Evaluate polys from permutation argument
        permutation_expressions(
            layouter,
            &self.scalar_chip,
            cs,
            phase0_evals,
            phase2_evals,
            &advice_evals,
            &fixed_evals,
            &instance_evals,
            &l_0,
            &l_last,
            &l_blind,
            &beta,
            &gamma,
            &x,
        )?
        .into_iter()
        .for_each(|perm_id| expressions.push(perm_id));

        // Evaluate polys from lookup argument
        cs.lookups()
            .iter()
            .map(|l| l.chunk_by_degree(assigned_vk.cs_degree))
            .enumerate()
            .map(|(argument_index, argument)| {
                let per_flat_inputs: Vec<&[Vec<_>]> =
                    argument.input_expression_chunks().iter().map(|c| c.as_slice()).collect();
                lookup_expressions(
                    layouter,
                    &self.scalar_chip,
                    argument_index,
                    phase1_evals,
                    phase2_evals,
                    argument.selector_expression(),
                    &per_flat_inputs,
                    argument.table_expressions(),
                    &advice_evals,
                    &fixed_evals,
                    &instance_evals,
                    &l_0,
                    &l_last,
                    &l_blind,
                    &theta,
                    &beta,
                )
            })
            .collect::<Result<Vec<Vec<_>>, Error>>()?
            .concat()
            .into_iter()
            .for_each(|lookup_id| expressions.push(lookup_id));

        // Evaluate polys from trashcan argument
        cs.trashcans()
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                trash_expressions(
                    layouter,
                    &self.scalar_chip,
                    index,
                    phase2_evals,
                    argument.selector(),
                    argument.constraint_expressions(),
                    &advice_evals,
                    &fixed_evals,
                    &instance_evals,
                    &trash_challenge,
                )
            })
            .collect::<Result<Vec<Vec<_>>, Error>>()?
            .concat()
            .into_iter()
            .for_each(|trash_id| expressions.push(trash_id));

        let splitting_factor = self.scalar_chip.div(layouter, &xn, &x)?;

        // -nu(x): the identities batched with y by Horner's rule, negated.
        let zero: AssignedNative<S::F> = self.scalar_chip.assign_fixed(layouter, S::F::ZERO)?;
        let neg_nu_eval = expressions.iter().try_fold(zero, |acc, id| {
            self.scalar_chip.add_and_mul(
                layouter,
                (S::F::ZERO, &acc),
                (S::F::ZERO, &y),
                (-S::F::ONE, id),
                S::F::ZERO,
                S::F::ONE,
            ) // acc * y - id
        })?;

        let quotient_commitment = Self::compute_quotient_commitment::<PCS>(
            layouter,
            &self.scalar_chip,
            xn,
            splitting_factor,
            &limb_commitments,
        )?;

        // Collect queries that are checked in the multi-open argument
        //
        // The multi-open scales the first commitment by 1, which is best spent on
        // one read from the proof: the phase-0 commitments are known in advance and
        // a committed instance may be a constant, so both go after phases 1 and 2.
        let queries = iter::empty()
            .chain(phase1_evaluated.queries())
            .chain(phase2_evaluated.queries())
            .chain(phase0_evaluated.queries())
            .chain(cs.instance_queries().iter().enumerate().filter_map(
                |(query_index, &(column, rot))| {
                    if column.index() < nb_committed_instances {
                        Some(VerifierQuery::<S, PCS>::new(
                            &x_rotations[&rot],
                            &assigned_committed_instances[column.index()],
                            PolynomialLabel::CommittedInstance(column.index()),
                            &instance_evals[query_index],
                        ))
                    } else {
                        None
                    }
                },
            ))
            .chain(iter::once(VerifierQuery::new(
                &x,
                &quotient_commitment,
                PolynomialLabel::Quotient,
                &neg_nu_eval,
            )))
            .collect::<Vec<_>>();

        // We are now convinced the circuit is satisfied so long as the
        // polynomial commitments open to the correct values, which is true as long
        // as the following accumulator passes the invariant.
        PCS::multi_prepare(
            layouter,
            &self.curve_chip,
            &self.scalar_chip,
            &mut transcript,
            &queries,
        )
    }

    /// Prepares a plonk proof into a PCS instance that can be finalized or
    /// batched. It is responsibility of the verifier to check the validity of
    /// the instance columns. It is the in-circuit analog of "prepare" from
    /// midnight-proofs at src/plonk/verifier.rs.
    ///
    /// The proof is considered to be valid if the resulting accumulator
    /// satisfies the [invariant](crate::verifier::Accumulator::check)
    /// with respect to the relevant `tau_in_g2`.
    pub fn prepare<PCS: InCircuitPCS<S>>(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S, PCS>,
        assigned_committed_instances: &[PCS::AssignedCommitment],
        assigned_instances: &[&[AssignedNative<S::F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<AssignedAccumulator<S>, Error> {
        let (trace, transcript) = self.parse_trace(
            layouter,
            assigned_vk,
            assigned_committed_instances,
            assigned_instances,
            proof,
        )?;

        self.verify_algebraic_constraints(
            layouter,
            assigned_vk,
            trace,
            assigned_committed_instances,
            assigned_instances,
            transcript,
        )
    }
}

#[cfg(test)]
pub(crate) mod tests {

    use group::Group;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, Constraints, Error, create_proof, keygen_pk, keygen_vk_with_k, prepare},
        poly::{
            PolynomialLabel,
            kzg::{KZGCommitmentScheme, commitment::KZGMultiCommitment, params::ParamsKZG},
        },
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        ecc::{
            curves::CircuitCurve,
            foreign::weierstrass_chip::{
                ForeignWeierstrassEccChip, ForeignWeierstrassEccConfig, nb_foreign_ecc_chip_columns,
            },
        },
        field::{
            NativeChip, NativeConfig, NativeGadget,
            decomposition::{
                chip::{P2RDecompositionChip, P2RDecompositionConfig},
                pow2range::Pow2RangeChip,
            },
            foreign::FieldChip,
            native::NB_EXTRA_ARITH_FIXED_COLS,
        },
        hash::poseidon::{
            NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS, PoseidonChip, PoseidonConfig,
            PoseidonState,
        },
        instructions::{
            AssignmentInstructions,
            hash::{HashCPU, HashInstructions},
        },
        testing_utils::FromScratch,
        types::{ComposableChip, Instantiable},
        verifier::{
            AssignedKZGCommitment, BlstrsEmulation, InCircuitKZG, accumulator::Accumulator,
            kzg::AssignedKZGMultiCommitment,
        },
    };

    type S = BlstrsEmulation;

    type F = <S as SelfEmulation>::F;
    type C = <S as SelfEmulation>::C;

    type E = <S as SelfEmulation>::Engine;
    type CBase = <C as CircuitCurve>::Base;

    type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    const NB_INNER_INSTANCES: usize = 1;

    #[derive(Clone, Debug, Default)]
    pub struct InnerCircuit {
        poseidon_preimage: Value<[F; 2]>,
    }

    impl InnerCircuit {
        pub fn from_witness(witness: [F; 2]) -> Self {
            Self {
                poseidon_preimage: Value::known(witness),
            }
        }
    }

    impl Circuit<F> for InnerCircuit {
        type Config = <PoseidonChip<F> as FromScratch<F>>::Config;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // A fixed column queried at two rotations, so that the inner
            // circuit has more fixed queries than fixed columns.
            let fixed_column = meta.fixed_column();
            meta.create_gate("fixed column at two rotations", |meta| {
                let cur = meta.query_fixed(fixed_column, Rotation::cur());
                let next = meta.query_fixed(fixed_column, Rotation::next());
                Constraints::without_selector(vec![cur * next])
            });

            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            PoseidonChip::configure_from_scratch(
                meta,
                &mut vec![],
                &mut vec![],
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_chip = NativeChip::new_from_scratch(&config.0);
            let poseidon_chip = PoseidonChip::new_from_scratch(&config);

            let inputs = native_chip
                .assign_many(&mut layouter, &self.poseidon_preimage.transpose_array())?;
            let output = poseidon_chip.hash(&mut layouter, &inputs)?;

            native_chip.constrain_as_public_input(&mut layouter, &output)?;

            native_chip.load_from_scratch(&mut layouter)?;
            poseidon_chip.load_from_scratch(&mut layouter)
        }
    }

    #[derive(Clone, Debug)]
    pub struct TestCircuit {
        // (cs, vk)
        inner_vk: (ConstraintSystem<F>, Value<VerifyingKey<S>>),
        inner_committed_instance: Value<C>,
        inner_instances: Value<[F; NB_INNER_INSTANCES]>,
        inner_proof: Value<Vec<u8>>,
    }

    impl Circuit<F> for TestCircuit {
        type Config = (
            NativeConfig,
            P2RDecompositionConfig,
            ForeignWeierstrassEccConfig<C>,
            PoseidonConfig<F>,
        );
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            const NB_ARITH_COLS: usize = 5;
            const NB_ARITH_FIXED_COLS: usize = NB_ARITH_COLS + NB_EXTRA_ARITH_FIXED_COLS;

            let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, C, NG>();
            let nb_fixed_cols = NB_ARITH_FIXED_COLS;

            let advice_columns: Vec<_> =
                (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
            let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();

            let native_config = NativeChip::configure(
                meta,
                &(
                    advice_columns[..NB_ARITH_COLS].to_vec(),
                    fixed_columns[..NB_ARITH_FIXED_COLS].to_vec(),
                    [committed_instance_column, instance_column],
                ),
            );

            let nb_parallel_range_checks = NB_ARITH_COLS - 1;
            let max_bit_len = 16;
            let core_decomp_config = {
                let pow2_config =
                    Pow2RangeChip::configure(meta, &advice_columns[1..=nb_parallel_range_checks]);
                P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2_config))
            };

            let base_config = FieldChip::<F, CBase, C, NG>::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            );
            let curve_config = ForeignWeierstrassEccChip::<F, C, C, NG, NG>::configure(
                meta,
                &base_config,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            );

            let poseidon_config = PoseidonChip::configure(
                meta,
                &(
                    advice_columns[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
                ),
            );

            (
                native_config,
                core_decomp_config,
                curve_config,
                poseidon_config,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
            let core_decomp_chip = P2RDecompositionChip::new(&config.1, &16);
            let native_gadget = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
            let curve_chip =
                ForeignWeierstrassEccChip::new(&config.2, &native_gadget, &native_gadget);
            let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

            let verifier_chip =
                VerifierGadget::<S>::new(&curve_chip, &native_gadget, &poseidon_chip);

            let assigned_inner_vk: AssignedVk<S, InCircuitKZG<S>> = verifier_chip
                .assign_vk_as_public_input(
                    &mut layouter,
                    self.inner_vk.1.as_ref(),
                    &self.inner_vk.0,
                )?;

            let assigned_committed_instance =
                AssignedKZGMultiCommitment(vec![AssignedKZGCommitment::assign(
                    &mut layouter,
                    &curve_chip,
                    self.inner_committed_instance,
                    PolynomialLabel::CommittedInstance(0),
                )?]);

            let assigned_inner_pi = native_gadget
                .assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

            let mut inner_proof_acc = verifier_chip.prepare(
                &mut layouter,
                &assigned_inner_vk,
                &[assigned_committed_instance],
                &[&assigned_inner_pi],
                self.inner_proof.clone(),
            )?;

            inner_proof_acc.collapse(&mut layouter, &curve_chip, &native_gadget)?;

            verifier_chip.constrain_as_public_input(&mut layouter, &inner_proof_acc)?;

            core_decomp_chip.load(&mut layouter)
        }
    }

    #[test]
    fn test_verify_proof() {
        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

        let inner_k = 10;
        let inner_params = ParamsKZG::unsafe_setup(inner_k, &mut rng);

        let inner_vk = keygen_vk_with_k(&inner_params, &InnerCircuit::default(), inner_k).unwrap();
        let inner_pk = keygen_pk(inner_vk.clone(), &InnerCircuit::default()).unwrap();

        let preimage = [F::random(&mut rng), F::random(&mut rng)];
        let output = <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage);
        let inner_public_inputs = vec![output];

        let inner_proof = {
            let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
            create_proof::<
                F,
                KZGCommitmentScheme<E>,
                CircuitTranscript<PoseidonState<F>>,
                InnerCircuit,
            >(
                &inner_params,
                &inner_pk,
                &InnerCircuit::from_witness(preimage),
                1,
                &[&[], &inner_public_inputs],
                &mut transcript,
                &mut rng,
            )
            .unwrap_or_else(|_| panic!("Problem creating the inner proof"));
            transcript.finalize()
        };

        let inner_dual_msm = {
            let mut transcript =
                CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&inner_proof);
            prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                &inner_vk,
                &[KZGMultiCommitment::commitment_to_zero(
                    PolynomialLabel::CommittedInstance(0),
                )],
                &[&inner_public_inputs],
                &mut transcript,
            )
            .expect("Problem preparing the inner proof")
        };

        let fixed_bases = crate::verifier::fixed_bases::<S>(&inner_vk);

        let mut inner_acc = Accumulator::<S>::from_dual_msm(inner_dual_msm.clone(), &fixed_bases);

        let inner_verifier_params = inner_params.verifier_params();
        assert!(inner_dual_msm.check(&inner_verifier_params));
        assert!(inner_acc.check(&inner_verifier_params, &fixed_bases));

        inner_acc.collapse();

        // The inner proof is ready.
        // Now, let us make a proof that we know an inner proof.

        let mut public_inputs = AssignedVk::<S, InCircuitKZG<S>>::as_public_input(&inner_vk);
        public_inputs.extend(AssignedAccumulator::as_public_input(&inner_acc));

        let circuit = TestCircuit {
            inner_vk: (inner_vk.cs().clone(), Value::known(inner_vk.clone())),
            inner_committed_instance: Value::known(C::identity()),
            inner_instances: Value::known([output]),
            inner_proof: Value::known(inner_proof),
        };

        let prover =
            MockProver::run(&circuit, vec![vec![], public_inputs]).expect("MockProver failed");
        prover.assert_satisfied();
    }
}
