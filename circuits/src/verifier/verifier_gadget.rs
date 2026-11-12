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
use std::{collections::BTreeMap, fmt::Debug, iter, marker::PhantomData};

use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::{EvaluationDomain, PolynomialLabel, Rotation},
    transcript::Hashable,
};

use crate::{
    CircuitField,
    field::AssignedNative,
    instructions::{
        ArithInstructions, PublicInputInstructions, assignments::AssignmentInstructions,
    },
    verifier::{
        AssignedEvaluationDomain, AssignedVk, ScalarChip, VerifyingKey, argument,
        expressions::{
            eval_expression, lookup::lookup_expressions, permutation::permutation_expressions,
            trash::trash_expressions,
        },
        pcs::{AssignedCommitment, InCircuitPCS, VerifierQuery},
        traces::VerifierTrace,
        transcript_gadget::InCircuitTranscript,
        utils::{
            evaluate_lagrange_polynomials, inner_product, mul_add, pow_of_two, square_k_times, sum,
        },
    },
};

mod unbound_vk;

pub use unbound_vk::{UnboundVk, vk_hash};

/// A gadget for in-circuit verification of proofs committed with `PCS`.
#[derive(Clone, Debug)]
#[doc(hidden)] // A bug in rustc prevents us from documenting the verifier gadget.
pub struct VerifierGadget<F: CircuitField, PCS: InCircuitPCS<F>> {
    commitment_chip: PCS::CommitmentChip,
    scalar_chip: ScalarChip<F>,
    _pcs: PhantomData<PCS>,
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> Chip<F> for VerifierGadget<F, PCS> {
    type Config = ();
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &()
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> VerifierGadget<F, PCS> {
    /// Creates a new verifier gadget from its underlying components.
    pub fn new(commitment_chip: &PCS::CommitmentChip, scalar_chip: &ScalarChip<F>) -> Self {
        Self {
            commitment_chip: commitment_chip.clone(),
            scalar_chip: scalar_chip.clone(),
            _pcs: PhantomData,
        }
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> PublicInputInstructions<F, AssignedVk<F, PCS>>
    for VerifierGadget<F, PCS>
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned_vk: &AssignedVk<F, PCS>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok([
            self.scalar_chip.as_public_input(layouter, &assigned_vk.transcript_repr)?,
            self.scalar_chip.as_public_input(layouter, assigned_vk.k())?,
            self.scalar_chip.as_public_input(layouter, assigned_vk.omega())?,
        ]
        .concat())
    }

    fn constrain_as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        _assigned_vk: &AssignedVk<F, PCS>,
    ) -> Result<(), Error> {
        unimplemented!(
            "We intend [assign_vk_as_public_input] to be the only entry point
             for assigned verifying keys."
        )
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> VerifierGadget<F, PCS> {
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
    pub fn assign_vk_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        vk: Value<&VerifyingKey<F, PCS>>,
        cs: &ConstraintSystem<F>,
    ) -> Result<AssignedVk<F, PCS>, Error> {
        let [transcript_repr_value, k_value, omega_value] = vk
            .map(|vk| {
                let domain = vk.get_domain();
                [
                    vk.transcript_repr(),
                    F::from(domain.k() as u64),
                    domain.get_omega(),
                ]
            })
            .transpose_array();

        let transcript_repr = self.scalar_chip.assign(layouter, transcript_repr_value)?;
        let k = self.scalar_chip.assign(layouter, k_value)?;
        let omega = self.scalar_chip.assign(layouter, omega_value)?;

        self.scalar_chip.constrain_as_public_input(layouter, &transcript_repr)?;
        self.scalar_chip.constrain_as_public_input(layouter, &k)?;
        self.scalar_chip.constrain_as_public_input(layouter, &omega)?;

        let domain = self.derive_domain(layouter, k, omega)?;

        self.assemble_vk(cs, domain, transcript_repr)
    }

    /// Assigns a verifying key as a constant. All the necessary information is
    /// available off-circuit, except for the `transcript_repr` and the
    /// evaluation domain, which are "assigned fixed".
    ///
    /// `cs` must be finalized, i.e. its selectors must have been converted to
    /// fixed columns, as in the constraint system of a verifying key.
    pub fn assign_fixed_vk(
        &self,
        layouter: &mut impl Layouter<F>,
        domain: &EvaluationDomain<F>,
        cs: &ConstraintSystem<F>,
        transcript_repr_constant: F,
    ) -> Result<AssignedVk<F, PCS>, Error> {
        let transcript_repr = self.scalar_chip.assign_fixed(layouter, transcript_repr_constant)?;
        let k = self.scalar_chip.assign_fixed(layouter, F::from(domain.k() as u64))?;
        let omega = self.scalar_chip.assign_fixed(layouter, domain.get_omega())?;
        let domain = self.derive_domain(layouter, k, omega)?;
        self.assemble_vk(cs, domain, transcript_repr)
    }

    /// Completes the assigned domain by deriving `omega_inv` and `n = 2^k` from
    /// assigned `k` and `omega` cells (in-circuit).
    pub(super) fn derive_domain(
        &self,
        layouter: &mut impl Layouter<F>,
        k: AssignedNative<F>,
        omega: AssignedNative<F>,
    ) -> Result<AssignedEvaluationDomain<F>, Error> {
        let omega_inv = self.scalar_chip.inv(layouter, &omega)?;
        let n = pow_of_two(layouter, &self.scalar_chip, &k)?;
        Ok(AssignedEvaluationDomain {
            k,
            omega,
            omega_inv,
            n,
        })
    }

    /// Builds the `AssignedVk`.
    pub(super) fn assemble_vk(
        &self,
        cs: &ConstraintSystem<F>,
        domain: AssignedEvaluationDomain<F>,
        transcript_repr: AssignedNative<F>,
    ) -> Result<AssignedVk<F, PCS>, Error> {
        if cs.num_selectors() > 0 {
            return Err(Error::Synthesis(
                "the constraint system has selectors, it must be finalized".into(),
            ));
        }

        Ok(AssignedVk {
            domain,
            phase0_commitment: PCS::fixed_commitment(&cs.fixed_polys_labels()),
            cs_degree: cs.degree(),
            cs: cs.clone(),
            transcript_repr,
        })
    }
}

impl<F: CircuitField, PCS: InCircuitPCS<F>> VerifierGadget<F, PCS> {
    /// Given a transcript initialised with a plonk proof (see
    /// [InCircuitTranscript::init_with_proof]), this function parses the proof
    /// to extract the verifying trace.
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
    pub fn parse_trace<T>(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned_vk: &AssignedVk<F, PCS>,
        assigned_committed_instances: &[AssignedCommitment<F, PCS>],
        assigned_instances: &[&[AssignedNative<F>]],
        transcript: &mut T,
    ) -> Result<VerifierTrace<F, PCS>, Error>
    where
        F: Hashable<T::Hash>,
        PCS::Commitment: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
        let cs = &assigned_vk.cs;

        // Check that instances matches the expected number of instance columns
        assert_eq!(
            cs.num_instance_columns(),
            assigned_committed_instances.len() + assigned_instances.len()
        );

        // Hash verification key into transcript.
        let vk_absorbed = assigned_vk.absorb_into(layouter, &self.scalar_chip, transcript)?;
        let phase0_committed = argument::committed_from_key(&vk_absorbed);

        (assigned_committed_instances.iter())
            .try_for_each(|com| transcript.common(layouter, &self.commitment_chip, com))?;

        for instance in assigned_instances {
            let n: AssignedNative<F> =
                self.scalar_chip.assign_fixed(layouter, (instance.len() as u64).into())?;
            transcript.common(layouter, &self.scalar_chip, &n)?;
            (instance.iter())
                .try_for_each(|pi| transcript.common(layouter, &self.scalar_chip, pi))?;
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

        let phase1_committed =
            argument::read_committed(layouter, &self.commitment_chip, &phase1_labels, transcript)?;

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

        let phase2_committed =
            argument::read_committed(layouter, &self.commitment_chip, &phase2_labels, transcript)?;

        // Sample y challenge, which keeps the gates linearly independent
        let y = transcript.squeeze_challenge(layouter)?;

        Ok(VerifierTrace {
            phase0_committed,
            phase1_committed,
            phase2_committed,
            beta,
            gamma,
            theta,
            trash_challenge,
            y,
        })
    }

    /// Given a [VerifierTrace], this function computes the opening challenge,
    /// x, and proceeds to verify the algebraic constraints with the claimed
    /// evaluations. This function does not verify the PCS proof.
    ///
    /// The proof is considered to be valid if the resulting accumulator
    /// satisfies the [invariant](crate::verifier::Accumulator::check)
    /// with respect to the relevant `tau_in_g2`.
    pub fn verify_algebraic_constraints<T>(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned_vk: &AssignedVk<F, PCS>,
        trace: VerifierTrace<F, PCS>,
        assigned_committed_instances: &[AssignedCommitment<F, PCS>],
        assigned_instances: &[&[AssignedNative<F>]],
        transcript: &mut T,
    ) -> Result<PCS::AssignedVerificationGuard, Error>
    where
        F: Hashable<T::Hash>,
        PCS::Commitment: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
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

        // Read the commitment to the quotient polynomial h(X) = nu(X)/(X^n-1) from
        // the transcript. The prover splits h(X) into `quotient_poly_degree + 1`
        // limbs, where `quotient_poly_degree = cs_degree - 1`, committed to as one
        // group.
        let quotient_labels: Vec<_> =
            (0..assigned_vk.cs_degree).map(PolynomialLabel::QuotientPiece).collect();
        let quotient_committed = argument::read_committed(
            layouter,
            &self.commitment_chip,
            &quotient_labels,
            transcript,
        )?;

        // Sample x challenge, which is used to ensure the circuit is satisfied with
        // high probability
        let x = <PCS as InCircuitPCS<F>>::squeeze_evaluation_point(
            layouter,
            &self.scalar_chip,
            transcript,
        )?;

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
                        transcript.read(layouter, &self.scalar_chip, &())
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
        for rotation in argument::rotations::<F>(cs) {
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
            phase0_committed.evaluate(layouter, &self.scalar_chip, cs, &x_rotations, transcript)?;
        let phase1_evaluated =
            phase1_committed.evaluate(layouter, &self.scalar_chip, cs, &x_rotations, transcript)?;
        let phase2_evaluated =
            phase2_committed.evaluate(layouter, &self.scalar_chip, cs, &x_rotations, transcript)?;
        let mut quotient_evaluated = quotient_committed.evaluate(
            layouter,
            &self.scalar_chip,
            cs,
            &x_rotations,
            transcript,
        )?;

        let phase0_evals = &phase0_evaluated.evals_map;
        let phase1_evals = &phase1_evaluated.evals_map;
        let phase2_evals = &phase2_evaluated.evals_map;

        // The advice evaluations in the order of `cs.advice_queries`, which is how
        // the identities index them. In the phase1 group, each column's follow the
        // order of its queries.
        let mut next = vec![0; cs.num_advice_columns()];
        let advice_evals: Vec<AssignedNative<F>> = cs
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
        let fixed_evals: Vec<AssignedNative<F>> = cs
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
        let l_blind = sum::<F>(
            layouter,
            &self.scalar_chip,
            &l_evals[1..=nr_blinding_factors],
        )?;
        let l_0 = l_evals[1 + nr_blinding_factors].clone();

        let mut expressions = Vec::new();
        // Evaluate polys from (custom) gates
        for gate in cs.gates().iter() {
            for poly in gate.polynomials().iter() {
                let eval = eval_expression::<F>(
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

        let x_squared = self.scalar_chip.mul(layouter, &x, &x, None)?;
        let splitting_factor = self.scalar_chip.div(layouter, &xn, &x_squared)?;

        // -nu(x): the identities batched with y by Horner's rule, negated.
        let zero: AssignedNative<F> = self.scalar_chip.assign_fixed(layouter, F::ZERO)?;
        let neg_nu_eval = expressions.iter().try_fold(zero, |acc, id| {
            self.scalar_chip.add_and_mul(
                layouter,
                (F::ZERO, &acc),
                (F::ZERO, &y),
                (-F::ONE, id),
                F::ZERO,
                F::ONE,
            ) // acc * y - id
        })?;

        // h_0(x) is derived from -nu(x) = (1 - x^n) h(x), for
        // h(x) = h_0(x) + x^{n-2} h_1(x) + ..., so that opening h_0 at it checks
        // the identities.
        let higher_limbs = {
            let mut limb_evals =
                quotient_evaluated.evals_map.values().skip(1).rev().map(|e| e[0].eval());
            let last = limb_evals.next().expect("a quotient limb h_1").clone();
            let horner = limb_evals.try_fold(last, |acc, eval| {
                mul_add(layouter, &self.scalar_chip, &acc, &splitting_factor, eval)
            })?;
            self.scalar_chip.mul(layouter, &horner, &splitting_factor, None)?
        };
        let one_minus_xn =
            self.scalar_chip.linear_combination(layouter, &[(-F::ONE, xn)], F::ONE)?;
        let h_eval = self.scalar_chip.div(layouter, &neg_nu_eval, &one_minus_xn)?;
        let h0_eval = self.scalar_chip.sub(layouter, &h_eval, &higher_limbs)?;
        quotient_evaluated.insert(PolynomialLabel::QuotientPiece(0), x.clone(), h0_eval);

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
                        Some(VerifierQuery::new(
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
            .chain(quotient_evaluated.queries())
            .collect::<Vec<_>>();

        // We are now convinced the circuit is satisfied so long as the
        // polynomial commitments open to the correct values, which is true as long
        // as the following accumulator passes the invariant.
        <PCS as InCircuitPCS<F>>::multi_prepare(
            layouter,
            &self.commitment_chip,
            &self.scalar_chip,
            &queries,
            transcript,
        )
    }

    /// Prepares a plonk proof, with which `transcript` must have been
    /// initialised (see [InCircuitTranscript::init_with_proof]), into a PCS
    /// instance that can be finalized or batched. It is responsibility of the
    /// verifier to check the validity of the instance columns. It is the
    /// in-circuit analog of "prepare" from midnight-proofs at
    /// src/plonk/verifier.rs.
    ///
    /// The proof is considered to be valid if the resulting accumulator
    /// satisfies the [invariant](crate::verifier::Accumulator::check)
    /// with respect to the relevant `tau_in_g2`.
    pub fn prepare<T>(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned_vk: &AssignedVk<F, PCS>,
        assigned_committed_instances: &[AssignedCommitment<F, PCS>],
        assigned_instances: &[&[AssignedNative<F>]],
        transcript: &mut T,
    ) -> Result<PCS::AssignedVerificationGuard, Error>
    where
        F: Hashable<T::Hash>,
        PCS::Commitment: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
        let trace = self.parse_trace(
            layouter,
            assigned_vk,
            assigned_committed_instances,
            assigned_instances,
            transcript,
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

    use ff::Field;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, Constraints, Error, create_proof, keygen_pk, keygen_vk_with_k, prepare},
        poly::{
            commitment::PolynomialCommitmentScheme,
            fflonk::Fflonk,
            kzg::{KZGCommitmentScheme, msm::DualMSM, params::ParamsVerifierKZG},
        },
        transcript::{CircuitTranscript, Hashable, Transcript},
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
            CommitmentBases, CurveChip, PoseidonTranscriptGadget,
            accumulator::{Accumulator, AssignedAccumulator},
        },
    };

    type E = midnight_curves::Bls12;
    type F = midnight_curves::Fq;
    type C = midnight_curves::G1Projective;
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
    pub struct TestCircuit<P: InCircuitPCS<F> + PolynomialCommitmentScheme<F>> {
        // (cs, vk)
        inner_vk: (ConstraintSystem<F>, Value<VerifyingKey<F, P>>),
        inner_instances: Value<[F; NB_INNER_INSTANCES]>,
        inner_proof: Value<Vec<u8>>,
    }

    impl<
        P: InCircuitPCS<
                F,
                CommitmentChip = CurveChip<E>,
                AssignedVerificationGuard = AssignedAccumulator<E>,
            > + PolynomialCommitmentScheme<F, Commitment: Hashable<PoseidonState<F>>>,
    > Circuit<F> for TestCircuit<P>
    {
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
                &fixed_columns,
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

            let verifier_chip = VerifierGadget::<F, P>::new(&curve_chip, &native_gadget);

            let assigned_inner_vk: AssignedVk<F, P> = verifier_chip.assign_vk_as_public_input(
                &mut layouter,
                self.inner_vk.1.as_ref(),
                &self.inner_vk.0,
            )?;

            let assigned_inner_pi = native_gadget
                .assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

            let mut transcript = PoseidonTranscriptGadget::<F>::new(&poseidon_chip);
            transcript.init_with_proof(&mut layouter, self.inner_proof.clone())?;
            let mut inner_proof_acc = verifier_chip.prepare(
                &mut layouter,
                &assigned_inner_vk,
                &[],
                &[&[], &assigned_inner_pi],
                &mut transcript,
            )?;

            inner_proof_acc.collapse(&mut layouter, &curve_chip, &native_gadget)?;

            inner_proof_acc.constrain_as_public_input(
                &mut layouter,
                &curve_chip,
                &native_gadget,
            )?;

            core_decomp_chip.load(&mut layouter)
        }
    }

    #[test]
    fn test_verify_proof() {
        check_verify_proof::<KZGCommitmentScheme<midnight_curves::Bls12>>();
    }

    #[test]
    fn test_verify_proof_fflonk() {
        check_verify_proof::<Fflonk<KZGCommitmentScheme<midnight_curves::Bls12>, 2>>();
    }

    /// Makes an inner proof with the off-circuit scheme `P`, verifies it
    /// in-circuit, and checks the circuit with the mock prover.
    fn check_verify_proof<P>()
    where
        P: InCircuitPCS<
                F,
                CommitmentChip = CurveChip<E>,
                AssignedVerificationGuard = AssignedAccumulator<E>,
            > + PolynomialCommitmentScheme<
                F,
                VerifierParameters = ParamsVerifierKZG<midnight_curves::Bls12>,
                VerificationGuard = DualMSM<midnight_curves::Bls12>,
                Commitment: Hashable<PoseidonState<F>> + CommitmentBases<C>,
            >,
    {
        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

        let inner_k = 10;
        let inner_params = P::gen_params(inner_k);

        let inner_vk = keygen_vk_with_k(&inner_params, &InnerCircuit::default(), inner_k).unwrap();
        let inner_pk = keygen_pk(inner_vk.clone(), &InnerCircuit::default()).unwrap();

        let preimage = [F::random(&mut rng), F::random(&mut rng)];
        let output = <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage);
        let inner_public_inputs = vec![output];

        let inner_proof = {
            let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
            create_proof::<F, P, CircuitTranscript<PoseidonState<F>>, InnerCircuit>(
                &inner_params,
                &inner_pk,
                &InnerCircuit::from_witness(preimage),
                0,
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
            prepare::<F, P, CircuitTranscript<PoseidonState<F>>>(
                &inner_vk,
                &[],
                &[&[], &inner_public_inputs],
                &mut transcript,
            )
            .expect("Problem preparing the inner proof")
        };

        let fixed_bases = crate::verifier::fixed_bases::<E, P>(&inner_vk);
        assert_eq!(
            crate::verifier::fixed_base_labels::<F, P>(inner_vk.cs()),
            fixed_bases.keys().cloned().collect::<Vec<_>>()
        );

        let mut inner_acc = Accumulator::<E>::from_dual_msm(inner_dual_msm.clone(), &fixed_bases);

        let inner_verifier_params = P::get_verifier_params(&inner_params);
        assert!(inner_dual_msm.check(&inner_verifier_params));
        assert!(inner_acc.check(&inner_verifier_params, &fixed_bases));

        inner_acc.collapse();

        // The inner proof is ready.
        // Now, let us make a proof that we know an inner proof.

        let mut public_inputs = AssignedVk::<F, P>::as_public_input(&inner_vk);
        public_inputs.extend(AssignedAccumulator::as_public_input(&inner_acc));

        let circuit = TestCircuit::<P> {
            inner_vk: (inner_vk.cs().clone(), Value::known(inner_vk.clone())),
            inner_instances: Value::known([output]),
            inner_proof: Value::known(inner_proof),
        };

        let prover =
            MockProver::run(&circuit, vec![vec![], public_inputs]).expect("MockProver failed");
        prover.assert_satisfied();
    }
}
