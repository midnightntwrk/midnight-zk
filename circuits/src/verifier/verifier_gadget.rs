// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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
//! We assume vk.cs.num_challenges = 1 (i.e. vk.cs.phases() is empty),
//! although there is no fundamental reason why this could not be generalized.
//!
//! We assume the CS of the verified circuit defines exactly one instance
//! column. (This is the norm throughout our whole codebase anyway.)

use std::{fmt::Debug, iter};

use ff::Field;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::{EvaluationDomain, Rotation},
};

use crate::{
    field::AssignedNative,
    instructions::{
        assignments::AssignmentInstructions, ArithInstructions, PublicInputInstructions,
    },
    verifier::{
        expressions::{
            eval_expression, lookup::lookup_expressions, permutation::permutation_expressions,
            trash::trash_expressions,
        },
        kzg::{self, VerifierQuery},
        lookup,
        permutation::{self, evaluate_permutation_common},
        transcript_gadget::TranscriptGadget,
        trash,
        utils::{evaluate_lagrange_polynomials, inner_product, sum, AssignedBoundedScalar},
        vanishing, Accumulator, AssignedAccumulator, AssignedVk, SelfEmulation, VerifyingKey,
    },
};

/// A gadget for KZG-based in-circuit proof verification.
#[derive(Clone, Debug)]
#[doc(hidden)] // A bug in rustc prevents us from documenting the verifier gadget.
pub struct VerifierGadget<S: SelfEmulation> {
    curve_chip: S::CurveChip,
    scalar_chip: S::ScalarChip,
    sponge_chip: S::SpongeChip,
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

impl<S: SelfEmulation> PublicInputInstructions<S::F, AssignedVk<S>> for VerifierGadget<S> {
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S>,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        self.scalar_chip
            .as_public_input(layouter, &assigned_vk.transcript_repr)
    }

    fn constrain_as_public_input(
        &self,
        _layouter: &mut impl Layouter<S::F>,
        _assigned_vk: &AssignedVk<S>,
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
    ) -> Result<AssignedVk<S>, Error> {
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
            (assigned.lhs).in_circuit_as_public_input(layouter, &self.curve_chip)?,
            (assigned.rhs).in_circuit_as_public_input(layouter, &self.curve_chip)?,
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
}

impl<S: SelfEmulation> VerifierGadget<S> {
    /// Assigns a verifying key as a public input. All the necessary information
    /// is required off-circuit, except for the `transcript_repr` value.
    pub fn assign_vk_as_public_input(
        &self,
        layouter: &mut impl Layouter<S::F>,
        vk_name: &str,
        domain: &EvaluationDomain<S::F>,
        cs: &ConstraintSystem<S::F>,
        transcript_repr_value: Value<S::F>,
    ) -> Result<AssignedVk<S>, Error> {
        let transcript_repr: AssignedNative<S::F> = self
            .scalar_chip
            .assign_as_public_input(layouter, transcript_repr_value)?;

        // We expect a finalized cs with no selectors, i.e. whose selectors have been
        // converted into fixed columns.
        let selectors = vec![vec![false]; cs.num_selectors()];
        let (processed_cs, _) = cs.clone().directly_convert_selectors_to_fixed(selectors);

        let assigned_vk = AssignedVk {
            vk_name: vk_name.to_string(),
            domain: domain.clone(),
            cs: processed_cs,
            transcript_repr,
        };

        Ok(assigned_vk)
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
    pub fn parse_trace(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S>,
        assigned_committed_instances: &[(&str, S::AssignedPoint)], // (name, com)
        assigned_instances: &[&[AssignedNative<S::F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<(super::traces::VerifierTrace<S>, TranscriptGadget<S>), Error> {
        let cs = &assigned_vk.cs;

        // Check that instances matches the expected number of instance columns
        assert_eq!(
            cs.num_instance_columns(),
            assigned_committed_instances.len() + assigned_instances.len()
        );

        let mut transcript =
            TranscriptGadget::new(&self.scalar_chip, &self.curve_chip, &self.sponge_chip);

        transcript.init_with_proof(layouter, proof)?;

        // Hash verification key into transcript
        transcript.common_scalar(layouter, &assigned_vk.transcript_repr)?;

        assigned_committed_instances
            .iter()
            .try_for_each(|(_, com)| transcript.common_point(layouter, com))?;

        for instance in assigned_instances {
            let n = (self.scalar_chip).assign_fixed(layouter, (instance.len() as u64).into())?;
            transcript.common_scalar(layouter, &n)?;
            (instance.iter()).try_for_each(|pi| transcript.common_scalar(layouter, pi))?;
        }

        // Assert that we only have one phase.
        // TODO: get rid of this assumption, we could support more than one phase.
        assert_eq!(cs.phases().count(), 1);

        // Hash the prover's advice commitments into the transcript and squeeze
        // challenges
        let advice_commitments = (0..cs.num_advice_columns())
            .map(|_| transcript.read_point(layouter))
            .collect::<Result<Vec<_>, Error>>()?;

        // Sample theta challenge for keeping lookup columns linearly independent
        let theta = transcript.squeeze_challenge(layouter)?;

        let lookups_permuted = cs
            .lookups()
            .iter()
            .map(|_| lookup::read_permuted_commitments(layouter, &mut transcript))
            .collect::<Result<Vec<_>, Error>>()?;

        let beta = transcript.squeeze_challenge(layouter)?;
        let gamma = transcript.squeeze_challenge(layouter)?;

        let permutation_committed =
            // Hash each permutation product commitment
            permutation::read_product_commitments(layouter, &mut transcript, cs)?;

        let lookups_committed = lookups_permuted
            .into_iter()
            .map(|lookup|
                // Hash each lookup product commitment
                lookup.read_product_commitment(layouter, &mut transcript))
            .collect::<Result<Vec<_>, _>>()?;

        let trash_challenge = transcript.squeeze_challenge(layouter)?;

        let trashcans_committed = cs
            .trashcans()
            .iter()
            .map(|_| trash::read_committed(layouter, &mut transcript))
            .collect::<Result<Vec<_>, _>>()?;

        let vanishing = vanishing::read_commitments_before_y(layouter, &mut transcript)?;

        // Sample y challenge, which keeps the gates linearly independent
        let y = transcript.squeeze_challenge(layouter)?;

        Ok((
            super::traces::VerifierTrace {
                advice_commitments,
                vanishing,
                lookups: lookups_committed,
                trashcans: trashcans_committed,
                permutations: permutation_committed,
                beta,
                gamma,
                theta,
                trash_challenge,
                y,
            },
            transcript,
        ))
    }

    /// Given a [super::traces::VerifierTrace], this function computes the
    /// opening challenge, x, and proceeds to verify the algebraic constraints
    /// with the claimed evaluations. This function does not verify the PCS
    /// proof.
    ///
    /// The proof is considered to be valid if the resulting accumulator
    /// satisfies the [invariant](crate::verifier::Accumulator::check)
    /// with respect to the relevant `tau_in_g2`.
    pub fn verify_algebraic_constraints(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S>,
        trace: super::traces::VerifierTrace<S>,
        assigned_committed_instances: &[(&str, S::AssignedPoint)], // (name, com)
        assigned_instances: &[&[AssignedNative<S::F>]],
        mut transcript: TranscriptGadget<S>,
    ) -> Result<AssignedAccumulator<S>, Error> {
        let cs = &assigned_vk.cs;
        let k = assigned_vk.domain.k();
        let nb_committed_instances = assigned_committed_instances.len();

        let super::traces::VerifierTrace {
            advice_commitments,
            vanishing,
            lookups,
            trashcans,
            permutations,
            beta,
            gamma,
            theta,
            trash_challenge,
            y,
        } = trace;

        let vanishing = vanishing.read_commitment_after_y(
            layouter,
            &mut transcript,
            assigned_vk.domain.get_quotient_poly_degree(),
        )?;

        // Sample x challenge, which is used to ensure the circuit is satisfied with
        // high probability
        let x = transcript.squeeze_challenge(layouter)?;
        let xn = ArithInstructions::pow(&self.scalar_chip, layouter, &x, 1 << k)?;

        let instance_evals = {
            let instance_queries = cs.instance_queries();
            let min_rotation = instance_queries.iter().map(|(_, rot)| rot.0).min().unwrap();
            let max_rotation = instance_queries.iter().map(|(_, rot)| rot.0).max().unwrap();

            let max_instance_len = assigned_instances
                .iter()
                .map(|instance| instance.len())
                .max()
                .unwrap_or(0);

            let l_i_s = evaluate_lagrange_polynomials(
                layouter,
                &self.scalar_chip,
                1 << k,
                assigned_vk.domain.get_omega(),
                (-max_rotation)..(max_instance_len as i32 + min_rotation.abs()),
                &x,
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

        let advice_evals = (0..cs.advice_queries().len())
            .map(|_| transcript.read_scalar(layouter))
            .collect::<Result<Vec<_>, _>>()?;

        let fixed_evals = (0..cs.fixed_queries().len())
            .map(|_| transcript.read_scalar(layouter))
            .collect::<Result<Vec<_>, _>>()?;

        let vanishing = vanishing.evaluate_after_x(layouter, &mut transcript)?;

        let permutations_common =
            evaluate_permutation_common(layouter, &mut transcript, cs.permutation().columns.len())?;

        let permutations_evaluated = permutations.evaluate(layouter, &mut transcript)?;

        let lookups_evaluated = lookups
            .into_iter()
            .map(|lookup| lookup.evaluate(layouter, &mut transcript))
            .collect::<Result<Vec<_>, Error>>()?;

        let trashcans_evaluated = trashcans
            .into_iter()
            .map(|trash| trash.evaluate(layouter, &mut transcript))
            .collect::<Result<Vec<_>, Error>>()?;

        // This check ensures the circuit is satisfied so long as the polynomial
        // commitments open to the correct values.
        let vanishing = {
            let blinding_factors = cs.blinding_factors();

            let l_evals = evaluate_lagrange_polynomials(
                layouter,
                &self.scalar_chip,
                1 << k,
                assigned_vk.domain.get_omega(),
                (-((blinding_factors + 1) as i32))..1,
                &x,
            )?;
            assert_eq!(l_evals.len(), 2 + blinding_factors);
            let l_last = l_evals[0].clone();
            let l_blind = sum::<S::F>(layouter, &self.scalar_chip, &l_evals[1..=blinding_factors])?;
            let l_0 = l_evals[1 + blinding_factors].clone();

            // Compute the expected value of h(x)
            let expressions = {
                let evaluated_gate_ids = {
                    let mut ids = vec![];
                    for gate in cs.gates().iter() {
                        for poly in gate.polynomials().iter() {
                            ids.push(eval_expression::<S>(
                                layouter,
                                &self.scalar_chip,
                                &advice_evals,
                                &fixed_evals,
                                &instance_evals,
                                poly,
                            )?)
                        }
                    }
                    ids
                };
                let evaluated_perm_ids = permutation_expressions(
                    layouter,
                    &self.scalar_chip,
                    cs,
                    &permutations_evaluated,
                    &permutations_common,
                    &advice_evals,
                    &fixed_evals,
                    &instance_evals,
                    &l_0,
                    &l_last,
                    &l_blind,
                    &beta,
                    &gamma,
                    &x,
                )?;

                let evaluated_lookup_ids = cs
                    .lookups()
                    .iter()
                    .enumerate()
                    .map(|(index, _)| {
                        lookup_expressions(
                            layouter,
                            &self.scalar_chip,
                            &lookups_evaluated[index],
                            cs.lookups()[index].input_expressions(),
                            cs.lookups()[index].table_expressions(),
                            &advice_evals,
                            &fixed_evals,
                            &instance_evals,
                            &l_0,
                            &l_last,
                            &l_blind,
                            &theta,
                            &beta,
                            &gamma,
                        )
                    })
                    .collect::<Result<Vec<Vec<_>>, Error>>()?
                    .concat();

                let evaluated_trashcan_ids = cs
                    .trashcans()
                    .iter()
                    .enumerate()
                    .map(|(index, _)| {
                        trash_expressions(
                            layouter,
                            &self.scalar_chip,
                            &trashcans_evaluated[index],
                            cs.trashcans()[index].selector(),
                            cs.trashcans()[index].constraint_expressions(),
                            &advice_evals,
                            &fixed_evals,
                            &instance_evals,
                            &trash_challenge,
                        )
                    })
                    .collect::<Result<Vec<Vec<_>>, Error>>()?
                    .concat();

                std::iter::empty()
                    // Evaluate the circuit using the custom gates provided
                    .chain(evaluated_gate_ids)
                    .chain(evaluated_perm_ids)
                    .chain(evaluated_lookup_ids)
                    .chain(evaluated_trashcan_ids)
                    .collect::<Vec<_>>()
            };

            vanishing.verify(layouter, &self.scalar_chip, &expressions, &y, &xn)
        }?;

        let one = AssignedBoundedScalar::<S::F>::one(layouter, &self.scalar_chip)?;
        let omega = assigned_vk.domain.get_omega();
        let omega_inv = omega.invert().unwrap();
        let omega_last = omega_inv.pow([cs.blinding_factors() as u64 + 1]);
        let x_next = self.scalar_chip.mul_by_constant(layouter, &x, omega)?;
        let x_prev = self.scalar_chip.mul_by_constant(layouter, &x, omega_inv)?;
        let x_last = self.scalar_chip.mul_by_constant(layouter, &x, omega_last)?;

        // Gets the evaluation point for a query at the given rotation.
        let get_point = |rotation: &Rotation| -> &AssignedNative<S::F> {
            match rotation.0 {
                -1 => &x_prev,
                0 => &x,
                1 => &x_next,
                _ => panic!("We do not support other rotations"),
            }
        };

        let queries =
            iter::empty()
                .chain(cs.instance_queries().iter().enumerate().filter_map(
                    |(query_index, &(column, rot))| {
                        if column.index() < nb_committed_instances {
                            Some(VerifierQuery::<S>::new_fixed(
                                &one,
                                get_point(&rot),
                                assigned_committed_instances[column.index()].0,
                                &instance_evals[query_index],
                            ))
                        } else {
                            None
                        }
                    },
                ))
                .chain(cs.advice_queries().iter().enumerate().map(
                    |(query_index, &(column, rot))| {
                        VerifierQuery::<S>::new(
                            &one,
                            get_point(&rot),
                            &advice_commitments[column.index()],
                            &advice_evals[query_index],
                        )
                    },
                ))
                .chain((permutations_evaluated).queries(&one, &x, &x_next, &x_last))
                .chain(
                    (lookups_evaluated.iter())
                        .flat_map(|lookup| lookup.queries(&one, &x, &x_next, &x_prev)),
                )
                .chain((trashcans_evaluated.iter()).flat_map(|trash| trash.queries(&one, &x)))
                .chain(
                    cs.fixed_queries()
                        .iter()
                        .enumerate()
                        .map(|(query_index, &(col, rot))| {
                            VerifierQuery::new_fixed(
                                &one,
                                get_point(&rot),
                                &assigned_vk.fixed_commitment_name(col.index()),
                                &fixed_evals[query_index],
                            )
                        }),
                )
                .chain(
                    permutations_common.queries(
                        &(0..cs.permutation().columns.len())
                            .map(|i| assigned_vk.perm_commitment_name(i))
                            .collect::<Vec<_>>(),
                        &one,
                        &x,
                    ),
                )
                .chain(vanishing.queries(&one, &x));

        // We are now convinced the circuit is satisfied so long as the
        // polynomial commitments open to the correct values, which is true as long
        // as the following accumulator passes the invariant.
        let multiopen_check = kzg::multi_prepare::<_, S>(
            layouter,
            #[cfg(feature = "truncated-challenges")]
            &self.curve_chip,
            &self.scalar_chip,
            &mut transcript,
            queries,
        )?;

        Ok(multiopen_check)
    }

    /// Prepares a plonk proof into a PCS instance that can be finalized or
    /// batched. It is responsibility of the verifier to check the validity of
    /// the instance columns. It is the in-circuit analog of "prepare" from
    /// midnight-proofs at src/plonk/verifier.rs.
    ///
    /// The proof is considered to be valid if the resulting accumulator
    /// satisfies the [invariant](crate::verifier::Accumulator::check)
    /// with respect to the relevant `tau_in_g2`.
    pub fn prepare(
        &self,
        layouter: &mut impl Layouter<S::F>,
        assigned_vk: &AssignedVk<S>,
        assigned_committed_instances: &[(&str, S::AssignedPoint)], // (name, com)
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

    use std::collections::BTreeMap;

    use group::Group;
    use midnight_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{create_proof, keygen_pk, keygen_vk_with_k, prepare, Circuit, Error},
        poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        ecc::{
            curves::CircuitCurve,
            foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
        },
        field::{
            decomposition::{
                chip::{P2RDecompositionChip, P2RDecompositionConfig},
                pow2range::Pow2RangeChip,
            },
            foreign::FieldChip,
            native::NB_ARITH_COLS,
            NativeChip, NativeConfig, NativeGadget,
        },
        hash::poseidon::{
            PoseidonChip, PoseidonConfig, PoseidonState, NB_POSEIDON_ADVICE_COLS,
            NB_POSEIDON_FIXED_COLS,
        },
        instructions::{
            hash::{HashCPU, HashInstructions},
            AssignmentInstructions,
        },
        testing_utils::FromScratch,
        types::{ComposableChip, Instantiable},
        verifier::{accumulator::Accumulator, BlstrsEmulation},
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
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            PoseidonChip::configure_from_scratch(
                meta,
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
            PoseidonChip::load_from_scratch(&mut layouter, &config);

            let inputs = native_chip
                .assign_many(&mut layouter, &self.poseidon_preimage.transpose_array())?;
            let output = poseidon_chip.hash(&mut layouter, &inputs)?;

            native_chip.constrain_as_public_input(&mut layouter, &output)
        }
    }

    #[derive(Clone, Debug)]
    pub struct TestCircuit {
        inner_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>), // (domain, cs, vk_repr)
        inner_committed_instance: Value<C>,
        inner_instances: Value<[F; NB_INNER_INSTANCES]>,
        inner_proof: Value<Vec<u8>>,
    }

    impl Circuit<F> for TestCircuit {
        type Config = (
            NativeConfig,
            P2RDecompositionConfig,
            ForeignEccConfig<C>,
            PoseidonConfig<F>,
        );
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, C, NG>();
            let nb_fixed_cols = NB_ARITH_COLS + 4;

            let advice_columns: Vec<_> =
                (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
            let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();

            let native_config = NativeChip::configure(
                meta,
                &(
                    advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                    fixed_columns[..NB_ARITH_COLS + 4].try_into().unwrap(),
                    [committed_instance_column, instance_column],
                ),
            );
            let core_decomp_config = {
                let pow2_config = Pow2RangeChip::configure(meta, &advice_columns[1..NB_ARITH_COLS]);
                P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2_config))
            };

            let base_config = FieldChip::<F, CBase, C, NG>::configure(meta, &advice_columns);
            let curve_config =
                ForeignEccChip::<F, C, C, NG, NG>::configure(meta, &base_config, &advice_columns);

            let poseidon_config = PoseidonChip::configure(
                meta,
                &(
                    advice_columns[..NB_POSEIDON_ADVICE_COLS]
                        .try_into()
                        .unwrap(),
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
            let curve_chip = ForeignEccChip::new(&config.2, &native_gadget, &native_gadget);
            let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

            let verifier_chip =
                VerifierGadget::<S>::new(&curve_chip, &native_gadget, &poseidon_chip);

            core_decomp_chip.load(&mut layouter)?;

            let assigned_inner_vk: AssignedVk<S> = verifier_chip.assign_vk_as_public_input(
                &mut layouter,
                "inner_vk",
                &self.inner_vk.0,
                &self.inner_vk.1,
                self.inner_vk.2,
            )?;

            let assigned_committed_instance =
                curve_chip.assign(&mut layouter, self.inner_committed_instance)?;

            let assigned_inner_pi = native_gadget
                .assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

            let mut inner_proof_acc = verifier_chip.prepare(
                &mut layouter,
                &assigned_inner_vk,
                &[("com_instance", assigned_committed_instance)],
                &[&assigned_inner_pi],
                self.inner_proof.clone(),
            )?;

            inner_proof_acc.collapse(&mut layouter, &curve_chip, &native_gadget)?;

            verifier_chip.constrain_as_public_input(&mut layouter, &inner_proof_acc)
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
                &[InnerCircuit::from_witness(preimage)],
                1,
                &[&[&[], &inner_public_inputs]],
                &mut rng,
                &mut transcript,
            )
            .unwrap_or_else(|_| panic!("Problem creating the inner proof"));
            transcript.finalize()
        };

        let inner_dual_msm = {
            let mut transcript =
                CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&inner_proof);
            prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                &inner_vk,
                &[&[C::identity()]],
                &[&[&inner_public_inputs]],
                &mut transcript,
            )
            .expect("Problem preparing the inner proof")
        };

        let mut fixed_bases = BTreeMap::new();
        fixed_bases.insert(String::from("com_instance"), C::identity());
        fixed_bases.extend(crate::verifier::fixed_bases::<S>("inner_vk", &inner_vk));

        let mut inner_acc: Accumulator<S> = inner_dual_msm.clone().into();
        inner_acc.extract_fixed_bases(&fixed_bases);

        assert!(inner_dual_msm.check(&inner_params.verifier_params()));
        assert!(inner_acc.check(&inner_params.s_g2().into(), &fixed_bases));

        inner_acc.collapse();

        // The inner proof is ready.
        // Now, let us make a proof that we know an inner proof.

        const K: u32 = 18;

        let mut public_inputs = AssignedVk::<S>::as_public_input(&inner_vk);
        public_inputs.extend(AssignedAccumulator::as_public_input(&inner_acc));

        let circuit = TestCircuit {
            inner_vk: (
                inner_vk.get_domain().clone(),
                inner_vk.cs().clone(),
                Value::known(inner_vk.transcript_repr()),
            ),
            inner_committed_instance: Value::known(C::identity()),
            inner_instances: Value::known([output]),
            inner_proof: Value::known(inner_proof),
        };

        let prover =
            MockProver::run(K, &circuit, vec![vec![], public_inputs]).expect("MockProver failed");
        prover.assert_satisfied();
    }
}
