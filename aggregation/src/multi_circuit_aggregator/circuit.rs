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

//! IVC circuit for multi-circuit proof aggregation.
//!
//! This module defines [`ProofAggregation`], the IVC transition that folds one
//! inner proof per step. It implements all the IVC traits ([`IvcContext`],
//! [`IvcState`], [`IvcIO`], [`IvcTransition`]).
//!
//! The off-circuit state ([`State`]) carries the full list of [`Claim`]s plus
//! constant-size summaries (a Poseidon hash chain digest and an accumulator).
//! The in-circuit state ([`AssignedState`]) contains only the summaries.
//!
//! [`InnerCircuitsContext`] holds the shared setup data (constraint system,
//! evaluation domain, SRS) that all inner circuits must conform to.
//! [`AggregationWitness`] is the private input to each IVC step: it contains
//! the inner proof bytes together with its VK and statement.

use std::collections::BTreeMap;

use ff::Field;
use group::Group;
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{hash::HashCPU, *},
    types::{AssignedNative, Instantiable},
    verifier::{self, Accumulator, AssignedAccumulator},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, ConstraintSystem, Error},
    poly::{
        kzg::{params::ParamsVerifierKZG, KZGCommitmentScheme},
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};

use super::aggregator::AggregationWitness;
use crate::{
    ivc::{IvcContext, IvcIO, IvcState, IvcTransition, C, E, F, S},
    multi_circuit_aggregator::{
        utils::{assign_and_hash_vk, compute_vk_hash},
        Claim,
    },
};

/// Off-circuit IVC state for multi-circuit proof aggregation.
///
/// Contains the full list of aggregated claims, a Poseidon hash chain digest
/// over those claims (constant-size summary), and a running accumulator for
/// deferred inner-proof verification.
#[derive(Clone, Debug)]
pub struct State {
    claims: Vec<Claim>,
    claims_hash: F,
    inner_acc: Accumulator<S>,
}

impl State {
    /// Returns the list of aggregated claims.
    pub fn claims(&self) -> &[Claim] {
        &self.claims
    }
}

/// In-circuit counterpart of [`State`] (constant size).
///
/// Contains only the claims hash and the accumulator, the full list of
/// claims is not represented in-circuit.
#[derive(Clone, Debug)]
pub struct AssignedState {
    claims_hash: AssignedNative<F>,
    inner_acc: AssignedAccumulator<S>,
}

/// Setup data for the inner circuits, threaded as IVC context.
///
/// Contains the shared constraint system, evaluation domain, SRS verifier
/// parameters and [`ZkStdLibArch`] of all inner circuits to be aggregated.
#[derive(Clone, Debug)]
pub struct InnerCircuitsContext {
    cs: ConstraintSystem<F>,
    domain: EvaluationDomain<F>,
    params_verifier: ParamsVerifierKZG<E>,
    arch: ZkStdLibArch,
}

impl InnerCircuitsContext {
    /// Creates a new [`InnerCircuitsContext`] from the shared architecture,
    /// circuit size parameter `k` (log2 of rows), and SRS verifier parameters.
    pub fn new(arch: ZkStdLibArch, k: u32, params_verifier: ParamsVerifierKZG<E>) -> Self {
        let mut cs = ConstraintSystem::default();
        ZkStdLib::configure(&mut cs, (arch, (k - 1) as u8));
        let domain = EvaluationDomain::new(cs.degree() as u32, k);
        InnerCircuitsContext {
            cs,
            domain,
            params_verifier,
            arch,
        }
    }

    /// The [`ZkStdLibArch`] that all inner circuits must use.
    pub fn arch(&self) -> ZkStdLibArch {
        self.arch
    }
}

/// IVC transition that aggregates one inner proof per step.
#[derive(Clone, Debug)]
pub struct ProofAggregation {
    std_lib: ZkStdLib,
    inner_ctx: InnerCircuitsContext,
}

impl IvcContext for ProofAggregation {
    type Context = InnerCircuitsContext;

    fn new(std_lib: ZkStdLib, ctx: &InnerCircuitsContext) -> Self {
        ProofAggregation {
            std_lib,
            inner_ctx: ctx.clone(),
        }
    }

    fn write_context<W: std::io::Write>(
        ctx: &InnerCircuitsContext,
        writer: &mut W,
    ) -> std::io::Result<()> {
        ctx.arch.write(writer)?;
        writer.write_all(&ctx.domain.k().to_le_bytes())?;
        ctx.params_verifier.write(writer, SerdeFormat::RawBytes)
    }

    fn read_context<R: std::io::Read>(reader: &mut R) -> std::io::Result<InnerCircuitsContext> {
        let arch = ZkStdLibArch::read(reader)?;
        let mut k_bytes = [0u8; 4];
        reader.read_exact(&mut k_bytes)?;
        let k = u32::from_le_bytes(k_bytes);
        let params_verifier = ParamsVerifierKZG::read(reader, SerdeFormat::RawBytes)?;
        Ok(InnerCircuitsContext::new(arch, k, params_verifier))
    }
}

impl IvcState for ProofAggregation {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis(_ctx: &InnerCircuitsContext) -> Self::State {
        State {
            claims: vec![],
            claims_hash: F::ZERO,
            inner_acc: Accumulator::<S>::trivial(&[]),
        }
    }

    fn decider(ctx: &InnerCircuitsContext, state: &State) -> bool {
        // Recompute the hash chain from the collected claims.
        let claims_hash = state.claims.iter().fold(F::ZERO, |h_acc, claim| {
            let vk_hash = compute_vk_hash(&claim.vk);
            let statement = claim.statement.format_instance();
            <PoseidonChip<F> as HashCPU<F, F>>::hash(&[vk_hash, statement, h_acc])
        });

        if claims_hash != state.claims_hash {
            return false;
        }

        // Check the inner accumulator (fully collapsed, no fixed bases).
        state.inner_acc.check(&ctx.params_verifier, &BTreeMap::new())
    }
}

impl IvcIO for ProofAggregation {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let claims_hash = self.std_lib.assign(layouter, value.as_ref().map(|s| s.claims_hash))?;

        let inner_acc = self.std_lib.verifier().assign_collapsed_accumulator(
            layouter,
            &[],
            value.as_ref().map(|s| s.inner_acc.clone()),
        )?;

        Ok(AssignedState {
            claims_hash,
            inner_acc,
        })
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        self.std_lib.constrain_as_public_input(layouter, &state.claims_hash)?;
        self.std_lib.verifier().constrain_as_public_input(layouter, &state.inner_acc)
    }

    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok([
            self.std_lib.as_public_input(layouter, &state.claims_hash)?,
            self.std_lib.verifier().as_public_input(layouter, &state.inner_acc)?,
        ]
        .concat())
    }

    fn format_public_input(state: &State) -> Vec<F> {
        [
            vec![state.claims_hash],
            AssignedAccumulator::<S>::as_public_input(&state.inner_acc),
        ]
        .concat()
    }
}

impl IvcTransition for ProofAggregation {
    type Witness = AggregationWitness;

    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn transition(
        ctx: &InnerCircuitsContext,
        state: &Self::State,
        witness: Self::Witness,
    ) -> Self::State {
        // 1. Compute vk_hash.
        let vk_hash = compute_vk_hash(&witness.claim.vk);

        // 2. Extract the statement.
        let statement = witness.claim.statement.format_instance();

        // 3. Prepare inner proof into an accumulator, resolve fixed bases.
        let inner_proof_acc = {
            let mut transcript =
                CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&witness.inner_proof);
            let dual_msm =
                plonk::prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                    witness.claim.vk.vk(),
                    &[&[C::identity()]],
                    &[&[&[statement]]],
                    &mut transcript,
                )
                .expect("off-circuit prepare should succeed");

            // Sanity check (also validated in Aggregator::aggregate).
            assert!(
                dual_msm.clone().check(&ctx.params_verifier),
                "invalid inner proof"
            );

            let vk_bases = verifier::fixed_bases::<S>("inner_vk", witness.claim.vk.vk());
            let mut acc = Accumulator::from_dual_msm(dual_msm, "inner_vk", &vk_bases);
            acc.collapse();
            acc.resolve_fixed_bases(&vk_bases);
            acc
        };

        // 4. Accumulate with the running accumulator and collapse.
        let inner_acc = {
            let mut acc = Accumulator::accumulate(&[inner_proof_acc, state.inner_acc.clone()]);
            acc.collapse();
            acc
        };

        // 5. Update hash chain.
        let claims_hash =
            <PoseidonChip<F> as HashCPU<F, F>>::hash(&[vk_hash, statement, state.claims_hash]);

        let mut claims = state.claims.clone();
        claims.push(witness.claim);

        State {
            claims,
            claims_hash,
            inner_acc,
        }
    }

    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error> {
        // 1. Witness VK bases and compute their hash in-circuit.
        let (vk_hash, fixed_bases_map) = assign_and_hash_vk(
            layouter,
            &self.std_lib,
            &self.inner_ctx.cs,
            witness.as_ref().map(|w| &w.claim.vk),
        )?;

        // 2. Witness the statement.
        let statement = self.std_lib.assign(
            layouter,
            witness.as_ref().map(|w| w.claim.statement.format_instance()),
        )?;

        // 3. Prepare inner proof into an accumulator, resolve fixed bases.
        let inner_proof_acc = {
            let acc_value = witness.map(|w| {
                let mut transcript =
                    CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&w.inner_proof);
                let dual_msm = plonk::prepare::<
                    F,
                    KZGCommitmentScheme<E>,
                    CircuitTranscript<PoseidonState<F>>,
                >(
                    w.claim.vk.vk(),
                    &[&[C::identity()]],
                    &[&[&[w.claim.statement.format_instance()]]],
                    &mut transcript,
                )
                .expect("off-circuit prepare should succeed");

                let vk_bases = verifier::fixed_bases::<S>("inner_vk", w.claim.vk.vk());
                let mut acc = Accumulator::from_dual_msm(dual_msm, "inner_vk", &vk_bases);
                acc.collapse();
                acc
            });

            let mut acc = self.std_lib.verifier().assign_collapsed_accumulator(
                layouter,
                &fixed_bases_map.keys().cloned().collect::<Vec<_>>(),
                acc_value,
            )?;

            acc.resolve_fixed_bases(&fixed_bases_map);
            acc
        };

        // 4. Accumulate with the running accumulator and collapse.
        let inner_acc = {
            let mut acc = self
                .std_lib
                .verifier()
                .accumulate(layouter, &[inner_proof_acc, state.inner_acc.clone()])?;

            acc.collapse(
                layouter,
                self.std_lib.bls12_381_curve(),
                self.std_lib.bls12_381_scalar(),
            )?;
            acc
        };

        // 5. Update hash chain.
        let claims_hash = self
            .std_lib
            .poseidon(layouter, &[vk_hash, statement, state.claims_hash.clone()])?;

        Ok(AssignedState {
            claims_hash,
            inner_acc,
        })
    }
}
