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
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{hash::HashCPU, *},
    types::{AssignedNative, Instantiable},
    verifier::{self, Accumulator, AssignedAccumulator, AssignedKZGMultiCommitment},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, ConstraintSystem, Error},
    poly::{
        PolynomialLabel,
        kzg::{KZGCommitmentScheme, commitment::KZGMultiCommitment, params::ParamsVerifierKZG},
    },
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};

use super::aggregator::AggregationWitness;
use crate::{
    ivc::{E, F, IvcContext, IvcIO, IvcState, IvcTransition, S},
    multi_circuit_aggregator::{
        Claim,
        utils::{assign_as_public_inputs_and_hash_vk, compute_vk_hash},
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

/// In-circuit representation of a verifying key.
#[derive(Clone, Debug)]
struct AssignedVk {
    repr: AssignedNative<F>,
    k: AssignedNative<F>,
    omega: AssignedNative<F>,
}

/// In-circuit counterpart of [`State`] (constant size).
///
/// Contains only the vk from the last claim, the claims hash and the
/// accumulator, the full list of claims is not represented in-circuit.
#[derive(Clone, Debug)]
pub struct AssignedState {
    last_vk: AssignedVk,
    claims_hash: AssignedNative<F>,
    inner_acc: AssignedAccumulator<S>,
}

/// Setup data for the inner circuits, threaded as IVC context.
///
/// Contains the shared constraint system, SRS verifier parameters and
/// [`ZkStdLibArch`] of all inner circuits to be aggregated.
#[derive(Clone, Debug)]
pub struct InnerCircuitsContext {
    cs: ConstraintSystem<F>,
    params_verifier: ParamsVerifierKZG<E>,
    arch: ZkStdLibArch,
}

impl InnerCircuitsContext {
    /// Creates a new [`InnerCircuitsContext`] from the shared architecture and
    /// SRS verifier parameters.
    pub fn new(arch: ZkStdLibArch, params_verifier: ParamsVerifierKZG<E>) -> Self {
        // The `max_bit_len` value is arbitrary: it only affects the configuration
        // of foreign-field chips, which inner circuits are not expected to use.
        // (Otherwise their `cs` would depend on their own `k` and would not match
        // this one.)
        let mut cs = ConstraintSystem::default();
        ZkStdLib::configure(&mut cs, (arch, 0));
        InnerCircuitsContext {
            cs: cs.into_finalized(),
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
        ctx.params_verifier.write(writer, SerdeFormat::RawBytes)
    }

    fn read_context<R: std::io::Read>(reader: &mut R) -> std::io::Result<InnerCircuitsContext> {
        let arch = ZkStdLibArch::read(reader)?;
        let params_verifier = ParamsVerifierKZG::read(reader, SerdeFormat::RawBytes)?;
        Ok(InnerCircuitsContext::new(arch, params_verifier))
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
        // There is no integrity checks performed in the VK (`vk_repr`, `k` and
        // `omega`), as those are guaranteed to be correct by the hash-chain,
        // which is checked in the decider. The hash-chain is enforced to be
        // correctly computed by hashing the previous `claims_hash`
        // together with the `vk_repr`, `k` and `omega` of the current circuit.
        // In the base case (no claims yet) there is no last vk: we use the default
        // one, as `format_public_input` does.
        let [last_vk_repr, last_vk_k, last_vk_omega] = value
            .as_ref()
            .map(|s| {
                let vk = s.claims.last().map(|c| c.vk.vk().clone()).unwrap_or_default();
                let domain = vk.get_domain();
                [
                    vk.transcript_repr(),
                    F::from(domain.k() as u64),
                    domain.get_omega(),
                ]
            })
            .transpose_array();
        let last_vk_repr = self.std_lib.assign(layouter, last_vk_repr)?;
        let last_vk_k = self.std_lib.assign(layouter, last_vk_k)?;
        let last_vk_omega = self.std_lib.assign(layouter, last_vk_omega)?;
        let claims_hash = self.std_lib.assign(layouter, value.as_ref().map(|s| s.claims_hash))?;

        let inner_acc = self.std_lib.verifier().assign_collapsed_accumulator(
            layouter,
            &[],
            value.as_ref().map(|s| s.inner_acc.clone()),
        )?;

        let last_vk = AssignedVk {
            repr: last_vk_repr,
            omega: last_vk_omega,
            k: last_vk_k,
        };

        Ok(AssignedState {
            last_vk,
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
            self.std_lib.as_public_input(layouter, &state.last_vk.repr)?,
            self.std_lib.as_public_input(layouter, &state.last_vk.k)?,
            self.std_lib.as_public_input(layouter, &state.last_vk.omega)?,
            self.std_lib.as_public_input(layouter, &state.claims_hash)?,
            self.std_lib.verifier().as_public_input(layouter, &state.inner_acc)?,
        ]
        .concat())
    }

    fn format_public_input(state: &State) -> Vec<F> {
        // In the base case (no claims yet) there is no last vk: we use the default
        // one, as `assign` does.
        let last_vk = state.claims.last().map(|c| c.vk.vk().clone()).unwrap_or_default();
        let domain = last_vk.get_domain();
        [
            vec![
                last_vk.transcript_repr(),
                F::from(domain.k() as u64),
                domain.get_omega(),
            ],
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
                    &[KZGMultiCommitment::commitment_to_zero(
                        PolynomialLabel::CommittedInstance(0),
                    )],
                    &[&[statement]],
                    &mut transcript,
                )
                .expect("off-circuit prepare should succeed");

            // Sanity check (also validated in Aggregator::aggregate).
            assert!(
                dual_msm.clone().check(&ctx.params_verifier),
                "invalid inner proof"
            );

            let vk_bases = verifier::fixed_bases::<S>(witness.claim.vk.vk());
            let mut acc = Accumulator::from_dual_msm(dual_msm, &vk_bases);
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
        // 1. Assign the VK as a public input, witness its bases, and compute their hash
        //    in-circuit.
        let (assigned_vk, vk_hash, fixed_bases_map) = assign_as_public_inputs_and_hash_vk(
            layouter,
            &self.std_lib,
            &self.inner_ctx.cs,
            witness.as_ref().map(|w| &w.claim.vk),
        )?;

        // 2. Witness the statement.
        let statement: AssignedNative<F> = self.std_lib.assign(
            layouter,
            witness.as_ref().map(|w| w.claim.statement.format_instance()),
        )?;

        // 3. Verify the inner proof in-circuit against the witnessed VK and statement.
        let inner_proof_acc = {
            let instance_com = AssignedKZGMultiCommitment::commitment_to_zero(
                layouter,
                self.std_lib.bls12_381(),
                PolynomialLabel::CommittedInstance(0),
            )?;
            let mut acc = self.std_lib.verifier().prepare(
                layouter,
                &assigned_vk,
                &[instance_com],
                &[std::slice::from_ref(&statement)],
                witness.map(|w| w.inner_proof),
            )?;

            // Collapse before resolving, mirroring the off-circuit `transition`
            // exactly so both feed an identically-shaped accumulator into the
            // accumulation step (otherwise the batching challenge diverges).
            acc.collapse(
                layouter,
                self.std_lib.bls12_381(),
                self.std_lib.bls12_381().scalar_field_chip(),
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
                self.std_lib.bls12_381(),
                self.std_lib.bls12_381().scalar_field_chip(),
            )?;
            acc
        };

        // 5. Update hash chain.
        let claims_hash = self
            .std_lib
            .poseidon(layouter, &[vk_hash, statement, state.claims_hash.clone()])?;

        Ok(AssignedState {
            last_vk: AssignedVk {
                repr: assigned_vk.transcript_repr().clone(),
                k: assigned_vk.k().clone(),
                omega: assigned_vk.omega().clone(),
            },
            claims_hash,
            inner_acc,
        })
    }
}
