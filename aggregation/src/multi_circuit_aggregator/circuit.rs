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
    verifier::{
        Accumulator, AssignedAccumulator, AssignedKZGMultiCommitment, InCircuitKZG, UnboundVk,
        vk_hash,
    },
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
    ivc::{C, E, F, IvcContext, IvcIO, IvcState, IvcTransition, S},
    multi_circuit_aggregator::Claim,
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
/// Contains only the claims hash and the accumulator, the full list of claims
/// is not represented in-circuit.
#[derive(Clone, Debug)]
pub struct AssignedState {
    claims_hash: AssignedNative<F>,
    inner_acc: AssignedAccumulator<S>,
}

/// Setup data for the inner circuits, threaded as IVC context.
///
/// Contains the shared constraint system, SRS verifier parameters,
/// [`ZkStdLibArch`] and `max_bit_len` of all inner circuits to be aggregated.
#[derive(Clone, Debug)]
pub struct InnerCircuitsContext {
    cs: ConstraintSystem<F>,
    params_verifier: ParamsVerifierKZG<E>,
    arch: ZkStdLibArch,
    max_bit_len: u8,
}

impl InnerCircuitsContext {
    /// Creates a new [`InnerCircuitsContext`] from the shared architecture, the
    /// `max_bit_len` the inner circuits were configured with (`k - 1` in
    /// zk_stdlib), and SRS verifier parameters.
    ///
    /// `max_bit_len` only affects foreign-field chips: inner circuits that use
    /// them must all have been configured with this value, whereas the others
    /// may have any size.
    pub fn new(arch: ZkStdLibArch, max_bit_len: u8, params_verifier: ParamsVerifierKZG<E>) -> Self {
        let mut cs = ConstraintSystem::default();
        ZkStdLib::configure(&mut cs, (arch, max_bit_len));
        InnerCircuitsContext {
            cs: cs.into_finalized(),
            params_verifier,
            arch,
            max_bit_len,
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
        writer.write_all(&[ctx.max_bit_len])?;
        ctx.params_verifier.write(writer, SerdeFormat::RawBytes)
    }

    fn read_context<R: std::io::Read>(reader: &mut R) -> std::io::Result<InnerCircuitsContext> {
        let arch = ZkStdLibArch::read(reader)?;
        let mut max_bit_len = [0u8; 1];
        reader.read_exact(&mut max_bit_len)?;
        let params_verifier = ParamsVerifierKZG::read(reader, SerdeFormat::RawBytes)?;
        Ok(InnerCircuitsContext::new(
            arch,
            max_bit_len[0],
            params_verifier,
        ))
    }
}

/// Extends the claims hash chain with a claim:
/// `H(vk_hash || statement || claims_hash)`.
///
/// Off-circuit counterpart of the chain update in `circuit_transition`.
fn extend_claims_hash(vk_hash: F, statement: F, claims_hash: F) -> F {
    <PoseidonChip<F> as HashCPU<F, F>>::hash(&[vk_hash, statement, claims_hash])
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
            let statement = claim.statement.format_instance();
            extend_claims_hash(vk_hash::<S>(claim.vk.vk()), statement, h_acc)
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
        // 1. Extract the statement.
        let statement = witness.claim.statement.format_instance();

        // 2. Prepare inner proof into an accumulator.
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

            // The inner VK is private in-circuit, so its commitments are variable
            // bases. Only `-G` is a fixed base, resolved after collapsing.
            let neg_g = BTreeMap::from([(PolynomialLabel::Custom("-G".into()), -C::generator())]);
            let mut acc = Accumulator::from_dual_msm(dual_msm, &neg_g);
            acc.collapse();
            acc.resolve_fixed_bases(&neg_g);
            acc
        };

        // 3. Accumulate with the running accumulator and collapse.
        let inner_acc = {
            let mut acc = Accumulator::accumulate(&[inner_proof_acc, state.inner_acc.clone()]);
            acc.collapse();
            acc
        };

        // 4. Update hash chain.
        let claims_hash = extend_claims_hash(
            vk_hash::<S>(witness.claim.vk.vk()),
            statement,
            state.claims_hash,
        );

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
        let verifier = self.std_lib.verifier();

        // 1. Witness the VK and the statement, bind the VK to its witnessed hash, and
        //    add both to the hash chain (checked by the decider).
        let unbound_vk: UnboundVk<S, InCircuitKZG<S>> = verifier.assign_private_vk(
            layouter,
            &self.inner_ctx.cs,
            witness.as_ref().map(|w| w.claim.vk.vk()),
        )?;
        let statement: AssignedNative<F> = self.std_lib.assign(
            layouter,
            witness.as_ref().map(|w| w.claim.statement.format_instance()),
        )?;
        let assigned_vk_hash: AssignedNative<F> = self.std_lib.assign(
            layouter,
            witness.as_ref().map(|w| vk_hash::<S>(w.claim.vk.vk())),
        )?;
        let assigned_vk = verifier.bind_vk_to_hash(layouter, unbound_vk, &assigned_vk_hash)?;
        let claims_hash = self.std_lib.poseidon(
            layouter,
            &[
                assigned_vk_hash,
                statement.clone(),
                state.claims_hash.clone(),
            ],
        )?;

        // 2. Verify the inner proof in-circuit against the witnessed VK and statement.
        let inner_proof_acc = {
            let instance_com = AssignedKZGMultiCommitment::commitment_to_zero(
                layouter,
                self.std_lib.bls12_381(),
                PolynomialLabel::CommittedInstance(0),
            )?;
            let mut acc = verifier.prepare(
                layouter,
                &assigned_vk,
                &[instance_com],
                &[std::slice::from_ref(&statement)],
                witness.map(|w| w.inner_proof),
            )?;

            // Collapse before resolving, mirroring the off-circuit `transition`
            // exactly so both feed an identically-shaped accumulator into the
            // accumulation step (otherwise the batching challenge diverges).
            // The VK commitments are variable bases, so only `-G` is resolved.
            acc.collapse(
                layouter,
                self.std_lib.bls12_381(),
                self.std_lib.bls12_381().scalar_field_chip(),
            )?;
            let neg_g = self.std_lib.bls12_381().assign_fixed(layouter, -C::generator())?;
            acc.resolve_fixed_bases(&BTreeMap::from([(
                PolynomialLabel::Custom("-G".into()),
                neg_g,
            )]));
            acc
        };

        // 3. Accumulate with the running accumulator and collapse.
        let inner_acc = {
            let mut acc =
                verifier.accumulate(layouter, &[inner_proof_acc, state.inner_acc.clone()])?;

            acc.collapse(
                layouter,
                self.std_lib.bls12_381(),
                self.std_lib.bls12_381().scalar_field_chip(),
            )?;
            acc
        };

        Ok(AssignedState {
            claims_hash,
            inner_acc,
        })
    }
}
