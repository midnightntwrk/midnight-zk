//! Proof aggregation via IVC.
//!
//! This example demonstrates how to aggregate multiple proofs of the same
//! circuit (a SHA-256 preimage circuit) using Incrementally Verifiable
//! Computation (IVC). All aggregated proofs must share the same verifying
//! key, i.e. they must originate from the same inner circuit.
//!
//! The IVC state tracks:
//! - A list of aggregated statements (off-circuit),
//! - A Poseidon hash of those statements (constant-size),
//! - An accumulator for deferred inner-proof verification (decider check).
//!
//! At each IVC step the transition function verifies one inner proof
//! in-circuit and folds the result into the running accumulator.
//!
//! DO NOT add this example to the CI as it is slow.
//!
//! Run with `features = truncated-challenges`.

#[path = "common/mod.rs"]
mod common;

use std::{collections::BTreeMap, time::Instant};

use common::sha_preimage::ShaPreimageCircuit;
use ff::Field;
use group::Group;
use midnight_aggregation::ivc::{self, IvcContext, IvcState, IvcTransition};
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{hash::HashCPU, *},
    types::{AssignedBit, AssignedNative, InnerValue, Instantiable},
    verifier::{self, Accumulator, AssignedAccumulator, BlstrsEmulation, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, ConstraintSystem, Error},
    poly::{
        kzg::{
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{MidnightVK, Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;

use crate::common::sha_preimage;

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;
type E = <S as SelfEmulation>::Engine;

type InnerCircuit = ShaPreimageCircuit;

/// Setup data for the inner circuit, threaded as IVC context.
#[derive(Clone, Debug)]
pub struct InnerCircuitContext {
    /// Constraint system used by the inner proofs (to be aggregated).
    cs: ConstraintSystem<F>,
    /// Evaluation domain for the inner circuit.
    domain: EvaluationDomain<F>,
    /// Verifying key.
    vk: MidnightVK,
    /// SRS verifier parameters (for off-circuit proof preparation).
    params_verifier: ParamsVerifierKZG<E>,
}

impl InnerCircuitContext {
    fn fixed_bases(&self) -> BTreeMap<String, C> {
        verifier::fixed_bases::<S>("inner_vk", self.vk.vk())
    }
}

/// Off-circuit IVC state for proof aggregation.
#[derive(Clone, Debug)]
pub struct State {
    /// All aggregated inner-circuit statements.
    statements: Vec<<InnerCircuit as Relation>::Instance>,
    /// Poseidon hash chain: H(h_n, H(h_{n-1}, H(... H(h_1, 0)))),
    /// where h_i = Poseidon(statement_i) is the digest of the i-th statement.
    statements_hash: F,
    /// Running accumulator over inner-proof verifications.
    inner_acc: Accumulator<S>,
}

/// In-circuit counterpart of [`State`] (constant size).
#[derive(Clone, Debug)]
pub struct AssignedState {
    statements_hash: AssignedNative<F>,
    inner_acc: AssignedAccumulator<S>,
}

impl InnerValue for AssignedState {
    type Element = State;

    fn value(&self) -> Value<State> {
        self.statements_hash
            .value()
            .zip(self.inner_acc.value())
            .map(|(hash, acc)| State {
                statements: vec![], // off-circuit only; not recoverable from cells
                statements_hash: *hash,
                inner_acc: acc,
            })
    }
}

impl Instantiable<F> for AssignedState {
    fn as_public_input(element: &State) -> Vec<F> {
        [
            vec![element.statements_hash],
            AssignedAccumulator::<S>::as_public_input(&element.inner_acc),
        ]
        .concat()
    }
}

/// Witness for a single aggregation step: an inner statement and its proof.
#[derive(Clone, Debug)]
pub struct AggregationWitness {
    pub inner_statement: <InnerCircuit as Relation>::Instance,
    pub inner_proof: Vec<u8>,
}

/// IVC transition that aggregates one inner proof per step.
#[derive(Clone, Debug)]
pub struct ProofAggregation {
    std_lib: ZkStdLib,
    inner_ctx: InnerCircuitContext,
}

impl IvcContext for ProofAggregation {
    type Context = InnerCircuitContext;

    fn new(std_lib: ZkStdLib, ctx: &InnerCircuitContext) -> Self {
        ProofAggregation {
            std_lib,
            inner_ctx: ctx.clone(),
        }
    }

    fn write_context<W: std::io::Write>(
        _ctx: &InnerCircuitContext,
        _writer: &mut W,
    ) -> std::io::Result<()> {
        // InnerCircuitContext serialization is not needed for this example.
        unimplemented!("InnerCircuitContext serialization not implemented")
    }

    fn read_context<R: std::io::Read>(_reader: &mut R) -> std::io::Result<InnerCircuitContext> {
        unimplemented!("InnerCircuitContext deserialization not implemented")
    }
}

impl IvcState for ProofAggregation {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis(ctx: &InnerCircuitContext) -> Self::State {
        State {
            statements: vec![],
            statements_hash: F::ZERO,
            inner_acc: Accumulator::<S>::trivial(
                &ctx.fixed_bases().keys().cloned().collect::<Vec<_>>(),
            ),
        }
    }

    fn is_genesis(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<AssignedBit<F>, Error> {
        self.std_lib.is_zero(layouter, &state.statements_hash)
    }

    fn decider(ctx: &InnerCircuitContext, state: &State) -> bool {
        // Hash all collected statements and check against the claimed hash.
        let expected_hash = state.statements.iter().fold(F::ZERO, |h_acc, x| {
            let pis = ShaPreimageCircuit::format_instance(x).expect("valid instance");
            let h = <PoseidonChip<F> as HashCPU<F, F>>::hash(&pis);
            <PoseidonChip<F> as HashCPU<F, F>>::hash(&[h, h_acc])
        });

        if expected_hash != state.statements_hash {
            return false;
        }

        // Check the inner accumulator.
        state.inner_acc.check(&ctx.params_verifier, &ctx.fixed_bases())
    }
}

impl AssignmentInstructions<F, AssignedState> for ProofAggregation {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let statements_hash =
            self.std_lib.assign(layouter, value.as_ref().map(|s| s.statements_hash))?;

        let inner_acc = self.std_lib.verifier().assign_collapsed_accumulator(
            layouter,
            &self.inner_ctx.fixed_bases().keys().cloned().collect::<Vec<_>>(),
            value.as_ref().map(|s| s.inner_acc.clone()),
        )?;

        Ok(AssignedState {
            statements_hash,
            inner_acc,
        })
    }

    fn assign_fixed(
        &self,
        _layouter: &mut impl Layouter<F>,
        _constant: State,
    ) -> Result<AssignedState, Error> {
        unimplemented!("not used by IVC")
    }
}

impl PublicInputInstructions<F, AssignedState> for ProofAggregation {
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok([
            self.std_lib.as_public_input(layouter, &state.statements_hash)?,
            self.std_lib.verifier().as_public_input(layouter, &state.inner_acc)?,
        ]
        .concat())
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        self.std_lib.constrain_as_public_input(layouter, &state.statements_hash)?;
        self.std_lib.verifier().constrain_as_public_input(layouter, &state.inner_acc)
    }

    fn assign_as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        _value: Value<State>,
    ) -> Result<AssignedState, Error> {
        unimplemented!("not used by IVC")
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
        ctx: &InnerCircuitContext,
        state: &Self::State,
        witness: Self::Witness,
    ) -> Self::State {
        // Format inner statement as field elements.
        let statement_pis =
            ShaPreimageCircuit::format_instance(&witness.inner_statement).expect("valid instance");

        // Off-circuit: prepare the inner proof to obtain the proof accumulator.
        let inner_proof_acc = {
            let mut transcript =
                CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&witness.inner_proof);
            let dual_msm =
                plonk::prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                    ctx.vk.vk(),
                    &[&[C::identity()]],
                    &[&[&statement_pis]],
                    &mut transcript,
                )
                .expect("off-circuit prepare should succeed");

            // Sanity check.
            assert!(
                dual_msm.clone().check(&ctx.params_verifier),
                "invalid inner proof"
            );

            Accumulator::from_dual_msm(dual_msm, "inner_vk", &ctx.fixed_bases())
        };

        // Accumulate and collapse.
        let inner_acc = {
            let mut acc = Accumulator::accumulate(&[inner_proof_acc, state.inner_acc.clone()]);
            acc.collapse();
            acc
        };

        // Hash: H(h_statement, prev_hash).
        let statements_hash = {
            let h_statement = <PoseidonChip<F> as HashCPU<F, F>>::hash(&statement_pis);
            <PoseidonChip<F> as HashCPU<F, F>>::hash(&[h_statement, state.statements_hash])
        };

        let mut statements = state.statements.clone();
        statements.push(witness.inner_statement);

        State {
            statements,
            statements_hash,
            inner_acc,
        }
    }

    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error> {
        // Assign inner VK as a hard-coded constant.
        let inner_vk = self.std_lib.verifier().assign_fixed_vk(
            layouter,
            "inner_vk",
            &self.inner_ctx.domain,
            &self.inner_ctx.cs,
            self.inner_ctx.vk.vk().transcript_repr(),
        )?;

        // Assign the inner statement as a witness.
        let statement_pis = self.std_lib.assign_many(
            layouter,
            &witness
                .as_ref()
                .map(|w| ShaPreimageCircuit::format_instance(&w.inner_statement).unwrap())
                .transpose_vec(sha_preimage::NB_PUBLIC_INPUTS),
        )?;

        // Verify the inner proof in-circuit.
        let id_point = self.std_lib.bls12_381_curve().assign_fixed(layouter, C::identity())?;

        let inner_proof_acc = self.std_lib.verifier().prepare(
            layouter,
            &inner_vk,
            &[id_point],
            &[&statement_pis],
            witness.map(|w| w.inner_proof),
        )?;

        // Accumulate and collapse.
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

        // Hash: H(h_statement, prev_hash).
        let statements_hash = {
            let h_statement = self.std_lib.poseidon(layouter, &statement_pis)?;
            self.std_lib.poseidon(layouter, &[h_statement, state.statements_hash.clone()])?
        };

        Ok(AssignedState {
            statements_hash,
            inner_acc,
        })
    }
}

fn main() {
    // Circuit size parameter for the IVC circuit (log2 of rows).
    const IVC_K: u32 = 19;
    const STEPS: usize = 3;

    // The inner circuit can use a different SRS than the IVC circuit.
    let inner_srs = ParamsKZG::unsafe_setup(sha_preimage::K, OsRng);
    let inner_vk = sha_preimage::setup_vk(&inner_srs);
    let inner_pk = sha_preimage::setup_pk(&inner_vk);
    let inner_ctx = {
        let (inner_cs, inner_domain) =
            common::constraint_system(ShaPreimageCircuit.used_chips(), sha_preimage::K);

        InnerCircuitContext {
            cs: inner_cs,
            domain: inner_domain,
            vk: inner_vk,
            params_verifier: inner_srs.verifier_params(),
        }
    };

    // Generate random inner statements and prove them.
    let start = Instant::now();
    let inner_statements_with_witnesses: [_; STEPS] =
        std::array::from_fn(|_| sha_preimage::random_instance());
    let inner_proofs: [_; STEPS] = std::array::from_fn(|i| {
        let (digest, preimage) = &inner_statements_with_witnesses[i];
        sha_preimage::prove(&inner_srs, &inner_pk, digest, *preimage)
    });
    let inner_statements = inner_statements_with_witnesses.map(|(x, _)| x);
    println!("{STEPS} inner proofs generated in {:.2?}", start.elapsed());

    // IVC setup.
    let ivc_srs = midnight_zk_stdlib::utils::plonk_api::filecoin_srs(IVC_K);
    let start = Instant::now();
    let (mut prover, verifier) = ivc::setup::<ProofAggregation>(ivc_srs, IVC_K, inner_ctx.clone());
    println!("IVC setup completed in {:.2?}", start.elapsed());

    // Aggregation steps.
    for i in 0..STEPS {
        let ivc_witness = AggregationWitness {
            inner_statement: inner_statements[i],
            inner_proof: inner_proofs[i].clone(),
        };

        let start = Instant::now();
        let ivc_proof = prover.prove_step(ivc_witness).unwrap();
        let prove_time = start.elapsed();

        let ivc_instance = prover.instance();
        let start = Instant::now();
        verifier.verify(&inner_ctx, &ivc_instance, &ivc_proof).unwrap();
        let verify_time = start.elapsed();

        println!("Step {i}: IVC prove {prove_time:.2?}, verify {verify_time:.2?}");
    }

    let final_state = prover.instance().state().clone();
    println!("\nAggregated {STEPS} SHA-256 proofs.");
    for (i, stmt) in final_state.statements.iter().enumerate() {
        let hex: String = stmt.iter().map(|b| format!("{b:02x}")).collect();
        println!("  {i}: {hex}");
    }
    println!("Statements hash: {:?}", final_state.statements_hash);
}
