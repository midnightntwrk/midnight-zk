//! IVC circuit definition and [`Relation`] implementation.
//!
//! The circuit proves a single IVC step: given a previous state, a transition
//! witness and a proof that the previous state was itself valid, it verifies
//! the prior proof, applies the transition, and produces a new accumulator
//! that attests to the entire chain up to the new state.
//!
//! The genesis case is handled specially: when the previous state is genesis,
//! there is no meaningful prior proof to verify, so the circuit substitutes a
//! default accumulator that satisfies the verification invariant.

use std::collections::BTreeMap;

use group::Group;
use midnight_circuits::{
    hash::poseidon::PoseidonState,
    instructions::{AssignmentInstructions, BinaryInstructions, PublicInputInstructions},
    types::{AssignedNative, Instantiable},
    verifier::{
        fixed_bases, Accumulator, AssignedAccumulator, AssignedKZGCommitment, AssignedVk,
        SelfEmulation,
    },
};
use midnight_proofs::{
    circuit::{Layouter, Value}, plonk::{self, ConstraintSystem, Error, VerifyingKey}, poly::{
        EvaluationDomain, PolynomialLabel, kzg::{KZGCommitmentScheme, commitment::KZGCommitment},
    }, transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{decidable::Decidable, Relation, ZkStdLib, ZkStdLibArch};

use super::{Ivc, IvcError, C, E, F, S};

/// The public instance (statement) of an IVC proof.
///
/// Contains:
/// - a commitment to the verifying key (of the IVC circuit itself),
/// - the current state (after the latest transition),
/// - the accumulator (that summarises all prior steps).
///
/// **Important:** the `vk_repr` field must **not** be trusted as-is. The
/// verifier must compare it against the canonical `vk_repr` obtained by
/// running [`setup`](super::setup()).
/// See [`IvcVerifier::verify`](super::IvcVerifier::verify) for details.
#[derive(Clone, Debug)]
pub struct IvcInstance<T: Ivc> {
    pub(crate) vk_repr: F,
    pub(crate) state: T::State,
    pub(crate) acc: Accumulator<S>,
}

impl<T: Ivc> IvcInstance<T> {
    /// Returns the current state.
    pub fn state(&self) -> &T::State {
        &self.state
    }

    /// Returns the accumulator carried by this instance.
    pub fn acc(&self) -> &Accumulator<S> {
        &self.acc
    }
}

/// The private witness for a single IVC step.
///
/// Contains:
/// - a previous state (input to the transition),
/// - a previous accumulator (summarises all steps up to the previous state),
/// - a proof asserting the validity of the previous step (if not genesis),
/// - a transition witness (input that drives the state change).
#[derive(Clone, Debug)]
pub struct IvcWitness<T: Ivc> {
    pub(crate) prev_state: T::State,
    pub(crate) prev_acc: Accumulator<S>,
    pub(crate) prev_proof: Vec<u8>,
    pub(crate) transition_witness: T::Witness,
}

/// The IVC circuit, parameterized by a transition function `T`.
///
/// Implements the [`Relation`] of the IVC logic. Namely, that for a given
/// [`IvcInstance`] `(vk_repr, state, acc)` there exists an [`IvcWitness`]
/// `(prev_state, prev_acc, prev_proof, transition_witness)` such that:
///
/// 1. `state` is the result of applying the transition function to `prev_state`
///    with `transition_witness`,
/// 2. `prev_state` is genesis OR `prev_proof` is a valid proof (under
///    `vk_repr`) for the instance `(vk_repr, prev_state, prev_acc)`, attesting
///    that `prev_state` was itself reached legitimately,
/// 3. `acc` is the accumulation of `prev_acc` with the accumulator resulting
///    from verifying `prev_proof`.
#[derive(Clone, Debug)]
pub struct IvcCircuit<T: Ivc> {
    domain: EvaluationDomain<F>,
    cs: ConstraintSystem<F>,
    ctx: T::Context,
}

impl<T: Ivc> IvcCircuit<T> {
    /// Creates a new IVC circuit.
    ///
    /// The `ctx` contains metadata that parametrizes the IVC computation
    /// (transition function). See [`IvcContext`](super::IvcContext).
    pub fn new(domain: EvaluationDomain<F>, cs: ConstraintSystem<F>, ctx: T::Context) -> Self {
        IvcCircuit { domain, cs, ctx }
    }

    /// Returns a reference to the context.
    pub fn ctx(&self) -> &T::Context {
        &self.ctx
    }

    /// The [ZkStdLibArch] for the IVC circuit, combining the transition's
    /// requirements with the verifier's (bls12_381 and poseidon).
    pub fn arch() -> ZkStdLibArch {
        let mut arch = T::arch();
        arch.bls12_381 = true;
        arch.poseidon = true;
        arch
    }

    /// Returns the constraint-system degree of the IVC circuit.
    pub fn cs_degree() -> usize {
        midnight_zk_stdlib::cs_degree(Self::arch())
    }
}

type PlonkVk = VerifyingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>>;

/// The IVC circuit's per-step decider: **prepare-only** partial verification of a
/// step's proof.
#[derive(Clone, Copy, Debug, Default)]
pub struct IvcDecider;

impl Decidable for IvcDecider {
    type Vk = PlonkVk;
    type AssignedVk = AssignedVk<S>;

    fn decide(
        vk: &Self::Vk,
        committed_instance: &[KZGCommitment<midnight_curves::Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error> {
        let fixed_bases = fixed_bases::<S>(vk);
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(proof);
        let dual_msm =
            plonk::prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                vk,
                committed_instance,
                instance,
                &mut transcript,
            )?;
            
        Ok(Some(Accumulator::from_dual_msm(dual_msm, &fixed_bases)))
    }

    fn in_circuit_decide(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &Self::AssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error> {
        let acc = std_lib.verifier().prepare(layouter, vk, committed_instance, instance, proof)?;
        Ok(Some(acc))
    }
}

/// Off-circuit verifying context for *finalizing* an IVC chain: the IVC PLONK
/// verifying key plus the (structured) accumulator carried in the proof's public
/// inputs.
#[derive(Clone, Debug)]
pub struct IvcFinalVk {
    /// Circuit VK
    pub vk: PlonkVk,
    /// Accumulator from the IVC instance
    pub accumulator: Accumulator<S>,
}

/// In-circuit analog of [`IvcFinalVk`].
#[derive(Clone, Debug)]
pub struct IvcAssignedFinalVk {
    /// Assigned VK.
    pub vk: AssignedVk<S>,
    /// Assigned accumulator from the IVC instance.
    pub carried_acc: AssignedAccumulator<S>,
    /// Assigned fixed bases map.
    pub fixed_bases: BTreeMap<PolynomialLabel, <S as SelfEmulation>::AssignedPoint>,
}

/// IVC final decider. Updates the state (as per the step function) once, and
/// collapses the MSM (including the fixed bases) into a collapsed MSM. 
#[derive(Clone, Copy, Debug, Default)]
pub struct IvcFinalDecider {}

impl Decidable for IvcFinalDecider {
    type Vk = IvcFinalVk;
    type AssignedVk = IvcAssignedFinalVk;

    fn decide(
        vk: &Self::Vk,
        committed_instance: &[KZGCommitment<midnight_curves::Bls12>],
        instance: &[&[F]],
        proof: &[u8],
    ) -> Result<Option<Accumulator<S>>, Error> {
        let proof_acc = IvcDecider::decide(&vk.vk, committed_instance, instance, proof)?
            .expect("IvcDecider always yields an accumulator");
        let mut next_acc = Accumulator::accumulate(&[proof_acc, vk.accumulator.clone()]);
        next_acc.collapse();
        next_acc.resolve_fixed_bases(&fixed_bases::<S>(&vk.vk));
        Ok(Some(next_acc))
    }

    fn in_circuit_decide(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        vk: &Self::AssignedVk,
        committed_instance: &[AssignedKZGCommitment<S>],
        instance: &[&[AssignedNative<F>]],
        proof: Value<Vec<u8>>,
    ) -> Result<Option<AssignedAccumulator<S>>, Error> {
        let bls = std_lib.bls12_381();

        let proof_acc =
            IvcDecider::in_circuit_decide(std_lib, layouter, &vk.vk, committed_instance, instance, proof)?
                .expect("IvcDecider always yields an accumulator");
        let mut next_acc = std_lib.verifier().accumulate(layouter, &[proof_acc, vk.carried_acc.clone()])?;
        next_acc.collapse(layouter, bls, bls.scalar_field_chip())?;
        next_acc.resolve_fixed_bases(&vk.fixed_bases);

        Ok(Some(next_acc))
    }
}

impl<T: Ivc> Relation for IvcCircuit<T> {
    type Instance = IvcInstance<T>;

    type Witness = IvcWitness<T>;

    type Error = IvcError;

    fn used_chips(&self) -> ZkStdLibArch {
        Self::arch()
    }

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, IvcError> {
        Ok([
            vec![instance.vk_repr],
            T::format_public_input(&instance.state),
            AssignedAccumulator::<S>::as_public_input(&instance.acc),
        ]
        .concat())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), IvcError> {
        let verifier_gadget = std_lib.verifier();
        let ivc_gadget = T::new(std_lib.clone(), &self.ctx);

        let assigned_self_vk: AssignedVk<S> = verifier_gadget.assign_vk_as_public_input(
            layouter,
            &self.domain,
            &self.cs,
            instance.as_ref().map(|x| x.vk_repr),
        )?;

        let prev_state_val = witness.as_ref().map(|w| w.prev_state.clone());
        let prev_state = ivc_gadget.assign(layouter, prev_state_val)?;

        let next_state = ivc_gadget.circuit_transition(
            layouter,
            &prev_state,
            witness.as_ref().map(|w| w.transition_witness.clone()),
        )?;
        ivc_gadget.constrain_as_public_input(layouter, &next_state)?;

        let fixed_base_labels = midnight_circuits::verifier::fixed_base_labels::<S>(
            self.cs.num_fixed_columns() + self.cs.num_selectors(),
            self.cs.permutation().columns.len(),
        );

        let prev_acc_value = witness.as_ref().map(|w| w.prev_acc.clone());
        let prev_acc = verifier_gadget.assign_collapsed_accumulator(
            layouter,
            &fixed_base_labels,
            prev_acc_value,
        )?;

        let prev_proof_pi = [
            verifier_gadget.as_public_input(layouter, &assigned_self_vk)?,
            ivc_gadget.as_public_input(layouter, &prev_state)?,
            verifier_gadget.as_public_input(layouter, &prev_acc)?,
        ]
        .concat();

        let instance_com = AssignedKZGCommitment::simple(
            std_lib.bls12_381().assign_fixed(layouter, C::identity())?,
            PolynomialLabel::CommittedInstance(0),
        );

        // Verify a witnessed proof that ensures the validity of `prev_state`.
        // The proof is valid iff `prev_proof_acc` satisfies the invariant.
        let mut prev_proof_acc = IvcDecider::in_circuit_decide(
            std_lib,
            layouter,
            &assigned_self_vk,
            &[instance_com],
            &[&prev_proof_pi],
            witness.map(|w| w.prev_proof),
        )?
        .expect("IvcDecider always yields an accumulator");

        // If `prev_state` is genesis, the provided accumulator is discarded/multiplied
        // by 0 so that it trivially satisfies the invariant.

        let is_not_genesis = {
            let b = ivc_gadget.circuit_is_genesis(std_lib, layouter, &self.ctx, &prev_state)?;
            std_lib.not(layouter, &b)?
        };
        AssignedAccumulator::scale_by_bit(
            layouter,
            std_lib.bls12_381().scalar_field_chip(),
            &is_not_genesis,
            &mut prev_proof_acc,
        )?;

        let mut next_acc = verifier_gadget.accumulate(layouter, &[prev_proof_acc, prev_acc])?;

        next_acc.collapse(
            layouter,
            std_lib.bls12_381(),
            std_lib.bls12_381().scalar_field_chip(),
        )?;

        verifier_gadget.constrain_as_public_input(layouter, &next_acc)?;
        Ok(())
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.domain.k().to_le_bytes())?;
        T::write_context(&self.ctx, writer)
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut k_bytes = [0u8; 4];
        reader.read_exact(&mut k_bytes)?;
        let k = u32::from_le_bytes(k_bytes);

        let ctx = T::read_context(reader)?;

        let mut cs = ConstraintSystem::default();
        ZkStdLib::configure(&mut cs, (Self::arch(), (k - 1) as u8));
        let domain = EvaluationDomain::new(cs.degree() as u32, k);

        Ok(IvcCircuit { domain, cs, ctx })
    }
}
