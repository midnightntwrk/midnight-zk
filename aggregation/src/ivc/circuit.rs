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

use group::Group;
use midnight_circuits::{
    instructions::{AssignmentInstructions, BinaryInstructions, PublicInputInstructions},
    types::Instantiable,
    verifier::{Accumulator, AssignedAccumulator, AssignedVk},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error},
    poly::EvaluationDomain,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};

use super::{Ivc, C, F, S};

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
}

impl<T: Ivc> Relation for IvcCircuit<T> {
    type Instance = IvcInstance<T>;

    type Witness = IvcWitness<T>;

    type Error = Error;

    fn used_chips(&self) -> ZkStdLibArch {
        Self::arch()
    }

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
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
    ) -> Result<(), Error> {
        let verifier_gadget = std_lib.verifier();
        let ivc_gadget = T::new(std_lib.clone(), &self.ctx);

        let assigned_self_vk: AssignedVk<S> = verifier_gadget.assign_vk_as_public_input(
            layouter,
            "self_vk",
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

        let fixed_base_names = midnight_circuits::verifier::fixed_base_names::<S>(
            "self_vk",
            self.cs.num_fixed_columns() + self.cs.num_selectors(),
            self.cs.permutation().columns.len(),
        );

        let prev_acc_value = witness.as_ref().map(|w| w.prev_acc.clone());
        let prev_acc = verifier_gadget.assign_collapsed_accumulator(
            layouter,
            &fixed_base_names,
            prev_acc_value,
        )?;

        let prev_proof_pi = [
            verifier_gadget.as_public_input(layouter, &assigned_self_vk)?,
            ivc_gadget.as_public_input(layouter, &prev_state)?,
            verifier_gadget.as_public_input(layouter, &prev_acc)?,
        ]
        .concat();

        let id_point = std_lib.bls12_381_curve().assign_fixed(layouter, C::identity())?;

        // Verify a witnessed proof that ensures the validity of `prev_state`.
        // The proof is valid iff `prev_proof_acc` satisfies the invariant.
        let mut prev_proof_acc = verifier_gadget.prepare(
            layouter,
            &assigned_self_vk,
            &[id_point],
            &[&prev_proof_pi],
            witness.map(|w| w.prev_proof),
        )?;

        // If `prev_state` is genesis, the provided accumulator is discarded/multiplied
        // by 0 so that it trivially satisfies the invariant.
        let is_genesis = ivc_gadget.is_genesis(layouter, &prev_state)?;
        let is_not_genesis = std_lib.not(layouter, &is_genesis)?;
        AssignedAccumulator::scale_by_bit(
            layouter,
            std_lib.bls12_381_scalar(),
            &is_not_genesis,
            &mut prev_proof_acc,
        )?;

        let mut next_acc = verifier_gadget.accumulate(layouter, &[prev_proof_acc, prev_acc])?;

        next_acc.collapse(
            layouter,
            std_lib.bls12_381_curve(),
            std_lib.bls12_381_scalar(),
        )?;

        verifier_gadget.constrain_as_public_input(layouter, &next_acc)
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
