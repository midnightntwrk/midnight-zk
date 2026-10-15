//! Step circuit of the folding IVC and its [`Relation`] implementation.
//!
//! Step `i` proves `next = transition(prev)` and that the accumulator of its
//! public input is the folding of the previous accumulator with the
//! instance of step `i − 1` (genesis handling in the module documentation).

use ff::Field;
use midnight_circuits::{
    instructions::{
        AssignmentInstructions, BinaryInstructions, ControlFlowInstructions,
        PublicInputInstructions,
    },
    types::{AssignedBit, AssignedNative},
    verifier::{AssignedVk, FoldingShape},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, VerifyingKey},
};
use midnight_zk_stdlib::{DefaultPCS, Relation, ZkStdLib, ZkStdLibArch};

use super::types::{FoldingAccumulator, step_public_inputs};
use crate::ivc::{F, Ivc, IvcCircuit, IvcError, S};

/// Number of public inputs of a step: `vk_repr` (3) and one hash.
pub(crate) const NB_PUBLIC_INPUTS: usize = 4;

/// The instance of [`FoldingIvcCircuit`]: the circuit's own verifying key,
/// the next state and the hash of the next accumulator (`0` for the default
/// one). Public inputs: `[vk_repr, H(state ‖ acc_hash)]`.
#[derive(Clone, Debug)]
pub struct FoldingIvcStepInstance<T: Ivc> {
    pub(crate) vk: VerifyingKey<F, DefaultPCS>,
    pub(crate) state: T::State,
    pub(crate) acc_hash: F,
}

/// The private witness of one step.
#[derive(Clone, Debug)]
pub struct FoldingIvcWitness<T: Ivc> {
    /// The state before the transition.
    pub(crate) prev_state: T::State,
    /// The previous accumulator (a dummy one when it is the default one).
    pub(crate) prev_acc: FoldingAccumulator,
    /// Whether the previous accumulator is the default one (the previous
    /// step was the genesis step), so that the previous instance initialises
    /// the accumulator instead of being folded into it.
    pub(crate) is_first: bool,
    /// Partial proof of the previous step (dummy at genesis).
    pub(crate) partial_proof: Vec<u8>,
    /// Folding messages of the previous instance (dummy unless folding).
    pub(crate) folding_proof: Vec<u8>,
    pub(crate) transition_witness: T::Witness,
}

/// The step circuit of the folding IVC, parameterized by a transition `T`.
#[derive(Clone, Debug)]
pub struct FoldingIvcCircuit<T: Ivc> {
    k: u32,
    cs: ConstraintSystem<F>,
    shape: FoldingShape,
    ctx: T::Context,
}

impl<T: Ivc> FoldingIvcCircuit<T> {
    /// Configures the step circuit for `2^k` rows.
    pub fn new(k: u32, ctx: T::Context) -> Self {
        let mut cs = ConstraintSystem::default();
        ZkStdLib::configure(&mut cs, (Self::arch(), (k - 1) as u8));
        let cs = cs.into_finalized();
        // Instance columns: the (empty) committed-instance column and the
        // public inputs.
        let shape = FoldingShape::new::<S>(&cs, k, &[0, NB_PUBLIC_INPUTS]);
        FoldingIvcCircuit { k, cs, shape, ctx }
    }

    /// The log2 of the number of rows.
    pub fn k(&self) -> u32 {
        self.k
    }

    /// The shape of the folded relation (the step circuit itself).
    pub(crate) fn shape(&self) -> &FoldingShape {
        &self.shape
    }

    /// The finalized constraint system.
    pub(crate) fn cs(&self) -> &ConstraintSystem<F> {
        &self.cs
    }

    /// Returns a reference to the context.
    pub fn ctx(&self) -> &T::Context {
        &self.ctx
    }

    /// The [ZkStdLibArch] of the step circuit (the SNARK-verifier IVC's).
    pub fn arch() -> ZkStdLibArch {
        // Two degree-1 lookup tuples per helper (bound 3) instead of four:
        // folding degree 7 instead of 10, for more helper columns.
        ZkStdLibArch {
            lookup_chunk_bound: Some(3),
            // Wider arith/range layout: fewer rows; advice count stays 15 (set by the BLS12-381 ECC chip).
            nb_arith_cols: 11,
            nr_pow2range_cols: 10,
            ..IvcCircuit::<T>::arch()
        }
    }

    /// `H(state ‖ acc_hash)`, in-circuit analog of the last public input in
    /// [`step_public_inputs`].
    fn state_hash(
        std_lib: &ZkStdLib,
        ivc_gadget: &T,
        layouter: &mut impl Layouter<F>,
        state: &T::AssignedState,
        acc_hash: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let mut inputs = ivc_gadget.as_public_input(layouter, state)?;
        inputs.push(acc_hash.clone());
        std_lib.poseidon(layouter, &inputs)
    }
}

impl<T: Ivc> Relation for FoldingIvcCircuit<T> {
    type Instance = FoldingIvcStepInstance<T>;

    type Witness = FoldingIvcWitness<T>;

    type Error = IvcError;

    fn used_chips(&self) -> ZkStdLibArch {
        Self::arch()
    }

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, IvcError> {
        Ok(step_public_inputs::<T>(
            &instance.vk,
            &instance.state,
            instance.acc_hash,
        ))
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), IvcError> {
        let verifier_gadget = std_lib.verifier();
        let folding = std_lib.folding(self.shape.clone());
        let ivc_gadget = T::new(std_lib.clone(), &self.ctx);
        let curve_chip = std_lib.bls12_381();

        let vk: AssignedVk<S> = verifier_gadget.assign_vk_as_public_input(
            layouter,
            instance.as_ref().map(|x| &x.vk),
            &self.cs,
        )?;
        let vk_pi = verifier_gadget.as_public_input(layouter, &vk)?;

        let prev_state =
            ivc_gadget.assign(layouter, witness.as_ref().map(|w| w.prev_state.clone()))?;
        let next_state = ivc_gadget.circuit_transition(
            layouter,
            &prev_state,
            witness.as_ref().map(|w| w.transition_witness.clone()),
        )?;
        let is_genesis =
            ivc_gadget.circuit_is_genesis(std_lib, layouter, &self.ctx, &prev_state)?;
        let is_first: AssignedBit<F> =
            std_lib.assign(layouter, witness.as_ref().map(|w| w.is_first))?;
        let zero: AssignedNative<F> = std_lib.assign_fixed(layouter, F::ZERO)?;

        // The previous step's instance: its public input binds `prev_state`
        // and the previous accumulator (hash 0 if it is the default one).
        let prev_acc =
            folding.assign_accumulator(layouter, witness.as_ref().map(|w| &w.prev_acc))?;
        let prev_acc_pi = prev_acc.as_public_input(layouter, curve_chip)?;
        let prev_acc_hash = std_lib.poseidon(layouter, &prev_acc_pi)?;
        let prev_acc_hash = std_lib.select(layouter, &is_first, &zero, &prev_acc_hash)?;
        let prev_hash =
            Self::state_hash(std_lib, &ivc_gadget, layouter, &prev_state, &prev_acc_hash)?;
        let prev_pi = [vk_pi, vec![prev_hash]].concat();
        let fresh = folding.read_instance(
            layouter,
            &vk,
            &[&[], &prev_pi],
            witness.as_ref().map(|w| w.partial_proof.clone()),
        )?;

        // Next accumulator: init (previous accumulator is the default one) or
        // fold; both are computed and the result is selected.
        let init_acc = folding.init(layouter, fresh.clone())?;
        // The fold is discarded at the first step (the init is selected) and at
        // genesis (the default accumulator): there the dummy folding proof need
        // not carry the right commitment products, and the fold transcript
        // absorbs `prev_acc_hash = 0` instead of a hash of the dummy
        // accumulator, which is sound as the result is not used.
        let discarded = std_lib.or(layouter, &[is_first.clone(), is_genesis.clone()])?;
        let fold_acc = folding.fold(
            layouter,
            &prev_acc,
            &prev_acc_hash,
            &fresh,
            witness.map(|w| w.folding_proof),
            Some(&discarded),
        )?;
        let init_pi = init_acc.as_public_input(layouter, curve_chip)?;
        let fold_pi = fold_acc.as_public_input(layouter, curve_chip)?;
        let next_acc_pi = (init_pi.iter().zip(fold_pi.iter()))
            .map(|(i, f)| std_lib.select(layouter, &is_first, i, f))
            .collect::<Result<Vec<_>, Error>>()?;
        let next_acc_hash = std_lib.poseidon(layouter, &next_acc_pi)?;

        // At genesis there is no previous instance: the next accumulator is
        // the default one.
        let next_acc_hash = std_lib.select(layouter, &is_genesis, &zero, &next_acc_hash)?;
        let next_hash =
            Self::state_hash(std_lib, &ivc_gadget, layouter, &next_state, &next_acc_hash)?;
        std_lib.constrain_as_public_input(layouter, &next_hash)?;
        Ok(())
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        T::write_context(&self.ctx, writer)
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut k_bytes = [0u8; 4];
        reader.read_exact(&mut k_bytes)?;
        let k = u32::from_le_bytes(k_bytes);
        let ctx = T::read_context(reader)?;
        Ok(Self::new(k, ctx))
    }
}
