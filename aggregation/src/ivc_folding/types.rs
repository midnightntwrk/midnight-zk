//! Instances, proofs and the public-input encoding of the folding IVC.

use std::time::Duration;

use ff::Field;
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::hash::HashCPU,
    types::Instantiable,
    verifier::{AssignedVk, CommitmentBases, NativeAccumulator, accumulator_as_public_input},
};
use midnight_proofs::{plonk::VerifyingKey, transcript::CircuitTranscript};
use midnight_zk_stdlib::DefaultPCS;

use crate::ivc::{F, Ivc, S};

/// The off-circuit folding accumulator.
pub type FoldingAccumulator = NativeAccumulator<S>;

/// Fiat-Shamir transcript of partial proofs, folding proofs and the decider.
pub(crate) type Tr = CircuitTranscript<PoseidonState<F>>;

/// The public instance of the folding IVC: the current state and the
/// running accumulator, `None` for the default accumulator of the step right
/// after genesis (see the module documentation).
#[derive(Clone, Debug)]
pub struct FoldingIvcInstance<T: Ivc> {
    pub(crate) state: T::State,
    pub(crate) acc: Option<FoldingAccumulator>,
}

impl<T: Ivc> FoldingIvcInstance<T> {
    /// Returns the current state.
    pub fn state(&self) -> &T::State {
        &self.state
    }

    /// Returns the running accumulator (`None`: default accumulator).
    pub fn accumulator(&self) -> Option<&FoldingAccumulator> {
        self.acc.as_ref()
    }

    /// Size in bytes of the serialized accumulator: compressed points (48
    /// bytes) and scalars (32 bytes). `0` for the default accumulator.
    pub fn accumulator_size(&self) -> usize {
        self.acc.as_ref().map_or(0, |acc| {
            let inst = acc.instance();
            let nb_points =
                inst.phase1_commitment().bases().len() + inst.phase2_commitment().bases().len();
            let c = inst.challenges();
            let nb_scalars = inst.instances().iter().map(Vec::len).sum::<usize>()
                + c.theta.len()
                + 2
                + c.trash_powers.len()
                + c.y.len()
                + acc.betas().len()
                + 1;
            48 * nb_points + 32 * nb_scalars
        })
    }
}

/// Proof of a [`FoldingIvcInstance`]: the partial proof of the last step
/// (its commit phases), the folding proof of that instance into the
/// accumulator (empty if the accumulator is the default one) and the decider
/// proof of the result.
#[derive(Clone, Debug)]
pub struct FoldingIvcProof {
    /// Partial proof (phase-1/2 commitments) of the last step.
    pub partial_proof: Vec<u8>,
    /// Folding messages (`F`, `K`) of the last fold.
    pub folding_proof: Vec<u8>,
    /// Decider proof of the final accumulator.
    pub decider_proof: Vec<u8>,
}

/// Prover timings of one IVC step.
#[derive(Clone, Copy, Debug)]
pub struct StepTimings {
    /// Native folding of the previous instance into the accumulator.
    pub fold: Duration,
    /// Synthesis and commit phases of the step circuit.
    pub commit: Duration,
}

/// Prover timings of [`super::FoldingIvcProver::finalize`].
#[derive(Clone, Copy, Debug)]
pub struct FinalTimings {
    /// Native folding of the last instance into the accumulator.
    pub fold: Duration,
    /// Decider proof of the final accumulator.
    pub decider: Duration,
}

fn poseidon(inputs: &[F]) -> F {
    <PoseidonChip<F> as HashCPU<F, F>>::hash(inputs)
}

/// Hash binding an accumulator; `0` for the default accumulator.
pub(crate) fn accumulator_hash(acc: Option<&FoldingAccumulator>) -> F {
    acc.map_or(F::ZERO, |acc| {
        poseidon(&accumulator_as_public_input::<S>(acc))
    })
}

/// The public inputs of a step: `[vk_repr, H(state ‖ acc_hash)]`.
pub(crate) fn step_public_inputs<T: Ivc>(
    vk: &VerifyingKey<F, DefaultPCS>,
    state: &T::State,
    acc_hash: F,
) -> Vec<F> {
    let state_hash = poseidon(&[T::format_public_input(state), vec![acc_hash]].concat());
    [AssignedVk::<S>::as_public_input(vk), vec![state_hash]].concat()
}
