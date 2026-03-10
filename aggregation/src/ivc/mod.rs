//! Incrementally Verifiable Computation (IVC).
//!
//! This module provides a framework for producing succinct proofs that a given
//! state is the result of applying a chain of transitions to a genesis state:
//!
//! ```text
//! genesis --w0--> s1 --w1--> s2 --w2--> ... --wN--> sN
//! ```
//!
//! Each transition step consumes a (secret) witness `wi` and advances the
//! state. The resulting proof attests that the final state `sN` was reached
//! legitimately without revealing any of the intermediate states or witnesses.
//!
//! Crucially, the proof size and verification time are *constant* regardless of
//! the number of steps `N`: the prover folds each new step into the existing
//! proof incrementally rather than proving the entire chain from scratch.
//!
//! Note that `N` (the number of steps) is **not** revealed by the proof. If
//! the chain length is relevant, it can be tracked by including a counter in
//! the state that the transition function increments at each step.

pub use circuit::{IvcCircuit, IvcInstance, IvcWitness};
pub use error::IvcError;
use midnight_circuits::{
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedBit, InnerValue, Instantiable},
    verifier::{BlstrsEmulation, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};
pub use prover::IvcProver;
pub use setup::setup;
pub use verifier::IvcVerifier;

pub(crate) type S = BlstrsEmulation;
pub(crate) type F = <S as SelfEmulation>::F;
pub(crate) type C = <S as SelfEmulation>::C;
pub(crate) type E = <S as SelfEmulation>::Engine;

pub mod circuit;
pub mod error;
pub mod prover;
pub mod setup;
pub mod verifier;

/// State representation for an Incrementally Verifiable Computation (IVC).
///
/// An IVC state evolves from a distinguished *genesis* value through repeated
/// applications of a transition function (see [`IvcTransition`]). This trait
/// captures the state type together with the ability to detect genesis, which
/// the IVC circuit needs to handle the very first step.
///
/// Implementors must be constructable from a [`ZkStdLib`] (via [`From`])
/// so that the IVC circuit can instantiate the gadget.
pub trait IvcState:
    Clone
    + From<ZkStdLib>
    + AssignmentInstructions<F, Self::AssignedState>
    + PublicInputInstructions<F, Self::AssignedState>
{
    /// The native (off-circuit) state type.
    type State: Clone;

    /// The in-circuit state type.
    type AssignedState: Clone + Instantiable<F> + InnerValue<Element = Self::State>;

    /// The genesis (initial) state of the IVC chain.
    fn genesis() -> Self::State;

    /// Returns true (in-circuit) if the given state is genesis.
    fn is_genesis(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<AssignedBit<F>, Error>;
}

/// A single-step transition function for an IVC computation.
///
/// Defines how an [`IvcState`] evolves:
/// [`transition`](Self::transition) computes the next state off-circuit,
/// while [`circuit_transition`](Self::circuit_transition) computes the
/// same transition inside the circuit, returning the new assigned state.
pub trait IvcTransition: IvcState {
    /// The witness type for a single transition step.
    type Witness: Clone;

    /// The [ZkStdLibArch] required by the transition function.
    fn arch() -> ZkStdLibArch;

    /// Computes the next state from the current state and witness
    /// (off-circuit).
    fn transition(state: &Self::State, witness: Self::Witness) -> Self::State;

    /// Computes the next state in-circuit from the current state and witness.
    ///
    /// This is the in-circuit analog of [`transition`](Self::transition). It
    /// receives the assigned current state and a witnessed transition input,
    /// and returns the assigned next state. The IVC circuit will constrain
    /// the returned state as public input.
    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error>;
}
