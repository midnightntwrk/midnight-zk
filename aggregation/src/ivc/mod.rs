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

/// External configuration for an IVC computation.
///
/// The context carries any metadata that the transition function needs.
/// Consider moving immutable state values (e.g. verification keys, domain
/// parameters) into the context rather than recomputing them at each step
/// or carrying them in the state.
pub trait IvcContext: Clone {
    /// The external configuration threaded through the IVC framework.
    /// Use `()` when no context is required.
    type Context: Clone + std::fmt::Debug;

    /// Constructs the in-circuit gadget from a [`ZkStdLib`] and the provided
    /// context.
    fn new(std_lib: ZkStdLib, ctx: &Self::Context) -> Self;

    /// Serializes the context to a writer.
    fn write_context<W: std::io::Write>(ctx: &Self::Context, writer: &mut W)
        -> std::io::Result<()>;

    /// Deserializes a context from a reader.
    fn read_context<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self::Context>;
}

/// State representation for an Incrementally Verifiable Computation (IVC).
///
/// An IVC state evolves from a distinguished *genesis* value through repeated
/// applications of a transition function (see [`IvcTransition`]). This trait
/// captures the state type together with the ability to detect genesis, which
/// the IVC circuit needs to handle the very first step.
pub trait IvcState:
    IvcContext
    + AssignmentInstructions<F, Self::AssignedState>
    + PublicInputInstructions<F, Self::AssignedState>
{
    /// The native (off-circuit) state type.
    type State: Clone;

    /// The in-circuit state type.
    type AssignedState: Clone + Instantiable<F> + InnerValue<Element = Self::State>;

    /// The genesis (initial) state of the IVC chain.
    fn genesis(ctx: &Self::Context) -> Self::State;

    /// Returns true (in-circuit) if the given state is genesis.
    fn is_genesis(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<AssignedBit<F>, Error>;

    /// Off-circuit check that the state meets the required invariants.
    ///
    /// Automatically called by [`IvcVerifier::verify`] to check any
    /// properties that are deferred to off-circuit verification, such as
    /// accumulator validity or hash-chain integrity.
    ///
    /// Returns `true` if the state passes all checks.
    fn decider(ctx: &Self::Context, state: &Self::State) -> bool;
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
    fn transition(ctx: &Self::Context, state: &Self::State, witness: Self::Witness) -> Self::State;

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
