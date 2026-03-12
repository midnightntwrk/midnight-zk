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
    types::{AssignedBit, AssignedNative},
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
///
/// [`State`](Self::State) and [`AssignedState`](Self::AssignedState) both
/// represent the same logical state, but [`State`](Self::State) may carry
/// additional data (e.g. variable-length collections) that cannot be
/// represented in constant size inside the circuit.
/// [`AssignedState`](Self::AssignedState) is its constant-size in-circuit
/// counterpart. When extra data is present, [`State`](Self::State) stores
/// both the full data *and* constant-size summaries of it (e.g. hashes or
/// commitments) that bind to the full data.
/// [`AssignedState`](Self::AssignedState) contains only these summaries,
/// which are exactly the fields that get assigned into the circuit.
/// A collision-resistant hash, for example, ensures that no two distinct
/// [`State`](Self::State) values map to the same
/// [`AssignedState`](Self::AssignedState), so that
/// [`AssignedState`](Self::AssignedState) computationally determines
/// [`State`](Self::State).
pub trait IvcState: IvcContext {
    /// The native (off-circuit) state type.
    ///
    /// It may contain data whose size grows over time (e.g. a list of
    /// aggregated statements) together with constant-size summaries of that
    /// data (e.g. hashes or commitments). These summaries are the same fields
    /// that [`AssignedState`](Self::AssignedState) contains.
    type State: Clone;

    /// The constant-size in-circuit state type.
    ///
    /// It must uniquely determine [`State`](Self::State) (at least
    /// computationally), e.g. by including hashes or binding commitments of
    /// any data in [`State`](Self::State) that cannot be directly represented
    /// in constant size inside the circuit.
    type AssignedState: Clone;

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
    /// In particular, when [`State`](Self::State) contains data that
    /// does not appear directly in [`AssignedState`](Self::AssignedState)
    /// but only through a hash or commitment, this function must verify
    /// that the summary stored in [`State`](Self::State) (e.g. a hash
    /// field) is consistent with the full data it summarises.
    ///
    /// Returns `true` if the state passes all checks.
    fn decider(ctx: &Self::Context, state: &Self::State) -> bool;
}

/// Input/output interface for IVC state values.
///
/// Bridges [`State`](IvcState::State) and
/// [`AssignedState`](IvcState::AssignedState): assigning native values into the
/// circuit, constraining them as public inputs, and formatting them as
/// raw native field elements for the public-input vector.
pub trait IvcIO: IvcState {
    /// Assigns a [`State`](IvcState::State) value as a private input,
    /// producing the corresponding [`AssignedState`](IvcState::AssignedState).
    ///
    /// Only the constant-size portion of the state is assigned; any
    /// variable-size data in [`State`](IvcState::State) that is only
    /// represented through a hash or commitment is not materialised in the
    /// resulting [`AssignedState`](IvcState::AssignedState).
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Self::State>,
    ) -> Result<Self::AssignedState, Error>;

    /// Constrains the assigned state as a public input to the circuit.
    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<(), Error>;

    /// Returns the cells of the assigned state formatted as public input
    /// (in-circuit analog of
    /// [`format_public_input`](Self::format_public_input)).
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error>;

    /// Formats a [`State`](IvcState::State) as raw native field elements
    /// (off-circuit analog of [`as_public_input`](Self::as_public_input)).
    fn format_public_input(state: &Self::State) -> Vec<F>;
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
    /// and returns the assigned next state.
    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error>;
}

/// Convenience trait combining [`IvcTransition`] and [`IvcIO`].
///
/// Automatically implemented for any type that implements both. This is the
/// bound required by the IVC machinery ([`IvcCircuit`], [`IvcProver`],
/// [`IvcVerifier`], [`setup`]).
pub trait Ivc: IvcTransition + IvcIO {}
impl<I: IvcTransition + IvcIO> Ivc for I {}
