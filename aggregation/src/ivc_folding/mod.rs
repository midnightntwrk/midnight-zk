//! Incrementally Verifiable Computation with Protogalaxy folding.
//!
//! Same interface as [`crate::ivc`] (any [`Ivc`](crate::ivc::Ivc)
//! transition), but the step circuit runs the in-circuit *folding* verifier
//! instead of a SNARK verifier, and a step never produces a proof: only the
//! commit phases of the step circuit (its *partial proof*). The previous
//! step's instance is folded into a running accumulator, natively by the
//! prover and in-circuit by the next step. The only full proof is the
//! decider of the final accumulator
//! (`midnight_proofs::plonk::protogalaxy`).
//!
//! The step circuit's proofs are committed with [`FoldingPCS`] (fflonk over
//! KZG with `T_MAX = 16`), which the in-circuit folding verifier reads.
//!
//! # Steps and public inputs
//! Step `i` has the public inputs `[vk_repr, H(sᵢ₊₁ ‖ hᵢ₊₁)]` (`vk_repr`: 3
//! scalars of the step circuit's own key; `H`: Poseidon; `hᵢ₊₁ = H(accᵢ₊₁)`
//! over [`accumulator_as_public_input`], or `0` for the default
//! accumulator) and proves `sᵢ₊₁ = transition(sᵢ)` and
//! `accᵢ₊₁ = fold(accᵢ, instanceᵢ₋₁)`, where `instanceᵢ₋₁` is read from the
//! previous step's partial proof for the public inputs
//! `[vk_repr, H(sᵢ ‖ hᵢ)]` (both witnessed, so bound to the previous step).
//!
//! # Genesis
//! - Step 0 (`s₀` genesis, no previous instance): `acc₁` is the *default*
//!   accumulator, `h₁ = 0`.
//! - Step 1 (`acc₁` default, flag `is_first`): `acc₂ = init(instance₀)`.
//! - Steps `i ≥ 2`: `accᵢ₊₁ = fold(accᵢ, instanceᵢ₋₁)`.
//!
//! The circuit always computes both `init` and `fold` (on well-formed dummy
//! inputs where they are not meaningful: generator points, zero folding
//! messages; the gadget uses complete additions) and selects: `is_first`
//! between `init` and `fold`, the genesis bit (computed from `sᵢ`) to output
//! `h = 0`. `is_first` is a free witness bit: with it set, the previous
//! instance's public input uses `h = 0`, which only a genesis step outputs
//! (any other step outputs a Poseidon hash), so it can only initialise with
//! the instance of a genesis step; unset, `h = H(accᵢ)`, which is not `0`.
//! The native default accumulator does not exist (no point/scalar value):
//! the prover witnesses a dummy accumulator and the verifier initialises
//! instead of folding when the instance's accumulator is the default one.
//!
//! # Committed instances
//! Folding does not support committed instances. The step circuit's
//! committed-instance column (ZkStdLib always has one) is an *empty plain
//! instance column*, exactly as in [`midnight_zk_stdlib::prove`] for
//! relations without committed instance: never committed, no public input.
//!
//! # Verification
//! `FoldingIvcVerifier::verify`: fold the last step's instance (read for
//! the public inputs computed from the claimed state and accumulator) into
//! the accumulator natively and verify the decider proof. No subgroup checks
//! (out of scope).
//!
//! [`accumulator_as_public_input`]: midnight_circuits::verifier::accumulator_as_public_input

pub use circuit::FoldingIvcCircuit;
use midnight_circuits::verifier::BlstrsFflonkEmulation;
use midnight_curves::Bls12;
use midnight_proofs::poly::{fflonk::Fflonk, kzg::KZGCommitmentScheme};
pub use prover::FoldingIvcProver;
pub use setup::{FoldingIvcKeys, setup};
pub use types::{FoldingAccumulator, FoldingIvcInstance, FoldingIvcProof};
pub use verifier::FoldingIvcVerifier;

pub mod circuit;
pub mod prover;
pub mod setup;
pub mod types;
pub mod verifier;

/// The polynomial commitment scheme of the folding IVC: fflonk over KZG with
/// `T_MAX = 16`.
pub type FoldingPCS = Fflonk<KZGCommitmentScheme<Bls12>, 4>;

/// The self-emulation of the folding IVC: the in-circuit verifier of
/// [`FoldingPCS`] proofs.
pub(crate) type S = BlstrsFflonkEmulation;
