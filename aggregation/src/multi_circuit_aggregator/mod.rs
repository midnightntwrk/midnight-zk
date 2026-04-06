//! Multi-circuit proof aggregation via IVC.
//!
//! This module provides an IVC-based proof aggregator that can aggregate proofs
//! from different inner circuits (i.e. circuits with different verifying keys)
//! into a single succinct proof.
//!
//! All inner circuits must share the same constraint system and evaluation
//! domain. They differ only in their verifying keys (fixed commitments).
//! Furthermore, all inner proofs must have been generated with the same SRS.
//!
//! The IVC state tracks:
//! - A list of claims off-circuit `(vk, statement)`.
//! - A succinct representation of such claims, in the form of the digest of a
//!   hash chain (with Poseidon) over the `(hash(vk), statement)` pairs.
//! - An accumulator for deferred inner-proof verification (decider check).
//!
//! At each IVC step the transition function verifies one inner proof
//! in-circuit w.r.t. some witnessed `vk_hash` and some witnessed `statement`
//! folds the result into the running accumulator and hashes the
//! `(hash(vk), statement)` pair into the Poseidon chain.
//!
//! A verifier receives the final IVC proof together with the list of claims.
//! The public instance of the IVC proof is composed of the claims digest
//! (the tip of a Poseidon hash chain) and the inner-proof accumulator. Both are
//! constant-size regardless of how many proofs were aggregated.
//!
//! Verification consists of:
//!
//! 1. Verify the IVC proof against the public instance. This checks:
//!
//!    a. The proof itself is valid w.r.t. the IVC verifying key.
//!    b. The claims digest in the instance matches the Poseidon hash chain
//!    recomputed from the provided list of claims (decider check).
//!    c. The accumulated inner-proof verification passes the pairing check
//!    (decider check).
//!
//! 2. Check that the aggregated claims are acceptable. Step 1 guarantees that
//!    every claim has a valid inner proof, but says nothing about *what* was
//!    proved. It is up to the verifier to decide whether the claims are
//!    meaningful by checking that each VK belongs to a trusted circuit, whose
//!    setup was run by the verifier and whose architecture meets the
//!    domain-specific requirements.

use midnight_zk_stdlib::Relation;

use crate::ivc::F;

mod aggregator;
mod circuit;
mod claims;
mod utils;

pub use aggregator::{AggregationWitness, Aggregator, Verifier};
pub use circuit::{InnerCircuitsContext, ProofAggregation, State};
pub use claims::{Claim, Statement, TypedStatement};

/// Extension of [`Relation`] for circuits whose proofs can be aggregated
/// w.r.t. a given IVC setup.
///
/// A relation is aggregable if it uses the
/// [`ZkStdLibArch`](midnight_zk_stdlib::ZkStdLibArch) chosen at IVC setup time,
/// is padded to the common circuit size `K`, and formats its instance into a
/// single public input.
pub trait AggregableRelation: Relation {
    /// Encodes the statement (the relation's instance) as a single
    /// public-input field element.
    ///
    /// # Panics
    ///
    /// If `format_instance` fails or does not return exactly one public input.
    fn format_statement(instance: &Self::Instance) -> F {
        let pis = Self::format_instance(instance).ok().expect("format_instance failed");
        assert_eq!(
            pis.len(),
            1,
            "aggregable circuits must have exactly one public input"
        );
        pis[0]
    }
}
