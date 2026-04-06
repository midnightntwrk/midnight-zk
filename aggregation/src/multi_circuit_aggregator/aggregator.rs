//! Aggregator, verifier, and witness types for multi-circuit proof aggregation.
//!
//! The [`Aggregator`] is the main entry point for building an aggregation
//! proof. It wraps the IVC prover and exposes a simple interface:
//! create witnesses with [`AggregationWitness::new`], then fold them in
//! one at a time with [`Aggregator::aggregate`].
//!
//! Each call to [`Aggregator::aggregate`] validates the witness (architecture
//! check), runs the off-circuit transition, and produces a new IVC proof that
//! attests to all claims aggregated so far.
//!
//! The [`Verifier`] checks the final aggregation proof. After verification,
//! the claims can be inspected via the instance's state.

use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_zk_stdlib::{MidnightVK, ZkStdLibArch};

use super::{
    circuit::{InnerCircuitsContext, ProofAggregation},
    claims::{Claim, TypedStatement},
    AggregableRelation,
};
use crate::ivc::{self, IvcError, IvcInstance, E};

impl ProofAggregation {
    /// Sets up the proof aggregator, returning an [`Aggregator`] (at genesis)
    /// and a [`Verifier`].
    pub fn setup(
        aggregator_srs: ParamsKZG<E>,
        aggregator_k: u32,
        inner_ctx: InnerCircuitsContext,
    ) -> (Aggregator, Verifier) {
        ivc::setup::<ProofAggregation>(aggregator_srs, aggregator_k, inner_ctx)
    }
}

/// Witness for a single aggregation step.
///
/// Contains the [`Claim`] being aggregated, the inner proof bytes that back
/// it, and the architecture of the inner circuit (used for validation).
#[derive(Clone, Debug)]
pub struct AggregationWitness {
    pub(crate) claim: Claim,
    pub(crate) inner_proof: Vec<u8>,
    arch: ZkStdLibArch,
}

impl AggregationWitness {
    /// Creates an [`AggregationWitness`] from a VK, a typed instance, and
    /// the inner proof bytes. The instance is wrapped into a type-erased
    /// [`Statement`](super::Statement) via [`TypedStatement`].
    pub fn new<R: AggregableRelation + Default + std::fmt::Debug + 'static>(
        vk: MidnightVK,
        instance: R::Instance,
        inner_proof: Vec<u8>,
    ) -> Self
    where
        R::Instance: std::fmt::Debug + Clone,
    {
        let statement = Box::new(TypedStatement::<R>::new(instance));
        AggregationWitness {
            claim: Claim { vk, statement },
            inner_proof,
            arch: R::default().used_chips(),
        }
    }
}

/// Stateful proof aggregator.
///
/// Internally an IVC prover specialized for [`ProofAggregation`]. Each call
/// to [`aggregate`](Self::aggregate) folds one inner proof into the running
/// chain. The resulting IVC proof can be verified with
/// [`Verifier::verify_aggregation`].
pub type Aggregator = ivc::IvcProver<ProofAggregation>;

impl Aggregator {
    /// Aggregates one inner proof, advancing the chain by one step.
    ///
    /// Returns [`IvcError::InvalidWitness`] if the inner circuit's
    /// architecture does not match the one chosen at setup time, or if the
    /// inner proof is invalid.
    pub fn aggregate(&mut self, witness: AggregationWitness) -> Result<Vec<u8>, IvcError> {
        if witness.arch != self.relation.ctx().arch() {
            return Err(IvcError::InvalidWitness(format!(
                "architecture mismatch: expected {:?}, got {:?}",
                self.relation.ctx().arch(),
                witness.arch,
            )));
        }
        self.prove_step(witness)
    }
}

/// Verifier for multi-circuit proof aggregation.
///
/// Internally an IVC verifier specialized for [`ProofAggregation`].
pub type Verifier = ivc::IvcVerifier<ProofAggregation>;

impl Verifier {
    /// Verifies an aggregation proof against the given instance.
    pub fn verify_aggregation(
        &self,
        instance: &IvcInstance<ProofAggregation>,
        proof: &[u8],
    ) -> Result<(), IvcError> {
        self.verify(instance, proof)
    }
}
