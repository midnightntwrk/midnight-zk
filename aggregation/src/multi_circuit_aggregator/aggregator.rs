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

    /// Folds a batch of witnesses in order, returning the final aggregation
    /// proof (the proof after the last step). This is a thin loop over
    /// [`Aggregator::aggregate`]; the running instance is available via the
    /// `instance()` method.
    ///
    /// Returns [`IvcError::InvalidWitness`] if `witnesses` is empty, or the
    /// first per-step error otherwise.
    pub fn aggregate_all(
        &mut self,
        witnesses: impl IntoIterator<Item = AggregationWitness>,
    ) -> Result<Vec<u8>, IvcError> {
        let mut proof = None;
        for witness in witnesses {
            proof = Some(self.aggregate(witness)?);
        }
        proof.ok_or_else(|| {
            IvcError::InvalidWitness("aggregate_all requires at least one witness".to_string())
        })
    }
}

/// Aggregates many proofs of a **single** inner circuit — all sharing the same
/// verifying key `inner_vk` — into one succinct proof.
///
/// This is the "batch proving via aggregation" (Option A) use case: given `K`
/// instances of one circuit and their inner proofs, it folds them into a single
/// IVC proof whose verification cost and size are constant in `K`. Build the
/// `aggregator` with [`ProofAggregation::setup`], then obtain the final
/// instance with the aggregator's `instance()` method and check it with
/// [`Verifier::verify_aggregation`].
///
/// `instances` and `inner_proofs` must be parallel slices of equal length, in
/// matching order (`inner_proofs[i]` must be a proof of `R` for `instances[i]`,
/// produced under `inner_vk`). Inner proofs can be generated with
/// `midnight_zk_stdlib::prove` (or, in parallel, `midnight_zk_stdlib::batch_prove`).
///
/// Returns [`IvcError::InvalidWitness`] if the slice lengths differ or are
/// empty, and propagates the first aggregation error otherwise.
pub fn aggregate_same_circuit<R>(
    aggregator: &mut Aggregator,
    inner_vk: &MidnightVK,
    instances: &[R::Instance],
    inner_proofs: &[Vec<u8>],
) -> Result<Vec<u8>, IvcError>
where
    R: AggregableRelation + Default + std::fmt::Debug + 'static,
    R::Instance: std::fmt::Debug + Clone,
{
    if instances.len() != inner_proofs.len() {
        return Err(IvcError::InvalidWitness(format!(
            "instances ({}) and inner_proofs ({}) must have equal length",
            instances.len(),
            inner_proofs.len(),
        )));
    }

    let witnesses = instances.iter().zip(inner_proofs.iter()).map(|(instance, proof)| {
        AggregationWitness::new::<R>(inner_vk.clone(), instance.clone(), proof.clone())
    });

    aggregator.aggregate_all(witnesses)
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
