//! Trait for a commitment scheme
use core::ops::{Add, Mul};
use std::fmt::Debug;

use ff::{FromUniformBytes, PrimeField};

use crate::{
    plonk::{k_from_circuit, Circuit},
    poly::{Coeff, Error, LagrangeCoeff, Polynomial, ProverQuery, VerifierQuery},
    transcript::{Hashable, Sampleable, Transcript},
    utils::helpers::ProcessedSerdeObject,
};

/// Public interface for a additively homomorphic Polynomial Commitment Scheme
/// (PCS)
pub trait PolynomialCommitmentScheme<F: PrimeField>: Clone + Debug {
    /// Parameters needed to generate a proof in the PCS
    type Parameters: Params;

    /// Parameters needed to verify a proof in the PCS
    type VerifierParameters;

    /// Type of a committed polynomial
    type Commitment: Clone
        + Copy
        + Debug
        + Default
        + PartialEq
        + ProcessedSerdeObject
        + Send
        + Sync
        + Add<Output = Self::Commitment>
        + Mul<F, Output = Self::Commitment>;

    /// Verification guard. Allows for batch verification
    type VerificationGuard: Guard<F, Self>;

    /// Generates the parameters of the polynomial commitment scheme
    fn gen_params(k: u32) -> Self::Parameters;

    /// Extract the `VerifierParameters` from `Parameters`
    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters;

    /// Commit to a polynomial in coefficient form
    fn commit(params: &Self::Parameters, polynomial: &Polynomial<F, Coeff>) -> Self::Commitment;

    /// Commit to a polynomial expressed in Lagrange evaluations form (over the
    /// underlying domain specified in params).
    fn commit_lagrange(
        params: &Self::Parameters,
        poly: &Polynomial<F, LagrangeCoeff>,
    ) -> Self::Commitment;

    /// Create a multi-opening proof at a set of [ProverQuery]'s.
    fn multi_open<'com, T: Transcript>(
        params: &Self::Parameters,
        prover_query: impl IntoIterator<Item = ProverQuery<'com, F>> + Clone,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Sampleable<T::Hash> + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;

    /// Verify an multi-opening proof for a given set of [VerifierQuery]'s.
    /// The function fails if the transcript has trailing bytes.
    fn multi_prepare<'com, T: Transcript>(
        verifier_query: impl IntoIterator<Item = VerifierQuery<'com, F, Self>> + Clone,
        transcript: &mut T,
    ) -> Result<Self::VerificationGuard, Error>
    where
        F: Sampleable<T::Hash> + Ord + Hashable<T::Hash>,
        Self::Commitment: 'com + Hashable<T::Hash>;
}

/// Interface for verifier finalizer
pub trait Guard<F: PrimeField, CS: PolynomialCommitmentScheme<F>>: Sized {
    /// Finalize the verification guard
    fn verify(self, params: &CS::VerifierParameters) -> Result<(), Error>;

    /// Finalize a batch of verification guards
    fn batch_verify<'a, I, J>(guards: I, params: J) -> Result<(), Error>
    where
        I: ExactSizeIterator<Item = Self>,
        J: ExactSizeIterator<Item = &'a CS::VerifierParameters>,
        CS::VerifierParameters: 'a,
    {
        assert_eq!(guards.len(), params.len());
        guards
            .into_iter()
            .zip(params)
            .try_for_each(|(guard, params)| guard.verify(params))
    }
}

/// Interface for PCS params
pub trait Params {
    /// Returns the max size of polynomials that these parameters can commit to
    fn max_k(&self) -> u32;

    /// Downsize the params to work with a circuit of size `new_k`
    fn downsize(&mut self, new_k: u32);

    /// Downsize the params to work with a circuit of unknown length. The
    /// function first computes the `k` of the provided circuit, and then
    /// downsizes the SRS.
    fn downsize_from_circuit<
        F: PrimeField + Ord + FromUniformBytes<64>,
        ConcreCircuit: Circuit<F>,
    >(
        &mut self,
        circuit: &ConcreCircuit,
    ) {
        let k = k_from_circuit(circuit);
        self.downsize(k);
    }
}
