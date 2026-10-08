//! Trait for a commitment scheme
use core::ops::{Add, Mul};
use std::{
    fmt::Debug,
    hash::Hash,
    io::{self, Read},
};

use ff::PrimeField;

use crate::{
    poly::{
        Error, Polynomial, PolynomialRepresentation, ProverQuery, VerifierQuery,
        query::PolynomialLabel,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::helpers::{ProcessedSerdeObject, SerdeFormat},
};

/// Public interface for a additively homomorphic Polynomial Commitment Scheme
/// (PCS)
pub trait PolynomialCommitmentScheme<F: PrimeField>: Clone + Debug {
    /// Parameters needed to generate a proof in the PCS
    type Parameters: Send + Sync;

    /// Parameters needed to verify a proof in the PCS
    type VerifierParameters;

    /// Type of a committed polynomial
    type Commitment: Clone
        + Debug
        + Default
        + PartialEq
        + ProcessedSerdeObject
        + Send
        + Sync
        + Add<Output = Self::Commitment>
        + Mul<F, Output = Self::Commitment>;

    /// Verification guard. Allows for batch verification
    type VerificationGuard: Guard<Self::VerifierParameters>;

    /// Generates the parameters of the polynomial commitment scheme, for
    /// committing to polynomials of degree strictly less than `2^k`.
    fn gen_params(k: u32) -> Self::Parameters;

    /// Reads the parameters of the polynomial commitment scheme from `reader`,
    /// for committing to polynomials of degree strictly less than `2^k`.
    fn load_params<R: io::Read>(
        reader: &mut R,
        format: SerdeFormat,
        k: u32,
    ) -> io::Result<Self::Parameters>;

    /// Returns the largest `k` such that `params` can commit to polynomials of
    /// degree strictly less than `2^k`.
    fn max_k(params: &Self::Parameters) -> u32;

    /// Extract the `VerifierParameters` from `Parameters`
    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters;

    /// Commit to several polynomials, tagging the result with the
    /// corresponding labels for identification during multi-open accumulation.
    ///
    /// The polynomials are committed to in the order given, which must be the
    /// order in which [`read_commitment`](Self::read_commitment) and
    /// [`deserialize_commitment`](Self::deserialize_commitment) receive their
    /// labels.
    ///
    /// Committing to no polynomials does not fail: it returns an empty
    /// commitment, which [`write_commitment`](Self::write_commitment) does not
    /// write to the transcript. An empty commitment holds no polynomial, so it
    /// cannot be queried: the multi-open rejects any query against it.
    ///
    /// # Panics
    ///
    /// Panics if `polynomials` and `labels` have different lengths, or if a
    /// label is repeated.
    fn commit_many<B: PolynomialRepresentation>(
        params: &Self::Parameters,
        polynomials: &[&Polynomial<F, B>],
        labels: &[PolynomialLabel],
    ) -> Self::Commitment;

    /// Commit to a single polynomial in coefficient form, tagging the result
    /// with `label`. Convenience wrapper around
    /// [`commit_many`](Self::commit_many).
    fn commit<B: PolynomialRepresentation>(
        params: &Self::Parameters,
        polynomial: &Polynomial<F, B>,
        label: PolynomialLabel,
    ) -> Self::Commitment {
        Self::commit_many(params, &[polynomial], &[label])
    }

    /// The commitment [`commit_many`](Self::commit_many) returns for zero
    /// polynomials under `labels`, built without the parameters, e.g. for a
    /// verifier to stand in for an absent committed instance.
    fn commitment_to_zero(labels: &[PolynomialLabel]) -> Self::Commitment;

    /// Read a commitment to `labels.len()` polynomials from the proof
    /// transcript, absorbing it into the transcript state and tagging each
    /// polynomial with its label.
    ///
    /// The labels are matched to the points read in the order given, that of
    /// [`commit_many`](Self::commit_many).
    ///
    /// Use [`deserialize_commitment`](Self::deserialize_commitment) instead for
    /// commitments that are not part of the proof.
    ///
    /// # Panics
    ///
    /// Panics if a label is repeated. Labels name the polynomials the
    /// verifying key expects, so a repeat is a caller bug, not a malformed
    /// proof.
    fn read_commitment<T: Transcript>(
        transcript: &mut T,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment>
    where
        Self::Commitment: Hashable<T::Hash>;

    /// Write a commitment produced by [`commit_many`](Self::commit_many) to the
    /// proof transcript, absorbing it in exactly the granularity in which
    /// [`read_commitment`](Self::read_commitment) reads it back.
    ///
    /// A commitment to no polynomials writes and absorbs nothing, and
    /// [`read_commitment`](Self::read_commitment) with no labels reads nothing.
    fn write_commitment<T: Transcript>(
        transcript: &mut T,
        commitment: &Self::Commitment,
    ) -> io::Result<()>
    where
        Self::Commitment: Hashable<T::Hash>,
    {
        transcript.write(commitment)
    }

    /// Deserialize a commitment to `labels.len()` polynomials from `reader`,
    /// tagging each polynomial with its label.
    ///
    /// Unlike [`read_commitment`](Self::read_commitment), the bytes come from a
    /// plain reader, typically a serialized verifying key, and nothing is
    /// absorbed into a transcript.
    ///
    /// # Panics
    ///
    /// Panics if a label is repeated.
    fn deserialize_commitment<R: Read>(
        reader: &mut R,
        format: SerdeFormat,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment>;

    /// Squeeze the evaluation point used by the protocol to open committed
    /// polynomials. The default implementation simply squeezes a challenge,
    /// but specific PCS may require squeezing challenges satisfying certain
    /// properties, for example fflonk requires the evaluation point to be a
    /// `t`-th power in the field.
    ///
    /// The protocol must squeeze evaluation points through this method.
    fn squeeze_evaluation_point<T: Transcript>(transcript: &mut T) -> F
    where
        F: Sampleable<T::Hash>,
    {
        transcript.squeeze_challenge()
    }

    /// Create a multi-opening proof at a set of [ProverQuery]'s.
    ///
    /// The evaluations of the queries are already in the transcript.
    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        prover_query: &[ProverQuery<F>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;

    /// The labels `commitment` tags its polynomials with.
    fn commitment_labels(commitment: &Self::Commitment) -> Vec<PolynomialLabel>;

    /// Total byte length when committing to `n` polynomials, which is 0 when
    /// `n` is 0.
    ///
    /// For schemes that commit each polynomial independently (e.g. KZG), this
    /// equals `n` times the per-commitment size. Override for schemes that fold
    /// `n` polynomials into a single proof element (e.g. fflonk).
    fn commitment_byte_length(n: usize) -> usize {
        n * Self::Commitment::default().byte_length(SerdeFormat::Processed)
    }

    /// Verify an multi-opening proof for a given set of [VerifierQuery]'s.
    /// The function fails if the transcript has trailing bytes.
    ///
    /// `k` is the log2 of the circuit's (Lagrange) domain size. Schemes whose
    /// opening structure depends on the domain relative to the SRS capacity
    /// (e.g. fflonk's SRS-aware bundling) need it to reconstruct and
    /// sanity-check the prover's choices; schemes that don't (e.g. plain KZG)
    /// ignore it.
    fn multi_prepare<'com, T: Transcript>(
        verifier_query: &[VerifierQuery<'com, F, Self>],
        k: u32,
        transcript: &mut T,
    ) -> Result<Self::VerificationGuard, Error>
    where
        F: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash> + 'com;
}

/// Interface for verifier finalizer, given the verifier parameters `VP` of
/// its PCS
pub trait Guard<VP>: Sized {
    /// Finalize the verification guard
    fn verify(self, params: &VP) -> Result<(), Error>;

    /// Finalize a batch of verification guards
    fn batch_verify<'a, I, J>(guards: I, params: J) -> Result<(), Error>
    where
        I: ExactSizeIterator<Item = Self>,
        J: ExactSizeIterator<Item = &'a VP>,
        VP: 'a,
    {
        assert_eq!(guards.len(), params.len());
        guards
            .into_iter()
            .zip(params)
            .try_for_each(|(guard, params)| guard.verify(params))
    }
}
