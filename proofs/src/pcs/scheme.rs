//! Trait for a commitment scheme
use core::ops::{Add, Mul};
use std::{
    fmt::Debug,
    hash::Hash,
    io::{self, Read},
};

use ff::{FromUniformBytes, PrimeField};

use crate::{
    plonk::{k_from_circuit, Circuit},
    poly::{
        query::PolynomialLabel, Error, Polynomial, PolynomialRepresentation, ProverQuery,
        VerifierQuery,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::helpers::{ProcessedSerdeObject, SerdeFormat},
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

    /// Commit to one or more polynomials, tagging the result with the
    /// corresponding labels for identification during multi-open accumulation.
    ///
    /// # Panics
    ///
    /// Panics if `polynomials` and `labels` have different lengths, or if
    /// either slice is empty.
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

    /// Read a commitment to `labels.len()` polynomials from the transcript,
    /// absorbing it into the transcript state and tagging each polynomial with
    /// its label.
    fn read_commitment<T: Transcript>(
        transcript: &mut T,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment>
    where
        Self::Commitment: Hashable<T::Hash>;

    /// Deserialize a commitment to `labels.len()` polynomials from `reader`,
    /// tagging each polynomial with its label.
    fn deserialize_commitment<R: Read>(
        reader: &mut R,
        format: SerdeFormat,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self::Commitment>;

    /// Write a batched `commitment` to the transcript and proof. Counterpart to
    /// [`read_commitment`](Self::read_commitment).
    fn write_commitment<T: Transcript>(
        transcript: &mut T,
        commitment: &Self::Commitment,
    ) -> io::Result<()>
    where
        Self::Commitment: Hashable<T::Hash>;

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

    /// Largest polynomial degree this scheme commits to internally, when asked
    /// to commit polynomials of degree at most `max_poly_degree`, those on the
    /// circuit domain (of degree below `2^k`) possibly several at a time.
    ///
    /// Schemes that commit every polynomial as given (e.g. KZG) return
    /// `max_poly_degree`. Schemes that fold several circuit-domain polynomials
    /// into a single commitment (e.g. fflonk) return a larger degree.
    ///
    /// Used to size the parameters, see
    /// [`max_committed_degree`](crate::plonk::max_committed_degree).
    fn internal_degree(k: u32, max_poly_degree: usize) -> usize {
        let _ = k; // Just to avoid a clippy warning.
        max_poly_degree
    }

    /// Create a multi-opening proof at a set of [ProverQuery]'s.
    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        prover_query: &[ProverQuery<F>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;

    /// Total byte length when committing to `n` polynomials.
    ///
    /// For schemes that commit each polynomial independently (e.g. KZG), this
    /// equals `n` times the per-commitment size. Override for schemes that fold
    /// `n` polynomials into a single proof element (e.g. fflonk).
    fn commitment_byte_length(n: usize) -> usize {
        n * Self::Commitment::default().byte_length(SerdeFormat::Processed)
    }

    /// Verify an multi-opening proof for a given set of [VerifierQuery]'s.
    /// The function fails if the transcript has trailing bytes.
    fn multi_prepare<'com, T: Transcript>(
        verifier_query: &[VerifierQuery<'com, F, Self>],
        transcript: &mut T,
    ) -> Result<Self::VerificationGuard, Error>
    where
        F: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash> + 'com;
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
pub trait Params: Send + Sync {
    /// Returns the size of the Lagrange basis, expressed as the exponent `k`
    /// such that the Lagrange domain has `2^k` elements. This equals the
    /// circuit domain size and is used by keygen to validate the SRS.
    fn max_k(&self) -> u32;

    /// Returns the number of monomial-basis elements `[s^i]G₁` available in
    /// the SRS. For a standard SRS this equals `1 << max_k()`. When the
    /// `single-h-commitment` feature is enabled the monomial basis may be
    /// larger than the Lagrange basis (which covers only the circuit
    /// domain), so this method returns the true capacity for
    /// coefficient-form commitments.
    fn g_monomial_size(&self) -> usize {
        1 << self.max_k()
    }

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
