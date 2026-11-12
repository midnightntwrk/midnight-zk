//! A verifying key that has been absorbed into a transcript.

use std::io;

use ff::PrimeField;

use super::VerifyingKey;
use crate::{
    poly::{PolynomialLabel, commitment::PolynomialCommitmentScheme},
    transcript::{Hashable, Transcript},
};

/// A verifying key whose `transcript_repr` has been absorbed into a
/// transcript.
///
/// The witness records which key was absorbed, not into which transcript.
///
/// The `transcript_repr` hashes every commitment the key holds, so those
/// commitments are bound to the transcript as much as the ones read from the
/// proof. The field is private to this module, so the only way to obtain one is
/// through [`VerifyingKey::absorb_into`].
#[derive(Debug)]
pub(crate) struct AbsorbedVk<'a, F: PrimeField, PCS: PolynomialCommitmentScheme<F>>(
    &'a VerifyingKey<F, PCS>,
);

impl<'a, F: PrimeField, PCS: PolynomialCommitmentScheme<F>> AbsorbedVk<'a, F, PCS> {
    /// The `transcript_repr` of the absorbed key.
    pub(crate) fn transcript_repr(&self) -> F {
        self.0.transcript_repr
    }

    /// The commitment the absorbed key holds to its phase-0 group; see
    /// [`VerifyingKey::phase0_commitment`].
    pub(crate) fn phase0_commitment(&self) -> &'a PCS::Commitment {
        &self.0.phase0_commitment
    }

    /// The labels of the polynomials committed to by
    /// [`Self::phase0_commitment`].
    pub(crate) fn phase0_labels(&self) -> Vec<PolynomialLabel> {
        self.0.cs.fixed_polys_labels()
    }
}

impl<F: PrimeField, PCS: PolynomialCommitmentScheme<F>> VerifyingKey<F, PCS> {
    /// Absorbs this verifying key into `transcript`, returning the witness that
    /// it was.
    pub(crate) fn absorb_into<T>(&self, transcript: &mut T) -> io::Result<AbsorbedVk<'_, F, PCS>>
    where
        F: Hashable<T::Hash>,
        T: Transcript,
    {
        transcript.common(&self.transcript_repr)?;
        Ok(AbsorbedVk(self))
    }
}
