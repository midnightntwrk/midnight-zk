//! A verifying key that has been absorbed into a transcript.

use std::io;

use ff::PrimeField;

use super::VerifyingKey;
use crate::{
    poly::commitment::PolynomialCommitmentScheme,
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
pub(crate) struct AbsorbedVk<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    &'a VerifyingKey<F, CS>,
);

impl<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>> AbsorbedVk<'a, F, CS> {
    /// The `transcript_repr` of the absorbed key.
    pub(crate) fn transcript_repr(&self) -> F {
        self.0.transcript_repr
    }

    /// The commitment the absorbed key holds to a group of fixed polynomials,
    /// as opposed to the per-column `fixed_commitments`.
    ///
    /// The key holds a single such group, the fixed permutation polynomials;
    /// this is to be generalized once other groups are committed to in the
    /// key.
    pub(crate) fn fixed_group_commitment(&self) -> &'a CS::Commitment {
        &self.0.fixed_perm_commitment
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    /// Absorbs this verifying key into `transcript`, returning the witness that
    /// it was.
    pub(crate) fn absorb_into<T: Transcript>(
        &self,
        transcript: &mut T,
    ) -> io::Result<AbsorbedVk<'_, F, CS>>
    where
        F: Hashable<T::Hash>,
    {
        transcript.common(&self.transcript_repr)?;
        Ok(AbsorbedVk(self))
    }
}
