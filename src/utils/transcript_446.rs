use std::marker::PhantomData;

use ff::{FromUniformBytes, PrimeField};
use halo2_proofs::transcript::EncodedChallenge;
use pasta_curves::arithmetic::CurveAffine;

/// A 446-bit challenge.
#[derive(Copy, Clone, Debug)]
pub struct Challenge446<C: CurveAffine>([u8; 56], PhantomData<C>);

impl<C: CurveAffine> std::ops::Deref for Challenge446<C> {
    type Target = [u8; 56];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<C: CurveAffine> EncodedChallenge<C> for Challenge446<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    type Input = [u8; 64];

    fn new(challenge_input: &[u8; 64]) -> Self {
        Challenge446(
            C::Scalar::from_uniform_bytes(challenge_input)
                .to_repr()
                .as_ref()
                .try_into()
                .expect("Scalar used does not fit in 56 bytes"),
            PhantomData,
        )
    }
    fn get_scalar(&self) -> C::Scalar {
        let mut repr = <C::Scalar as PrimeField>::Repr::default();
        repr.as_mut().copy_from_slice(&self.0);
        C::Scalar::from_repr(repr).unwrap()
    }
}
