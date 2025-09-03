use std::marker::PhantomData;

use ff::PrimeField;

use crate::poly::commitment::PolynomialCommitmentScheme;

pub(crate) mod prover;
pub(crate) mod verifier;

/// A vanishing argument.
pub(crate) struct Argument<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    _marker: PhantomData<(F, CS)>,
}
