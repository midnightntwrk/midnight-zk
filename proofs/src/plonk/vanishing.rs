use std::marker::PhantomData;

use ff::PrimeField;

use crate::poly::commitment::PolynomialCommitmentScheme;

mod prover;
mod verifier;

/// A vanishing argument.
pub(crate) struct Argument<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    _marker: PhantomData<(F, CS)>,
}
