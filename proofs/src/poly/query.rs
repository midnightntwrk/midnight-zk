use std::{fmt::Debug, ops::Deref};

use ff::PrimeField;

use crate::{
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial},
    utils::arithmetic::eval_polynomial,
};

pub trait Query<F>: Debug + Sized + Clone + Send + Sync {
    type Commitment: Debug + PartialEq + Copy + Send + Sync;
    type Eval: Clone + Default + Debug;

    fn get_point(&self) -> F;
    fn get_eval(&self) -> Self::Eval;
    fn get_commitment(&self) -> Self::Commitment;
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct ProverQuery<'com, F: PrimeField> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Coefficients of polynomial
    pub(crate) poly: &'com Polynomial<F, Coeff>,
}

impl<'com, F> ProverQuery<'com, F>
where
    F: PrimeField,
{
    /// Create a new prover query based on a polynomial
    pub fn new(point: F, poly: &'com Polynomial<F, Coeff>) -> Self {
        ProverQuery { point, poly }
    }
}

#[doc(hidden)]
#[derive(Copy, Clone, Debug)]
pub struct PolynomialPointer<'com, F: PrimeField> {
    pub(crate) poly: &'com Polynomial<F, Coeff>,
}

impl<'com, F: PrimeField> PartialEq for PolynomialPointer<'com, F> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.poly, other.poly)
    }
}

impl<'com, F: PrimeField> Query<F> for ProverQuery<'com, F> {
    type Commitment = PolynomialPointer<'com, F>;
    type Eval = F;

    fn get_point(&self) -> F {
        self.point
    }
    fn get_eval(&self) -> Self::Eval {
        eval_polynomial(&self.poly[..], self.get_point())
    }
    fn get_commitment(&self) -> Self::Commitment {
        PolynomialPointer { poly: self.poly }
    }
}

#[derive(Clone, Debug)]
pub struct CommitmentReference<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    &'com CS::Commitment,
);

impl<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> Copy
    for CommitmentReference<'com, F, CS>
{
}

impl<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> PartialEq
    for CommitmentReference<'com, F, CS>
{
    #![allow(ambiguous_wide_pointer_comparisons)]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> Deref
    for CommitmentReference<'com, F, CS>
{
    type Target = CS::Commitment;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct VerifierQuery<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Commitment to polynomial
    pub(crate) commitment: CommitmentReference<'com, F, CS>,
    /// Evaluation of polynomial at query point
    pub(crate) eval: F,
}

impl<'com, F, CS> VerifierQuery<'com, F, CS>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    /// Create a new verifier query based on a commitment
    pub fn new(point: F, commitment: &'com CS::Commitment, eval: F) -> Self {
        VerifierQuery {
            point,
            commitment: CommitmentReference(commitment),
            eval,
        }
    }
}

impl<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> Query<F>
    for VerifierQuery<'com, F, CS>
{
    type Commitment = CommitmentReference<'com, F, CS>;
    type Eval = F;

    fn get_point(&self) -> F {
        self.point
    }
    fn get_eval(&self) -> F {
        self.eval
    }
    fn get_commitment(&self) -> Self::Commitment {
        self.commitment
    }
}
