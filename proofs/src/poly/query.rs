use std::fmt::{self, Debug};

use ff::PrimeField;

use crate::{
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial},
    utils::arithmetic::eval_polynomial,
};

/// A structured label for polynomial commitments in verifier queries.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CommitmentLabel {
    /// Advice column commitment (column index).
    Advice(usize),
    /// Instance column commitment (column index).
    Instance(usize),
    /// Fixed column commitment (column index).
    Fixed(usize),
    /// Permutation verifying-key commitment (index).
    Permutation(usize),
    /// User-defined label.
    Custom(String),
    /// No label.
    NoLabel,
}

impl fmt::Display for CommitmentLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Advice(i) => write!(f, "advice_{i}"),
            Self::Instance(i) => write!(f, "instance_{i}"),
            Self::Fixed(i) => write!(f, "fixed_{i}"),
            Self::Permutation(i) => write!(f, "vk_perm_{i}"),
            Self::Custom(s) => f.write_str(s),
            Self::NoLabel => f.write_str("-"),
        }
    }
}

pub trait Query<F>: Debug + Sized + Clone + Send + Sync {
    type Commitment: Debug + PartialEq + Clone + Send + Sync;
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

impl<F: PrimeField> PartialEq for PolynomialPointer<'_, F> {
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

/// A pointer to a commitment, with pointer-based equality.
///
/// Two `CommitmentReference`s are equal iff they point to the same allocation,
/// so that commitments are grouped by reference rather than by value.
#[derive(Debug)]
pub struct CommitmentReference<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>>(
    pub(crate) &'com CS::Commitment,
);

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Copy for CommitmentReference<'_, F, CS> {}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Clone for CommitmentReference<'_, F, CS> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PartialEq
    for CommitmentReference<'_, F, CS>
{
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

/// A polynomial query at a point.
#[derive(Debug, Clone)]
pub struct VerifierQuery<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    /// Point at which polynomial is queried.
    pub(crate) point: F,
    /// Commitment to polynomial.
    pub(crate) commitment: CommitmentReference<'com, F, CS>,
    /// Evaluation of polynomial at query point.
    pub(crate) eval: F,
}

impl<'com, F, CS> VerifierQuery<'com, F, CS>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    /// Create a new verifier query.
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
