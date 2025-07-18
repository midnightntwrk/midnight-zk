use std::fmt::Debug;

use ff::PrimeField;

use crate::{
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial},
    utils::arithmetic::eval_polynomial,
};

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

#[derive(Clone, Debug)]
/// A reference to a polynomial commitment.
///
/// Most polynomials are committed in "one piece", however, polynomials of high
/// degree can be "chopped" into pieces, which are then committed individually.
/// Concretely, a polynomial A(X) of degree k * n can be chopped into k pieces
/// {A_i(X)}_i of degree n, such that A(X) := sum_i A_i(X) * X^{n * i}. In that
/// case, the `Chopped` representation of the commitment includes commitments
/// to all the pieces [A_i(X)] as well as the piece-degree `n`.
/// (Note that the pieces are stored in little-endian.)
pub enum CommitmentReference<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    OnePiece(&'com CS::Commitment),
    Chopped(Vec<&'com CS::Commitment>, u64),
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PartialEq
    for CommitmentReference<'_, F, CS>
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                &CommitmentReference::OnePiece(self_com),
                &CommitmentReference::OnePiece(other_com),
            ) => std::ptr::eq(self_com, other_com),
            (
                CommitmentReference::Chopped(self_parts, self_n),
                CommitmentReference::Chopped(other_parts, other_n),
            ) => {
                if self_parts.len() != other_parts.len() {
                    return false;
                }

                for i in 0..self_parts.len() {
                    if !std::ptr::eq(self_parts[i], other_parts[i]) {
                        return false;
                    }
                }

                self_n == other_n
            }
            _ => false,
        }
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> CommitmentReference<'_, F, CS> {
    pub(crate) fn is_chopped(&self) -> bool {
        matches!(self, CommitmentReference::Chopped(_, _))
    }

    /// If the commitment is represented in one piece, this function returns
    /// vec![(F::ONE, com)] and the evaluation point should not be provided.
    ///
    /// If the commitment is in chopped form ({com_i}_i, n), given evaluation
    /// point `x`, this function returns vector {(x^{n * i}, com_i)}_i,
    /// representing the evaluation of this commitment at `x`.
    ///
    /// # Panics
    ///
    /// If the commitment is in "one piece" and an evaluation point is provided.
    /// If the commitment is "chopped" and no evaluation point is provided.
    pub(crate) fn as_terms(&self, eval_point_opt: Option<F>) -> Vec<(F, CS::Commitment)> {
        match self.clone() {
            CommitmentReference::OnePiece(com) => {
                assert!(eval_point_opt.is_none());
                vec![(F::ONE, com.clone())]
            }
            CommitmentReference::Chopped(parts, n) => {
                let x = eval_point_opt
                    .expect("an evaluation point is required when the commitment is chopped");
                let xn = x.pow([n]);

                let mut terms = Vec::with_capacity(parts.len());
                let mut scalar = F::ONE;
                for &part in parts.iter() {
                    terms.push((scalar, part.clone()));
                    scalar *= xn;
                }
                terms
            }
        }
    }
}

/// A polynomial query at a point
#[derive(Debug, Clone)]
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
            commitment: CommitmentReference::OnePiece(commitment),
            eval,
        }
    }

    /// Create a new verifier query based on a commitment made of pieces
    pub fn from_parts(point: F, parts: &[&'com CS::Commitment], eval: F, n: u64) -> Self {
        VerifierQuery {
            point,
            commitment: CommitmentReference::Chopped(parts.to_vec(), n),
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
        self.commitment.clone()
    }
}
