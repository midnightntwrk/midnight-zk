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
    fn get_col_idx(&self) -> Vec<Option<usize>> {
        vec![]
    }
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
///
/// Moreover, the commitment to the linearization polynomial is a linear
/// combination of (partially or fully) evaluated identities (i.e., scalars) and
/// commitments to fixed columns (representing simple selectors). In case of
/// full evaluations, the corresponding commitment is just the constant
/// commitment (representing the constant term of a polynomial). This linear
/// combination is represented in the form two vectors: one vectors holds the
/// commitments, the other one holds the scalars.
pub enum CommitmentReference<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    OnePiece(&'com CS::Commitment),
    Chopped(Vec<&'com CS::Commitment>, u64),
    Linear(Vec<&'com CS::Commitment>, Vec<F>),
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
            (
                CommitmentReference::Linear(self_points, self_scalars),
                CommitmentReference::Linear(other_points, other_scalars),
            ) => (self_points == other_points) && (self_scalars == other_scalars),
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
    /// If the commitment is "one piece" or "linear" and an evaluation point is
    /// provided.
    /// If the commitment is "chopped" and no evaluation point is provided.
    /// If the commitment is "linear" and the nr of points differs from the
    /// nr of scalars.
    pub(crate) fn as_terms(
        &self,
        eval_point_opt: Option<F>,
        col_idx: Vec<Option<usize>>,
    ) -> Vec<(F, CS::Commitment, Option<usize>)> {
        match self.clone() {
            CommitmentReference::OnePiece(com) => {
                assert!(eval_point_opt.is_none());
                assert_eq!(col_idx.len(), 1);
                vec![(F::ONE, com.clone(), col_idx[0])]
            }
            CommitmentReference::Chopped(parts, n) => {
                let x = eval_point_opt
                    .expect("an evaluation point is required when the commitment is chopped");
                let xn = x.pow([n]);

                let mut terms = Vec::with_capacity(parts.len());
                let mut scalar = F::ONE;
                for &part in parts.iter() {
                    terms.push((scalar, part.clone(), None));
                    scalar *= xn;
                }
                terms
            }
            CommitmentReference::Linear(points, scalars) => {
                assert!(eval_point_opt.is_none());
                assert_eq!(points.len(), scalars.len());

                let mut terms = Vec::with_capacity(points.len());
                for ((&p, s), col_idx) in points.iter().zip(scalars.iter()).zip(col_idx.iter()) {
                    terms.push((*s, p.clone(), *col_idx));
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
    pub(crate) commitment: (Vec<Option<usize>>, CommitmentReference<'com, F, CS>),
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
            commitment: (vec![None], CommitmentReference::OnePiece(commitment)),
            eval,
        }
    }
    /// Create a new verifier query based on a commitment
    pub fn new_fixed(
        point: F,
        commitment: &'com CS::Commitment,
        eval: F,
        fixed_col_idx: Option<usize>,
    ) -> Self {
        // dbg!(&fixed_col_idx);
        VerifierQuery {
            point,
            commitment: (
                vec![fixed_col_idx],
                CommitmentReference::OnePiece(commitment),
            ),
            eval,
        }
    }

    /// Create a new verifier query based on a commitment
    /// represented in the form of curve points and corresponding
    /// scalars.
    ///
    /// # panics
    ///
    /// If the number of points and scalars differs.
    pub fn new_linear(
        point: F,
        points: Vec<&'com CS::Commitment>,
        scalars: Vec<F>,
        eval: F,
        fixed_col_indices: Vec<Option<usize>>,
    ) -> Self {
        assert_eq!(
            points.len(),
            scalars.len(),
            "The number of points and scalars needs to be equal."
        );
        VerifierQuery {
            point,
            commitment: (
                fixed_col_indices,
                CommitmentReference::Linear(points, scalars),
            ),
            eval,
        }
    }

    /// Create a new verifier query based on a commitment made of pieces
    pub fn from_parts(point: F, parts: &[&'com CS::Commitment], eval: F, n: u64) -> Self {
        VerifierQuery {
            point,
            commitment: (vec![], CommitmentReference::Chopped(parts.to_vec(), n)),
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
        self.commitment.1.clone()
    }

    fn get_col_idx(&self) -> Vec<Option<usize>> {
        self.commitment.0.clone()
    }
}
