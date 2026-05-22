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
    fn get_commitment_label(&self) -> CommitmentLabel;
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
    fn get_commitment_label(&self) -> CommitmentLabel {
        CommitmentLabel::NoLabel
    }
}

#[derive(Clone, Debug)]
/// A reference to a polynomial commitment.
///
/// A commitment can either be a single piece (`OnePiece`) or a linear
/// combination of commitments (`Linear`). The linear form is used, e.g., for
/// the linearization polynomial, whose commitment is expressed as:
///     * scalars (representing - partially or fully - evaluated identities),
///       and
///     * commitments (representing, either, commitments to simple,
///       multiplicative selectors or the commitment to the constant polynomial
///       `P(X) = 1`).
/// The linear combination is given in form of two vectors: one holds references
/// to the commitments, the other one holds the scalars.
pub enum CommitmentReference<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    OnePiece(&'com CS::Commitment),
    Linear(Vec<&'com CS::Commitment>, Vec<F>, Vec<CommitmentLabel>),
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
                CommitmentReference::Linear(self_points, self_scalars, _),
                CommitmentReference::Linear(other_points, other_scalars, _),
            ) => (self_points == other_points) && (self_scalars == other_scalars),
            _ => false,
        }
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> CommitmentReference<'_, F, CS> {
    /// Returns the commitment as a list of `(scalar, commitment)` pairs.
    ///
    /// If the commitment is represented in one piece, this function returns
    /// `vec![(F::ONE, com)]`.
    ///
    /// If the commitment is a linear combination, this function returns the
    /// pairs `(scalar_i, commitment_i)`.
    ///
    /// # Panics
    ///
    /// If the commitment is "linear" and the number of points and the number
    /// of scalars are not equal.
    pub(crate) fn as_terms(&self) -> Vec<(F, CS::Commitment)> {
        match self.clone() {
            CommitmentReference::OnePiece(com) => {
                vec![(F::ONE, com.clone())]
            }
            CommitmentReference::Linear(points, scalars, _) => {
                assert_eq!(points.len(), scalars.len());

                let mut terms = Vec::with_capacity(points.len());
                for (&p, s) in points.iter().zip(scalars.iter()) {
                    terms.push((*s, p.clone()));
                }
                terms
            }
        }
    }
}

/// A polynomial query at a point.
#[derive(Debug, Clone)]
pub struct VerifierQuery<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    /// Point at which polynomial is queried.
    pub(crate) point: F,
    /// Optional label identifying the commitment in this query.
    pub(crate) commitment_label: CommitmentLabel,
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
    /// Create a new verifier query based on an optionally labeled commitment.
    pub fn new(
        point: F,
        commitment_label: CommitmentLabel,
        commitment: &'com CS::Commitment,
        eval: F,
    ) -> Self {
        VerifierQuery {
            point,
            commitment_label,
            commitment: CommitmentReference::OnePiece(commitment),
            eval,
        }
    }

    /// Create a new verifier query based on a commitment
    /// represented in the form of curve points and corresponding
    /// scalars. Each term carries its own `CommitmentLabel` so that
    /// downstream consumers (e.g. `from_dual_msm`) can classify
    /// individual bases correctly.
    ///
    /// # panics
    ///
    /// If the number of points, scalars, or base_labels differs.
    pub fn new_linear(
        point: F,
        commitment_label: CommitmentLabel,
        points: Vec<&'com CS::Commitment>,
        scalars: Vec<F>,
        base_labels: Vec<CommitmentLabel>,
        eval: F,
    ) -> Self {
        assert_eq!(
            points.len(),
            scalars.len(),
            "The number of points and scalars needs to be equal."
        );
        assert_eq!(
            points.len(),
            base_labels.len(),
            "The number of points and base_labels needs to be equal."
        );
        VerifierQuery {
            point,
            commitment_label,
            commitment: CommitmentReference::Linear(points, scalars, base_labels),
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
    fn get_commitment_label(&self) -> CommitmentLabel {
        self.commitment_label.clone()
    }
}
