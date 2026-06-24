use std::fmt::{self, Debug};

use ff::PrimeField;

use crate::poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial};

/// A structured label for polynomial commitments in verifier queries.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PolynomialLabel {
    /// Fixed column commitment (column index).
    Fixed(usize),
    /// Advice column commitment (column index).
    Advice(usize),
    /// Instance column commitment (column index).
    Instance(usize),
    /// Committed instance column commitment (column index).
    CommittedInstance(usize),
    /// Permutation verifying-key commitment (index).
    PermutationFixed(usize),
    /// Permutation accumulator polynomial z(X) (chain index).
    PermutationAccumulator(usize),
    /// LogUp helper polynomial h_j(X) = 1/(f_j(X) + β) (argument index).
    LogupHelper(usize),
    /// LogUp multiplicities polynomial m(X) (argument index).
    LogupMultiplicities(usize),
    /// LogUp accumulator polynomial Z(X) (argument index).
    LogupAggregator(usize),
    /// PLONK quotient polynomial h(X), committed as a single piece.
    Quotient,
    /// PLONK quotient polynomial h(X), committed in pieces (piece index).
    QuotientPiece(usize),
    /// Trash compressed polynomial (argument index).
    Trash(usize),
    /// A commitment obtained by collapsing an MSM.
    Collapsed,
    /// User-defined label.
    Custom(String),
    /// A commitment freshly deserialized from bytes, not yet assigned a label.
    /// Reaching the MSM/query layer with this label is a programming error.
    NoLabel,
}

impl fmt::Display for PolynomialLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fixed(i) => write!(f, "fixed_{i}"),
            Self::Advice(i) => write!(f, "advice_{i}"),
            Self::Instance(i) => write!(f, "instance_{i}"),
            Self::CommittedInstance(i) => write!(f, "committed_instance_{i}"),
            Self::PermutationFixed(i) => write!(f, "perm_fixed_{i}"),
            Self::PermutationAccumulator(i) => write!(f, "perm_acc_{i}"),
            Self::LogupHelper(i) => write!(f, "logup_helper({i})"),
            Self::LogupMultiplicities(i) => write!(f, "logup_multiplicities({i})"),
            Self::LogupAggregator(i) => write!(f, "logup_aggregator({i})"),
            Self::Trash(i) => write!(f, "trash({i})"),
            Self::Quotient => f.write_str("quotient"),
            Self::QuotientPiece(i) => write!(f, "quotient_piece_{i}"),
            Self::Collapsed => f.write_str("collapsed"),
            Self::Custom(s) => write!(f, "custom({s})"),
            Self::NoLabel => f.write_str("no_label"),
        }
    }
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct ProverQuery<'com, F: PrimeField> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Reference to a polynomial
    pub(crate) poly_ref: PolynomialReference<'com, F>,
}

impl<'com, F> ProverQuery<'com, F>
where
    F: PrimeField,
{
    /// Create a new prover query based on a polynomial
    pub fn new(point: F, poly: &'com Polynomial<F, Coeff>) -> Self {
        ProverQuery {
            point,
            poly_ref: PolynomialReference(poly),
        }
    }
}

#[doc(hidden)]
#[derive(Copy, Clone, Debug)]
pub struct PolynomialReference<'com, F: PrimeField>(pub(crate) &'com Polynomial<F, Coeff>);

impl<F: PrimeField> PartialEq for PolynomialReference<'_, F> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
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
    pub(crate) commitment_ref: CommitmentReference<'com, F, CS>,
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
            commitment_ref: CommitmentReference(commitment),
            eval,
        }
    }
}
