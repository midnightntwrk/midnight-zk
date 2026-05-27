use std::fmt;

use ff::PrimeField;

use crate::poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial};

/// A structured label for polynomial commitments in verifier queries.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    /// LogUp helper polynomial h_j(X) = 1/(f_j(X) + β), for a named argument.
    LogupHelper(String),
    /// LogUp multiplicities polynomial m(X), for a named argument.
    LogupMultiplicities(String),
    /// LogUp accumulator polynomial Z(X), for a named argument.
    LogupAggregator(String),
    /// PLONK quotient polynomial h(X), committed as a single piece.
    Quotient,
    /// PLONK quotient polynomial h(X), committed in pieces (piece index).
    QuotientPiece(usize),
    /// Trash compressed polynomial, for a named argument.
    Trash(String),
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
            Self::LogupHelper(name) => write!(f, "logup_helper({name})"),
            Self::LogupMultiplicities(name) => write!(f, "logup_multiplicities({name})"),
            Self::LogupAggregator(name) => write!(f, "logup_aggregator({name})"),
            Self::Trash(name) => write!(f, "trash({name})"),
            Self::Quotient => f.write_str("quotient"),
            Self::QuotientPiece(i) => write!(f, "quotient_piece_{i}"),
            Self::Collapsed => f.write_str("collapsed"),
            Self::Custom(s) => f.write_str(s),
            Self::NoLabel => f.write_str("no_label"),
        }
    }
}

/// A polynomial query at a point
#[derive(Debug, Clone)]
pub struct ProverQuery<'com, F: PrimeField> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Coefficients of polynomial
    pub(crate) poly: &'com Polynomial<F, Coeff>,
    /// Label identifying which polynomial within the commitment is being
    /// opened.
    pub(crate) label: PolynomialLabel,
}

impl<'com, F> ProverQuery<'com, F>
where
    F: PrimeField,
{
    /// Create a new prover query based on a polynomial and its label.
    pub fn new(point: F, poly: &'com Polynomial<F, Coeff>, label: PolynomialLabel) -> Self {
        ProverQuery { point, poly, label }
    }
}

/// A polynomial query at a point.
#[derive(Debug, Clone)]
pub struct VerifierQuery<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    /// Point at which polynomial is queried.
    pub(crate) point: F,
    /// Reference to the commitment that contains the queried polynomial.
    pub(crate) commitment: &'com CS::Commitment,
    /// Evaluation of polynomial at query point.
    pub(crate) eval: F,
    /// Label identifying which polynomial within the commitment is being
    /// opened.
    pub(crate) label: PolynomialLabel,
}

impl<'com, F, CS> VerifierQuery<'com, F, CS>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    /// Create a new verifier query.
    pub fn new(
        point: F,
        commitment: &'com CS::Commitment,
        eval: F,
        label: PolynomialLabel,
    ) -> Self {
        VerifierQuery {
            point,
            commitment,
            eval,
            label,
        }
    }
}
