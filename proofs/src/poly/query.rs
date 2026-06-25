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
    /// LogUp helper polynomial h_j(X) = 1/(f_j(X) + β)
    /// (argument index, chunk index `j`).
    LogupHelper(usize, usize),
    /// LogUp multiplicities polynomial m(X) (argument index).
    LogupMultiplicities(usize),
    /// LogUp accumulator polynomial Z(X) (argument index).
    LogupAggregator(usize),
    /// PLONK linearization polynomial.
    Linearization,
    /// PLONK quotient polynomial h(X), committed as a single piece.
    Quotient,
    /// PLONK quotient polynomial h(X), committed in pieces (piece index).
    QuotientPiece(usize),
    /// Trash compressed polynomial (argument index).
    Trash(usize),
    /// User-defined label.
    Custom(String),
    /// Absence of a meaningful label. Used for freshly deserialized commitments
    /// (before a label is attached) and for aggregate commitments produced by
    /// collapsing an MSM, which do not correspond to a single polynomial.
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
            Self::LogupHelper(i, j) => write!(f, "logup_helper({i}, {j})"),
            Self::LogupMultiplicities(i) => write!(f, "logup_multiplicities({i})"),
            Self::LogupAggregator(i) => write!(f, "logup_aggregator({i})"),
            Self::Trash(i) => write!(f, "trash({i})"),
            Self::Linearization => f.write_str("linearization"),
            Self::Quotient => f.write_str("quotient"),
            Self::QuotientPiece(i) => write!(f, "quotient_piece_{i}"),
            Self::Custom(s) => write!(f, "custom({s})"),
            Self::NoLabel => f.write_str("no_label"),
        }
    }
}

/// A polynomial query at a point
#[derive(Debug, Clone)]
pub struct ProverQuery<'com, F: PrimeField> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Reference to the queried polynomial.
    pub(crate) poly: &'com Polynomial<F, Coeff>,
    /// Label identifying the queried polynomial.
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
    /// Commitment containing the queried polynomial.
    pub(crate) commitment: &'com CS::Commitment,
    /// Label identifying which polynomial within the commitment is queried.
    pub(crate) label: PolynomialLabel,
    /// Evaluation of polynomial at query point.
    pub(crate) eval: F,
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
        label: PolynomialLabel,
        eval: F,
    ) -> Self {
        VerifierQuery {
            point,
            commitment,
            label,
            eval,
        }
    }
}
