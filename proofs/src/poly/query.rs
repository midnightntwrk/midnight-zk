use std::fmt::{self, Debug};

use ff::PrimeField;

use crate::poly::{Coeff, Polynomial, commitment::PolynomialCommitmentScheme};

/// A structured label for polynomial commitments in verifier queries.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PolynomialLabel {
    /// Fixed column commitment (column index).
    Fixed(usize),
    /// Advice column commitment (column index).
    Advice(usize),
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
    /// PLONK quotient polynomial h(X), committed as a single piece.
    Quotient,
    /// PLONK quotient polynomial h(X), committed in pieces (piece index).
    QuotientPiece(usize),
    /// Trash compressed polynomial (argument index).
    Trash(usize),
    /// User-defined label.
    Custom(String),
    /// A label made of the given labels, in order.
    Collection(Vec<PolynomialLabel>),
    /// Absence of a meaningful label. Used for freshly deserialized commitments
    /// (before a label is attached) and for aggregate commitments produced by
    /// collapsing an MSM, which do not correspond to a single polynomial.
    NoLabel,
}

impl PolynomialLabel {
    /// Whether the label names a polynomial of the verifying key: a fixed or
    /// permutation column, or a collection of them.
    pub fn is_fixed(&self) -> bool {
        match self {
            Self::Fixed(_) | Self::PermutationFixed(_) => true,
            Self::Collection(labels) => !labels.is_empty() && labels.iter().all(Self::is_fixed),
            _ => false,
        }
    }

    /// Asserts that no label of `labels` is repeated.
    pub fn assert_distinct(labels: &[Self]) {
        let mut seen = rustc_hash::FxHashSet::default();
        for label in labels {
            assert!(seen.insert(label), "duplicated label {label}");
        }
    }
}

impl fmt::Display for PolynomialLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fixed(i) => write!(f, "fixed_{i}"),
            Self::Advice(i) => write!(f, "advice_{i}"),
            Self::CommittedInstance(i) => write!(f, "committed_instance_{i}"),
            Self::PermutationFixed(i) => write!(f, "perm_fixed_{i}"),
            Self::PermutationAccumulator(i) => write!(f, "perm_acc_{i}"),
            Self::LogupHelper(i, j) => write!(f, "logup_helper({i}, {j})"),
            Self::LogupMultiplicities(i) => write!(f, "logup_multiplicities({i})"),
            Self::LogupAggregator(i) => write!(f, "logup_aggregator({i})"),
            Self::Trash(i) => write!(f, "trash({i})"),
            Self::Quotient => f.write_str("quotient"),
            Self::QuotientPiece(i) => write!(f, "quotient_piece_{i}"),
            Self::Custom(s) => write!(f, "custom({s})"),
            Self::Collection(labels) => {
                let labels: Vec<_> = labels.iter().map(ToString::to_string).collect();
                write!(f, "collection({})", labels.join(", "))
            }
            Self::NoLabel => f.write_str("no_label"),
        }
    }
}

/// A query of a polynomial at a point. The polynomial is identified by its
/// label within the group of polynomials it was committed to together with.
#[derive(Debug, Clone)]
pub struct ProverQuery<'com, F: PrimeField> {
    /// Labels of every polynomial committed to together with the queried one.
    pub(crate) group_labels: &'com [PolynomialLabel],
    /// The polynomials of `group_labels`, in the same order.
    pub(crate) group_polys: &'com [Polynomial<F, Coeff>],
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Label identifying which polynomial within the group is queried.
    pub(crate) label: PolynomialLabel,
}

impl<'com, F: PrimeField> ProverQuery<'com, F> {
    /// Create a new prover query on the polynomial labelled `label` of the
    /// group of `group_polys`, labelled `group_labels`.
    pub fn new(
        group_labels: &'com [PolynomialLabel],
        group_polys: &'com [Polynomial<F, Coeff>],
        point: F,
        label: PolynomialLabel,
    ) -> Self {
        ProverQuery {
            group_labels,
            group_polys,
            point,
            label,
        }
    }

    /// The queried polynomial.
    ///
    /// # Panics
    ///
    /// Panics if the group holds no polynomial under the query label.
    pub(crate) fn poly(&self) -> &'com Polynomial<F, Coeff> {
        let i = (self.group_labels.iter().position(|l| *l == self.label))
            .expect("the queried group has no polynomial under the query label");
        &self.group_polys[i]
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
