use std::{
    io::{self, Read},
    ops::{Add, Mul},
};

use ff::Field;
use midnight_curves::{pairing::MultiMillerLoop, CurveAffine};

use crate::{
    poly::{commitment::Labelable, kzg::msm::MSMKZG, query::PolynomialLabel},
    transcript::{Hashable, TranscriptHash},
    utils::helpers::{ProcessedSerdeObject, SerdeFormat},
};

/// A KZG commitment: either a single curve point, or a lazy linear combination
/// of curve points kept unevaluated for MSM batching.
///
/// Each point carries a [`PolynomialLabel`] that identifies its role in the
/// protocol (e.g. `Fixed(i)`, `Advice(i)`).  Labels are protocol-level
/// metadata; they are not included in serialization or hashing.
///
/// # Serialization invariant
///
/// Only `Simple` commitments are ever serialized or hashed.  `Linear`
/// is a **verifier-internal** structure: the verifier assembles it from
/// individually deserialized `Simple` points (via [`Mul`] and [`Add`]) so
/// that all scalar multiplications can be batched in a single multi-scalar
/// multiplication at the end of
/// [`crate::poly::commitment::PolynomialCommitmentScheme::multi_prepare`].
/// It is therefore a programming error to attempt to serialize or hash a
/// `Linear` commitment; the corresponding trait methods panic.
#[derive(Clone, Debug)]
pub enum KZGCommitment<E: MultiMillerLoop> {
    /// A single committed point with its label.
    Simple(E::G1, PolynomialLabel),
    /// A lazy linear combination `∑ scalars[i] * points[i]` with per-term
    /// labels, accumulated during verification for MSM batching.
    /// Never serialized or hashed directly.
    Linear(Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>),
}

// We implement `PartialEq` manually because its derivation would require
// `E: PartialEq`. In practice, only `E::G1` and `E::Fr` need it;
// `E` itself never appears directly in a comparison.
impl<E: MultiMillerLoop> PartialEq for KZGCommitment<E>
where
    E::G1: PartialEq,
    E::Fr: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Simple(p, l), Self::Simple(q, m)) => p == q && l == m,
            (Self::Linear(ps, rs, ls), Self::Linear(qs, ss, ms)) => {
                ps == qs && rs == ss && ls == ms
            }
            (Self::Simple(..), Self::Linear(..)) | (Self::Linear(..), Self::Simple(..)) => false,
        }
    }
}

impl<E: MultiMillerLoop> KZGCommitment<E> {
    /// Extracts the inner curve point, panicking if this is a `Linear`
    /// commitment.
    pub fn into_point(self) -> E::G1 {
        match self {
            Self::Simple(p, _) => p,
            Self::Linear(..) => panic!("expected KZGCommitment::Simple"),
        }
    }

    /// Returns a reference to the inner curve point, panicking if this is a
    /// `Linear` commitment.
    pub fn as_point(&self) -> &E::G1 {
        match self {
            Self::Simple(p, _) => p,
            Self::Linear(..) => panic!("expected KZGCommitment::Simple"),
        }
    }
}

impl<E: MultiMillerLoop> KZGCommitment<E>
where
    E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    /// Collapses a `Linear` combination into a `Simple` commitment by computing
    /// the MSM `∑ scalars[i] * points[i]`.
    ///
    /// A `Simple` commitment is left unchanged.
    /// After the call, the result always has scalar `1` and label `Collapsed`.
    pub fn collapse(&mut self) {
        match self {
            Self::Simple(_, _) => (),
            Self::Linear(points, scalars, labels) => {
                let mut msm = MSMKZG::<E>::new(scalars, points, labels);
                msm.collapse();
                debug_assert_eq!(msm.bases.len(), 1);
                debug_assert_eq!(msm.scalars, vec![E::Fr::ONE]);
                *self = Self::Simple(msm.bases[0], msm.labels[0].clone());
            }
        }
    }
}

impl<E: MultiMillerLoop> From<KZGCommitment<E>> for MSMKZG<E> {
    fn from(commitment: KZGCommitment<E>) -> Self {
        match commitment {
            KZGCommitment::Simple(p, label) => MSMKZG::new(&[E::Fr::ONE], &[p], &[label]),
            KZGCommitment::Linear(points, scalars, labels) => {
                MSMKZG::new(&scalars, &points, &labels)
            }
        }
    }
}

impl<E: MultiMillerLoop> Default for KZGCommitment<E>
where
    E::G1: Default,
{
    fn default() -> Self {
        Self::Simple(E::G1::default(), PolynomialLabel::Collapsed)
    }
}

impl<E: MultiMillerLoop> Labelable for KZGCommitment<E> {
    /// Adds a label to the KZG commitment.
    ///
    /// # Panics
    ///
    /// If the commitment is not `Simple` or if it was already labeled.
    fn label(self, label: PolynomialLabel) -> Self {
        match self {
            Self::Simple(p, PolynomialLabel::NoLabel) => Self::Simple(p, label),
            Self::Simple(_, existing) => panic!("commitment is already labeled: {existing:?}"),
            Self::Linear(_, _, _) => panic!("KZGCommitment::Linear cannot be labeled"),
        }
    }
}

/// Only `Simple` commitments are serialized; see the type-level doc for why
/// `Linear` is never written to or read from a proof directly.
///
/// Labels are not part of the serialized form; deserialized commitments receive
/// [`PolynomialLabel::NoLabel`] and must be labeled at the call site.
impl<E: MultiMillerLoop> ProcessedSerdeObject for KZGCommitment<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        Ok(Self::Simple(
            E::G1::read(reader, format)?,
            PolynomialLabel::NoLabel,
        ))
    }

    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        match self {
            Self::Simple(p, _) => p.write(writer, format),
            Self::Linear(..) => panic!("KZGCommitment::Linear cannot be serialized directly"),
        }
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        match self {
            Self::Simple(p, _) => p.byte_length(format),
            Self::Linear(..) => panic!("KZGCommitment::Linear has no fixed byte length"),
        }
    }
}

/// Only `Simple` commitments are hashed into transcripts; see the type-level
/// doc for why `Linear` is never hashed directly. Labels are not part of the
/// transcript.
impl<H: TranscriptHash, E: MultiMillerLoop> Hashable<H> for KZGCommitment<E>
where
    E::G1: Hashable<H>,
{
    fn to_input(&self) -> H::Input {
        match self {
            Self::Simple(p, _) => p.to_input(),
            Self::Linear(..) => panic!("KZGCommitment::Linear cannot be hashed directly"),
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Self::Simple(p, _) => p.to_bytes(),
            Self::Linear(..) => panic!("KZGCommitment::Linear cannot be serialized to bytes"),
        }
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        Ok(Self::Simple(E::G1::read(buffer)?, PolynomialLabel::NoLabel))
    }
}

impl<E: MultiMillerLoop> Mul<E::Fr> for KZGCommitment<E> {
    type Output = Self;

    fn mul(self, scalar: E::Fr) -> Self {
        match self {
            Self::Simple(p, label) => Self::Linear(vec![p], vec![scalar], vec![label]),
            Self::Linear(points, scalars, labels) => Self::Linear(
                points,
                scalars.into_iter().map(|s| s * scalar).collect(),
                labels,
            ),
        }
    }
}

impl<E: MultiMillerLoop> Add for KZGCommitment<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let (mut points, mut scalars, mut labels) = match self {
            Self::Simple(p, label) => (vec![p], vec![E::Fr::ONE], vec![label]),
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        let (other_points, other_scalars, other_labels) = match other {
            Self::Simple(p, label) => (vec![p], vec![E::Fr::ONE], vec![label]),
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Self::Linear(points, scalars, labels)
    }
}
