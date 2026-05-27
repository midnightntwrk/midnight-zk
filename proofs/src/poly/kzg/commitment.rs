use std::{
    io::{self, Read},
    ops::{Add, Mul},
};

use ff::Field;
use midnight_curves::pairing::MultiMillerLoop;

use crate::{
    poly::{commitment::Labelable, query::PolynomialLabel},
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
    /// labels, accumulated during verification for MSM batching.  Never
    /// serialized or hashed directly.
    Linear(Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>),
}

impl<E: MultiMillerLoop> PartialEq for KZGCommitment<E>
where
    E::G1: PartialEq,
    E::Fr: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Simple(p, _), Self::Simple(q, _)) => p == q,
            (Self::Linear(ps, rs, _), Self::Linear(qs, ss, _)) => ps == qs && rs == ss,
            _ => false,
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

impl<E: MultiMillerLoop> Default for KZGCommitment<E>
where
    E::G1: Default,
{
    fn default() -> Self {
        Self::Simple(E::G1::default(), PolynomialLabel::Collapsed)
    }
}

impl<E: MultiMillerLoop> Labelable for KZGCommitment<E> {
    fn length(&self) -> usize {
        1
    }

    fn label(self, labels: Vec<PolynomialLabel>) -> Self {
        assert_eq!(
            labels.len(),
            1,
            "KZGCommitment holds exactly one polynomial"
        );
        let label = labels.into_iter().next().unwrap();
        match self {
            Self::Simple(p, _) => Self::Simple(p, label),
            Self::Linear(points, scalars, old_labels) => Self::Linear(
                points,
                scalars,
                old_labels.into_iter().map(|_| label.clone()).collect(),
            ),
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

/// A KZG commitment to one or more polynomials.
///
/// Each inner [`KZGCommitment`] corresponds to one polynomial. All current
/// protocol uses hold exactly one polynomial; multi-polynomial support is
/// reserved for future batching schemes.
#[derive(Clone, Debug)]
pub struct KZGMultiCommitment<E: MultiMillerLoop>(pub Vec<KZGCommitment<E>>);

impl<E: MultiMillerLoop> KZGMultiCommitment<E> {
    fn assert_single(&self) {
        assert_eq!(
            self.0.len(),
            1,
            "Add/Mul on KZGMultiCommitment requires exactly one polynomial"
        );
    }

    /// Returns a reference to the inner curve point, panicking if this
    /// commitment does not hold exactly one polynomial.
    pub fn as_point(&self) -> &E::G1 {
        self.assert_single();
        self.0[0].as_point()
    }

    /// Extracts the inner curve point, panicking if this commitment does not
    /// hold exactly one polynomial.
    pub fn into_point(self) -> E::G1 {
        self.assert_single();
        self.0.into_iter().next().unwrap().into_point()
    }
}

impl<E: MultiMillerLoop> PartialEq for KZGMultiCommitment<E>
where
    E::G1: PartialEq,
    E::Fr: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<E: MultiMillerLoop> Default for KZGMultiCommitment<E>
where
    E::G1: Default,
{
    fn default() -> Self {
        Self(vec![KZGCommitment::default()])
    }
}

impl<E: MultiMillerLoop> Labelable for KZGMultiCommitment<E> {
    fn length(&self) -> usize {
        self.0.len()
    }

    fn label(self, labels: Vec<PolynomialLabel>) -> Self {
        assert_eq!(
            labels.len(),
            self.0.len(),
            "label count must match polynomial count"
        );
        Self(self.0.into_iter().zip(labels).map(|(c, l)| c.label(vec![l])).collect())
    }
}

impl<E: MultiMillerLoop> ProcessedSerdeObject for KZGMultiCommitment<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut len_bytes = [0u8; 4];
        reader.read_exact(&mut len_bytes)?;
        let len = u32::from_le_bytes(len_bytes) as usize;
        let inner = (0..len)
            .map(|_| <KZGCommitment<E> as ProcessedSerdeObject>::read(reader, format))
            .collect::<io::Result<Vec<_>>>()?;
        Ok(Self(inner))
    }

    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        let len = self.0.len() as u32;
        writer.write_all(&len.to_le_bytes())?;
        for c in &self.0 {
            c.write(writer, format)?;
        }
        Ok(())
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        4 + self.0.iter().map(|c| c.byte_length(format)).sum::<usize>()
    }
}

impl<H: TranscriptHash, E: MultiMillerLoop> Hashable<H> for KZGMultiCommitment<E>
where
    E::G1: Hashable<H>,
{
    fn to_input(&self) -> H::Input {
        self.0.iter().flat_map(|c| c.to_input()).collect()
    }

    fn to_bytes(&self) -> Vec<u8> {
        let len = self.0.len() as u32;
        let mut bytes = len.to_le_bytes().to_vec();
        for c in &self.0 {
            bytes.extend_from_slice(&c.to_bytes());
        }
        bytes
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut len_bytes = [0u8; 4];
        buffer.read_exact(&mut len_bytes)?;
        let len = u32::from_le_bytes(len_bytes) as usize;
        let inner = (0..len)
            .map(|_| <KZGCommitment<E> as Hashable<H>>::read(buffer))
            .collect::<io::Result<Vec<_>>>()?;
        Ok(Self(inner))
    }
}

impl<E: MultiMillerLoop> Mul<E::Fr> for KZGMultiCommitment<E> {
    type Output = Self;

    fn mul(self, scalar: E::Fr) -> Self {
        self.assert_single();
        Self(vec![self.0.into_iter().next().unwrap() * scalar])
    }
}

impl<E: MultiMillerLoop> Add for KZGMultiCommitment<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.assert_single();
        other.assert_single();
        Self(vec![
            self.0.into_iter().next().unwrap() + other.0.into_iter().next().unwrap(),
        ])
    }
}
