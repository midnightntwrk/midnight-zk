//! fflonk commitment type.
//!
//! A [`FflonkCommitment`] is the output of one `commit` call.
//!
//! - [`FflonkCommitment::Regular`] variant holds one G1 point per bundle
//!   produced by `partition`, each paired with the labels of the `t =
//!   labels.len()` polynomials packed into it via `combine`.
//! - [`FflonkCommitment::Linear`] is a lazy linear combination: a
//!   verifier-internal deferred MSM `\sum scalars[i] points[i]` accumulated
//!   symbolically by `Add`/`Mul` on single `t=1` bundles for linearization, and
//!   collapsed to one group element only when the guard verifies. It is never
//!   serialized or hashed.

use std::{
    io::{self, Read},
    ops::{Add, Mul},
};

use ff::Field;
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;

use crate::{
    poly::query::PolynomialLabel,
    transcript::{Hashable, TranscriptHash},
    utils::helpers::{ProcessedSerdeObject, SerdeFormat},
};

/// A fflonk commitment: the output of a single `commit` call.
#[derive(Clone, Debug)]
pub enum FflonkCommitment<E: MultiMillerLoop> {
    /// One `(point, labels)` pair per bundle, where `point` commits to the
    /// `labels.len()` polynomials combined into it. The bundle is interpreted
    /// as a combination of `t = labels.len().next_power_of_two()` polynomials
    /// (unused slots zero-padded), since the `t`-th roots fflonk opens at
    /// require `t` to be a power of two.
    Regular(Vec<(E::G1, Vec<PolynomialLabel>)>),
    /// Verifier-internal lazy linear combination `\sum scalars[i] * points[i]`
    /// with per-term labels, produced by `Add`/`Mul` on `t=1` bundles. Never
    /// serialized or hashed.
    Linear(Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>),
}

impl<E: MultiMillerLoop> FflonkCommitment<E> {
    /// A commitment to the zero polynomial: a single singleton bundle at the
    /// identity point, carrying `label`.
    pub fn commitment_to_zero(label: PolynomialLabel) -> Self {
        Self::Regular(vec![(E::G1::identity(), vec![label])])
    }

    /// Returns a reference to the inner curve point. Panics unless the
    /// commitment is a single `Regular` bundle.
    pub fn as_point(&self) -> &E::G1 {
        self.single_point().expect("expected a single-bundle Regular FflonkCommitment")
    }

    /// Like [`as_point`](Self::as_point), but returns `None` instead of
    /// panicking. Used on commitments read off the transcript, where a
    /// malformed proof must be rejected rather than crash the verifier.
    pub(super) fn single_point(&self) -> Option<&E::G1> {
        match self {
            Self::Regular(pairs) => match pairs.as_slice() {
                [(point, _)] => Some(point),
                _ => None,
            },
            Self::Linear(..) => None,
        }
    }

    /// Bundle count as the `u8` written on the wire, so a commitment may hold
    /// at most 255 bundles.
    fn count_u8(len: usize) -> u8 {
        u8::try_from(len).expect("FflonkCommitment holds more than 255 bundles.")
    }

    /// Polynomial count of a single bundle as the `u8` written on the wire.
    /// Bounded by `t_max = 1 << FFLONK_T_MAX_LOG`, well under 255.
    fn size_u8(size: usize) -> u8 {
        u8::try_from(size).expect("fflonk bundle packs more than 255 polynomials.")
    }

    /// Decomposes into `(points, scalars, labels)` for `Add`/`Mul`. A single
    /// `t=1` `Regular` bundle becomes a one-term combination with scalar `1`; a
    /// `Linear` returns its parts unchanged. Panics on `t > 1`.
    fn into_linear_parts(self) -> (Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>) {
        match self {
            Self::Regular(pairs) => {
                assert_eq!(
                    pairs.len(),
                    1,
                    "Add/Mul on FflonkCommitment requires exactly one bundle"
                );
                let (p, labels) = pairs.into_iter().next().unwrap();
                assert_eq!(
                    labels.len(),
                    1,
                    "Add/Mul requires t=1; got t={}",
                    labels.len()
                );
                (vec![p], vec![E::Fr::ONE], labels)
            }
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        }
    }

    /// Locate the bundle inside a `Regular` commitment's `pairs` whose label
    /// set contains `label`. Used by `FflonkScheme::multi_prepare` to
    /// recover bundle structure from the verifier's commitment objects.
    pub(super) fn find_bundle<'a>(
        pairs: &'a [(E::G1, Vec<PolynomialLabel>)],
        label: &PolynomialLabel,
    ) -> &'a (E::G1, Vec<PolynomialLabel>) {
        pairs
            .iter()
            .find(|(_, labels)| labels.contains(label))
            .expect("fflonk multi_prepare: query label not found in any bundle of its commitment")
    }

    /// Canonical synthetic label for a `t > 1` bundle. Both prover and verifier
    /// compute this for the same bundle.
    pub(super) fn synthetic_bundle_label(bundle_labels: &[PolynomialLabel]) -> PolynomialLabel {
        let first = bundle_labels.first().expect("fflonk: multi-poly bundle must be non-empty");
        PolynomialLabel::Custom(format!("fflonk_bundle[{first}]"))
    }
}

impl<E: MultiMillerLoop> FflonkCommitment<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    /// Parses the wire format: a bundle count, then per bundle the number of
    /// polynomials it packs and its point. Labels are not on the wire, so each
    /// bundle comes back with that count alone; see the wire-format doc on the
    /// [`ProcessedSerdeObject`] impl.
    fn read_wire<R: io::Read>(
        reader: &mut R,
        format: SerdeFormat,
    ) -> io::Result<Vec<(E::G1, usize)>> {
        let mut byte = [0u8; 1];
        reader.read_exact(&mut byte)?;
        let nb_bundles = byte[0] as usize;
        (0..nb_bundles)
            .map(|_| {
                reader.read_exact(&mut byte)?;
                let size = byte[0] as usize;
                Ok((E::G1::read(reader, format)?, size))
            })
            .collect()
    }

    /// Reads a commitment and tags each bundle with its share of `labels`, in a
    /// single pass. The chunk boundaries come from the per-bundle sizes on the
    /// wire, since the prover's effective bundling factor depends on the SRS,
    /// which the verifier cannot inspect. The ordering within those chunks is
    /// `t_max`-independent and re-derived here through
    /// [`canonical_order`](super::partition::canonical_order), so both sides
    /// agree on the slot assignment whatever order `labels` are supplied in.
    ///
    /// A commitment whose sizes do not add up to `labels.len()` is rejected as
    /// invalid data: the verifier expects a different number of polynomials
    /// than the prover committed to.
    pub(super) fn read_labeled<R: io::Read>(
        reader: &mut R,
        format: SerdeFormat,
        labels: &[PolynomialLabel],
    ) -> io::Result<Self> {
        let ordered: Vec<PolynomialLabel> = super::partition::canonical_order(labels)
            .into_iter()
            .map(|i| labels[i].clone())
            .collect();
        let mut rest = ordered.as_slice();

        let pairs = Self::read_wire(reader, format)?
            .into_iter()
            .map(|(point, size)| {
                if size > rest.len() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "FflonkCommitment: bundle packs {size} polynomials but only {} labels \
                             are left",
                            rest.len()
                        ),
                    ));
                }
                let (chunk, tail) = rest.split_at(size);
                rest = tail;
                Ok((point, chunk.to_vec()))
            })
            .collect::<io::Result<Vec<_>>>()?;

        if !rest.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "FflonkCommitment: {} labels were supplied but the commitment carries fewer \
                     polynomials",
                    labels.len()
                ),
            ));
        }
        Ok(Self::Regular(pairs))
    }

    /// Attaches `labels` to a commitment read off a transcript, whose bundles
    /// carry `NoLabel` placeholders because `Hashable::read` takes no labels.
    /// The keys path parses and tags in one pass instead, see
    /// [`read_labeled`](Self::read_labeled).
    ///
    /// The chunk boundaries come from the per-bundle sizes carried on the wire:
    /// the prover's effective bundling factor depends on the SRS, which the
    /// verifier cannot inspect. The ordering within those chunks is
    /// `t_max`-independent and re-derived here through
    /// [`canonical_order`](super::partition::canonical_order), so both sides
    /// agree on the slot assignment whatever order `labels` are supplied in.
    ///
    /// # Panics
    /// If `labels.len()` differs from the polynomial count the commitment
    /// carries, i.e. the verifier expects a different number of polynomials
    /// than the prover committed to.
    pub(super) fn with_labels(self, labels: &[PolynomialLabel]) -> Self {
        match self {
            Self::Regular(pairs) => {
                let total: usize = pairs.iter().map(|(_, l)| l.len()).sum();
                assert_eq!(
                    total,
                    labels.len(),
                    "FflonkCommitment: commitment carries {total} polynomials but {} labels were \
                     supplied",
                    labels.len(),
                );
                let ordered: Vec<PolynomialLabel> = super::partition::canonical_order(labels)
                    .into_iter()
                    .map(|i| labels[i].clone())
                    .collect();
                let mut rest = ordered.as_slice();
                let new_pairs = pairs
                    .into_iter()
                    .map(|(p, placeholders)| {
                        let (chunk, tail) = rest.split_at(placeholders.len());
                        rest = tail;
                        (p, chunk.to_vec())
                    })
                    .collect();
                Self::Regular(new_pairs)
            }
            Self::Linear(..) => panic!("FflonkCommitment::Linear is never deserialized"),
        }
    }
}

// Manual `PartialEq` (deriving would demand `E: PartialEq`; only
// `E::G1`/`E::Fr` are ever compared). Equality is on the committed points alone
// (plus a `Linear`'s scalars): a commitment's identity is its curve points, and
// labels are routing metadata attached after reading.
impl<E: MultiMillerLoop> PartialEq for FflonkCommitment<E>
where
    E::G1: PartialEq,
    E::Fr: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Regular(a), Self::Regular(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|((p, _), (q, _))| p == q)
            }
            (Self::Linear(ps, rs, _), Self::Linear(qs, ss, _)) => ps == qs && rs == ss,
            _ => false,
        }
    }
}

impl<E: MultiMillerLoop> Default for FflonkCommitment<E>
where
    E::G1: Default,
{
    fn default() -> Self {
        Self::Regular(vec![(E::G1::default(), vec![PolynomialLabel::NoLabel])])
    }
}

/// Wire format: `u8 num_bundles`, then per bundle a `u8` count of the
/// polynomials it packs followed by its G1 point. The counts make the grouping
/// self-describing, which the verifier needs: the prover's effective bundling
/// factor depends on the SRS and is not recoverable verifier-side. Labels
/// themselves are never encoded, so `read` is unimplemented; commitments are
/// read through `read_commitment` (from a transcript) or
/// `deserialize_commitment` (from keys), whose `labels` argument tags each
/// polynomial.
impl<E: MultiMillerLoop> ProcessedSerdeObject for FflonkCommitment<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    fn read<R: io::Read>(_reader: &mut R, _format: SerdeFormat) -> io::Result<Self> {
        unimplemented!(
            "use `PolynomialCommitmentScheme::deserialize_commitment` to read a labeled commitment"
        )
    }

    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        match self {
            Self::Regular(pairs) => {
                writer.write_all(&[Self::count_u8(pairs.len())])?;
                for (p, labels) in pairs {
                    writer.write_all(&[Self::size_u8(labels.len())])?;
                    p.write(writer, format)?;
                }
                Ok(())
            }
            Self::Linear(..) => panic!("FflonkCommitment::Linear cannot be serialized"),
        }
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        match self {
            Self::Regular(pairs) => {
                1 + pairs.iter().map(|(p, _)| 1 + p.byte_length(format)).sum::<usize>()
            }
            Self::Linear(..) => panic!("FflonkCommitment::Linear has no fixed byte length"),
        }
    }
}

impl<H: TranscriptHash, E: MultiMillerLoop> Hashable<H> for FflonkCommitment<E>
where
    E::G1: Hashable<H> + Default + ProcessedSerdeObject,
{
    fn to_input(&self) -> H::Input {
        match self {
            Self::Regular(pairs) => pairs.iter().flat_map(|(p, _)| p.to_input()).collect(),
            Self::Linear(..) => panic!("FflonkCommitment::Linear cannot be hashed"),
        }
    }

    // `to_bytes` / `read` share the `ProcessedSerdeObject` wire format:
    // `SerdeFormat::Processed` is the compressed `GroupEncoding` the transcript
    // uses, so the framing and per-point bytes are identical. Delegate rather
    // than duplicate. (`to_input` cannot: it yields `H::Input`, not bytes.)
    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        <Self as ProcessedSerdeObject>::write(self, &mut bytes, SerdeFormat::Processed)
            .expect("writing to a Vec is infallible");
        bytes
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let pairs = Self::read_wire(buffer, SerdeFormat::Processed)?
            .into_iter()
            .map(|(point, size)| (point, vec![PolynomialLabel::NoLabel; size]))
            .collect();
        Ok(Self::Regular(pairs))
    }
}

impl<E: MultiMillerLoop> Mul<E::Fr> for FflonkCommitment<E> {
    type Output = Self;

    /// Only valid for a single `t == 1` bundle (or an existing `Linear`).
    /// Panics otherwise: a `t > 1` commitment cannot enter linearization, since
    /// a scalar mul would scale all slots uniformly.
    fn mul(self, scalar: E::Fr) -> Self {
        match self {
            Self::Linear(points, scalars, labels) => Self::Linear(
                points,
                scalars.into_iter().map(|s| s * scalar).collect(),
                labels,
            ),
            committed => {
                let (points, _, labels) = committed.into_linear_parts();
                Self::Linear(points, vec![scalar], labels)
            }
        }
    }
}

impl<E: MultiMillerLoop> Add for FflonkCommitment<E> {
    type Output = Self;

    /// Single `t == 1` bundles (or existing `Linear`s) fold into a `Linear`
    /// deferred MSM for linearization. Two `t > 1` bundles with identical
    /// layout (same size and labels) add homomorphically into a single
    /// point, since `combine` and KZG commitment are both linear. Any other
    /// `t > 1` combination panics.
    fn add(self, other: Self) -> Self {
        // Same-layout t>1 bundles: `commit(P) + commit(Q) = commit(P + Q)`,
        // still a single point over the same slots.
        if let (Self::Regular(a), Self::Regular(b)) = (&self, &other)
            && let ([(pa, la)], [(pb, lb)]) = (a.as_slice(), b.as_slice())
            && la.len() > 1
            && la == lb
        {
            return Self::Regular(vec![(*pa + *pb, la.clone())]);
        }
        let (mut points, mut scalars, mut labels) = self.into_linear_parts();
        let (other_points, other_scalars, other_labels) = other.into_linear_parts();
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Self::Linear(points, scalars, labels)
    }
}
