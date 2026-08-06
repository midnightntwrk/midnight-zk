//! fflonk commitment type.
//!
//! A [`FflonkCommitment`] is the output of one `commit` call. Its
//! [`FflonkCommitment::Regular`] variant holds one G1 point per bundle
//! produced by `partition`, each paired with the labels of the
//! `t = labels.len()` polynomials packed into it via `combine` (paper's
//! `combine_t`); `t` may be 1.
//!
//! [`FflonkCommitment::Linear`] is a *lazy linear combination*: a
//! verifier-internal deferred MSM `Σ scalars[i]·points[i]` accumulated
//! symbolically by `Add`/`Mul` on single `t=1` bundles for linearization, and
//! collapsed to one group element only when the guard verifies. It is never
//! serialized or hashed (unreachable on attempt).
//!
//! # `Add` / `Mul<F>` semantics
//! These trait-level bounds on `Commitment` exist for the linearization MSM
//! (`proofs/src/plonk/linearization/verifier.rs`), which operates on
//! single-polynomial commitments. `Mul`, and `Add` on differently-labelled
//! bundles, require `t == 1` and panic otherwise. `Add` of two `t > 1`
//! bundles with identical layout is supported (homomorphic slot-wise
//! sum); the general per-slot-scalar case remains `t == 1`.

use std::{
    io::{self, Read},
    ops::{Add, Mul},
};

use ff::Field;
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;

use super::FFLONK_T_MAX_LOG;
use crate::{
    pcs::scheme::Labelable,
    poly::query::PolynomialLabel,
    transcript::{Hashable, TranscriptHash},
    utils::helpers::{ProcessedSerdeObject, SerdeFormat},
};

/// A fflonk commitment: the output of a single `commit` call.
#[derive(Clone, Debug)]
pub enum FflonkCommitment<E: MultiMillerLoop> {
    /// A vector of committed points, i.e., a vector of `(g,labels)` where
    /// each `g` is a single G1 element corresponding to `labels.len()` combined
    /// real polynomials labelled by `labels`. In practice, the commitment is
    /// interpreted as a combination of `t =
    /// labels.len().next_power_of_two()` polynomials
    /// (unused slots zero-padded), since computations of roots of unity assume
    /// they are a power of two.
    Regular(Vec<(E::G1, Vec<PolynomialLabel>)>),
    /// Verifier-internal lazy linear combination `\sum scalars[i] * points[i]`
    /// with per-term labels, produced by `Add`/`Mul` on `t=1` bundles.
    /// Never serialized or hashed.
    Linear(Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>),
}

impl<E: MultiMillerLoop> FflonkCommitment<E> {
    /// A commitment to the zero polynomial: a single singleton bundle at
    /// the identity point, carrying `label`.
    pub fn commitment_to_zero(label: PolynomialLabel) -> Self {
        Self::Regular(vec![(E::G1::identity(), vec![label])])
    }

    /// Returns a reference to the inner curve point. Panics unless the
    /// commitment is a single `Regular` bundle.
    pub fn as_point(&self) -> &E::G1 {
        match self {
            Self::Regular(pairs) => {
                assert_eq!(pairs.len(), 1, "as_point requires exactly one bundle");
                &pairs[0].0
            }
            Self::Linear(..) => panic!("expected a Regular FflonkCommitment, got Linear"),
        }
    }

    /// Bundle count as the `u8` written on the wire. The count is
    /// serialized in a single byte, so a commitment may hold at most 255
    /// bundles.
    fn count_u8(len: usize) -> u8 {
        u8::try_from(len).expect("FflonkCommitment holds more than 255 bundles.")
    }

    /// Polynomial count of a single bundle as the `u8` written on the wire.
    /// Bounded by `t_max = 1 << FFLONK_T_MAX_LOG`, well under 255.
    fn size_u8(size: usize) -> u8 {
        u8::try_from(size).expect("fflonk bundle packs more than 255 polynomials.")
    }

    /// Decomposes into `(points, scalars, labels)` for `Add`/`Mul`. A single
    /// `t=1` `Regular` bundle becomes a one-term combination with scalar
    /// `1`; a `Linear` returns its parts unchanged. Panics on `t > 1`.
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
}

// Manual `PartialEq` (deriving would demand `E: PartialEq`; only
// `E::G1`/`E::Fr` are ever compared). Equality is on the committed points alone
// (plus a `Linear`'s scalars): a commitment's identity is its curve points.
// Labels are post-read routing metadata (`NoLabel` until `Labelable::label`
// runs) and are excluded, so a labelled and an unlabelled commitment over the
// same points compare equal.
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

impl<E: MultiMillerLoop> Labelable for FflonkCommitment<E> {
    /// Total number of polynomials across all bundles.
    ///
    /// Freshly-deserialized commitments carry `NoLabel` placeholders (one per
    /// polynomial, from the on-wire per-bundle counts), so this already
    /// equals the number of polynomials originally committed, before
    /// [`Labelable::label`] replaces the placeholders with real labels.
    fn length(&self) -> usize {
        match self {
            Self::Regular(pairs) => pairs.iter().map(|(_, labels)| labels.len()).sum(),
            Self::Linear(_, _, labels) => labels.len(),
        }
    }

    /// Attaches `labels` across bundles. The prover's effective bundling
    /// factor may be smaller than `1 << FFLONK_T_MAX_LOG` (when the SRS or
    /// field 2-adicity cannot afford the full bundle) and the verifier
    /// cannot recompute it, so the *chunk boundaries* are taken from the
    /// per-bundle sizes carried on the wire (`read` pre-fills each pair
    /// with that many `NoLabel` placeholders). The *ordering* within those
    /// chunks is `t_max`-independent and re-derived here via
    /// `partition::canonical_order`, so both sides agree on the slot
    /// assignment regardless of the order `labels` are supplied in.
    ///
    /// # Panics
    /// If `labels.len()` differs from the total polynomial count the commitment
    /// carries (mismatch between the labels the verifier expects and the
    /// commitment the prover wrote).
    fn label(self, labels: &[PolynomialLabel]) -> Self {
        match self {
            Self::Regular(pairs) => {
                let total: usize = pairs.iter().map(|(_, l)| l.len()).sum();
                assert_eq!(
                    total,
                    labels.len(),
                    "FflonkCommitment::label: commitment carries {total} polynomials but \
                     {} labels were supplied",
                    labels.len(),
                );
                let ordered: Vec<PolynomialLabel> = super::partition::canonical_order(labels)
                    .into_iter()
                    .map(|i| labels[i].clone())
                    .collect();
                let mut rest = ordered.as_slice();
                let new_pairs = pairs
                    .into_iter()
                    .map(|(p, placeholder)| {
                        let (chunk, tail) = rest.split_at(placeholder.len());
                        rest = tail;
                        (p, chunk.to_vec())
                    })
                    .collect();
                Self::Regular(new_pairs)
            }
            // `Linear` is verifier-internal and never deserialized, so this is
            // not exercised in practice; attach the labels flat for robustness.
            Self::Linear(points, scalars, _) => Self::Linear(points, scalars, labels.to_vec()),
        }
    }
}

/// Wire format: `u8 num_bundles`, then each bundle's G1 point. When
/// `FFLONK_T_MAX_LOG != 0` a `u8` count of the polynomials the bundle packs
/// precedes its point, making the grouping self-describing: the verifier splits
/// the labels it expects according to those counts (see [`Labelable::label`])
/// rather than re-deriving the partition, which it could not — the prover's
/// effective bundling factor depends on the SRS and is not recoverable
/// verifier-side. At `FFLONK_T_MAX_LOG = 0` every bundle is a singleton, so
/// the counts are all `1` and omitted, keeping the wire byte-identical to KZG.
/// Labels themselves are never encoded.
impl<E: MultiMillerLoop> ProcessedSerdeObject for FflonkCommitment<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut byte = [0u8; 1];
        reader.read_exact(&mut byte)?;
        let len = byte[0] as usize;
        let pairs = (0..len)
            .map(|_| {
                let size = read_bundle_size(reader)?;
                let point = E::G1::read(reader, format)?;
                Ok((point, vec![PolynomialLabel::NoLabel; size]))
            })
            .collect::<io::Result<Vec<_>>>()?;
        Ok(Self::Regular(pairs))
    }

    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        match self {
            Self::Regular(pairs) => {
                writer.write_all(&[Self::count_u8(pairs.len())])?;
                for (p, labels) in pairs {
                    if FFLONK_T_MAX_LOG != 0 {
                        writer.write_all(&[Self::size_u8(labels.len())])?;
                    }
                    p.write(writer, format)?;
                }
                Ok(())
            }
            Self::Linear(..) => unreachable!("FflonkCommitment::Linear cannot be serialized"),
        }
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        match self {
            Self::Regular(pairs) => {
                let size_prefix = if FFLONK_T_MAX_LOG != 0 { 1 } else { 0 };
                1 + pairs.iter().map(|(p, _)| size_prefix + p.byte_length(format)).sum::<usize>()
            }
            Self::Linear(..) => unreachable!("FflonkCommitment::Linear has no fixed byte length"),
        }
    }
}

/// Reads a bundle's polynomial-count prefix, or `1` when
/// `FFLONK_T_MAX_LOG = 0` (all bundles are singletons and the count is not
/// on the wire). Shared by the `ProcessedSerdeObject` and `Hashable` readers.
fn read_bundle_size(reader: &mut impl Read) -> io::Result<usize> {
    if FFLONK_T_MAX_LOG == 0 {
        return Ok(1);
    }
    let mut byte = [0u8; 1];
    reader.read_exact(&mut byte)?;
    Ok(byte[0] as usize)
}

impl<H: TranscriptHash, E: MultiMillerLoop> Hashable<H> for FflonkCommitment<E>
where
    E::G1: Hashable<H> + Default + ProcessedSerdeObject,
{
    fn to_input(&self) -> H::Input {
        match self {
            Self::Regular(pairs) => pairs.iter().flat_map(|(p, _)| p.to_input()).collect(),
            Self::Linear(..) => unreachable!("FflonkCommitment::Linear cannot be hashed"),
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
        <Self as ProcessedSerdeObject>::read(buffer, SerdeFormat::Processed)
    }
}

impl<E: MultiMillerLoop> Mul<E::Fr> for FflonkCommitment<E> {
    type Output = Self;

    /// Only valid for a single `t == 1` bundle (or an existing `Linear`).
    /// Panics otherwise: a `t > 1` commitment cannot enter linearization
    /// (scalar mul would scale all slots uniformly).
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

    /// Single `t == 1` bundles (or existing `Linear`s) fold into a
    /// `Linear` deferred MSM for linearization. Two `t > 1` bundles with
    /// identical layout (same size and labels) add homomorphically into a
    /// single point, since `combine` and KZG commitment are both linear.
    /// Any other `t > 1` combination panics.
    fn add(self, other: Self) -> Self {
        // Same-layout t>1 bundles: `commit(P) + commit(Q) = commit(P + Q)`,
        // still a single point over the same slots.
        if let (Self::Regular(a), Self::Regular(b)) = (&self, &other) {
            if let ([(pa, la)], [(pb, lb)]) = (a.as_slice(), b.as_slice()) {
                if la.len() > 1 && la == lb {
                    return Self::Regular(vec![(*pa + *pb, la.clone())]);
                }
            }
        }
        let (mut points, mut scalars, mut labels) = self.into_linear_parts();
        let (other_points, other_scalars, other_labels) = other.into_linear_parts();
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Self::Linear(points, scalars, labels)
    }
}

/// Canonical synthetic label for a `t > 1` bundle. Both prover and
/// verifier compute this for the same bundle.
pub(super) fn synthetic_bundle_label(bundle_labels: &[PolynomialLabel]) -> PolynomialLabel {
    let first = bundle_labels.first().expect("fflonk: multi-poly bundle must be non-empty");
    PolynomialLabel::Custom(format!("fflonk_bundle[{}]", first))
}

impl<E: MultiMillerLoop> FflonkCommitment<E> {
    /// Locate the bundle inside a `Regular` commitment's `pairs` whose
    /// label set contains `label`. Used by `FflonkScheme::multi_prepare` to
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
}
