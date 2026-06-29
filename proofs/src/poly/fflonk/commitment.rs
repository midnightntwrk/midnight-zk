//! fflonk commitment types.
//!
//! A [`FflonkCommitment`] is the output of one `commit` call: a `Vec` of
//! [`FflonkBundle`]s, one per sub-bundle produced by [`partition`]. Each
//! [`FflonkBundle::Bundle`] holds a single G1 commitment to `t = labels.len()`
//! polynomials packed via `combine` (paper's `combine_t`).
//!
//! [`FflonkBundle::Linear`] is a verifier-internal deferred-MSM accumulator
//! produced by `Add`/`Mul<F>` on `t=1` sub-bundles, used by linearization.
//! It is never serialized or hashed (panic on attempt).
//!
//! # `Add` / `Mul<F>` semantics
//! These trait-level bounds on `Commitment` exist for the linearization MSM
//! (`proofs/src/plonk/linearization/verifier.rs`), which operates on
//! single-polynomial commitments. Attempting `Add`/`Mul` on a sub-bundle
//! with `t > 1` panics. This matches the integration plan: fixed/selector
//! columns that feed linearization stay `t=1` for the first integration.
//!
//! [`partition`]: super::partition::partition

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

/// A single fflonk sub-bundle: one G1 point committing to `t` polynomials
/// packed via `combine`, with their labels stored in commit order.
///
/// `Linear` is verifier-internal; see the module docs.
#[derive(Clone, Debug)]
pub enum FflonkBundle<E: MultiMillerLoop> {
    /// One G1 commitment to `t = labels.len()` polynomials. `t` may be 1.
    Bundle(E::G1, Vec<PolynomialLabel>),
    /// Lazy linear combination `∑ scalars[i] * points[i]` with per-term
    /// labels. Only emitted by `Add`/`Mul` on `t=1` `Bundle`s; never
    /// serialized or hashed.
    Linear(Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>),
}

impl<E: MultiMillerLoop> FflonkBundle<E> {
    /// Number of polynomials this sub-bundle represents
    /// (= `t` for `Bundle`, = number of terms for `Linear`).
    pub fn len(&self) -> usize {
        match self {
            Self::Bundle(_, labels) => labels.len(),
            Self::Linear(_, _, labels) => labels.len(),
        }
    }

    /// Extracts the inner curve point, panicking on `Linear`.
    pub fn into_point(self) -> E::G1 {
        match self {
            Self::Bundle(p, _) => p,
            Self::Linear(..) => panic!("expected FflonkBundle::Bundle"),
        }
    }

    /// Returns a reference to the inner curve point, panicking on `Linear`.
    pub fn as_point(&self) -> &E::G1 {
        match self {
            Self::Bundle(p, _) => p,
            Self::Linear(..) => panic!("expected FflonkBundle::Bundle"),
        }
    }
}

impl<E: MultiMillerLoop> PartialEq for FflonkBundle<E>
where
    E::G1: PartialEq,
    E::Fr: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bundle(p, l1), Self::Bundle(q, l2)) => p == q && l1.len() == l2.len(),
            (Self::Linear(ps, rs, _), Self::Linear(qs, ss, _)) => ps == qs && rs == ss,
            _ => false,
        }
    }
}

impl<E: MultiMillerLoop> Default for FflonkBundle<E>
where
    E::G1: Default,
{
    fn default() -> Self {
        Self::Bundle(E::G1::default(), vec![PolynomialLabel::Collapsed])
    }
}

impl<E: MultiMillerLoop> ProcessedSerdeObject for FflonkBundle<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    /// Wire format: a single G1 point. The bundle's `t` (number of
    /// polynomials packed into this sub-bundle) is not encoded — it is
    /// recovered from [`partition`](super::partition::partition) by
    /// [`Labelable::label`] on the enclosing [`FflonkCommitment`]. Labels
    /// are an empty placeholder after deserialization and must be attached
    /// via `label`.
    ///
    /// Choosing not to encode `t` keeps the wire format symmetric with
    /// `KZGMultiCommitment` so that at `T_MAX_LOG = 0` (every sub-bundle
    /// has `t = 1` ⇒ num_sub_bundles = num_polys), an `FflonkCommitment`
    /// serialises to the same bytes as a `KZGMultiCommitment` holding the
    /// same group elements.
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let p = E::G1::read(reader, format)?;
        Ok(Self::Bundle(p, Vec::new()))
    }

    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        match self {
            Self::Bundle(p, _) => p.write(writer, format),
            Self::Linear(..) => panic!("FflonkBundle::Linear cannot be serialized directly"),
        }
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        match self {
            Self::Bundle(p, _) => p.byte_length(format),
            Self::Linear(..) => panic!("FflonkBundle::Linear has no fixed byte length"),
        }
    }
}

impl<H: TranscriptHash, E: MultiMillerLoop> Hashable<H> for FflonkBundle<E>
where
    E::G1: Hashable<H> + Default + ProcessedSerdeObject,
{
    fn to_input(&self) -> H::Input {
        match self {
            Self::Bundle(p, _) => p.to_input(),
            Self::Linear(..) => panic!("FflonkBundle::Linear cannot be hashed directly"),
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Self::Bundle(p, _) => p.to_bytes(),
            Self::Linear(..) => panic!("FflonkBundle::Linear cannot be serialized to bytes"),
        }
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let p = <E::G1 as Hashable<H>>::read(buffer)?;
        Ok(Self::Bundle(p, Vec::new()))
    }
}

impl<E: MultiMillerLoop> Mul<E::Fr> for FflonkBundle<E> {
    type Output = Self;

    /// Only valid for sub-bundles with `t == 1`. Panics otherwise: bundled
    /// `t > 1` commitments cannot enter linearization (scalar mul would
    /// scale all slots uniformly).
    fn mul(self, scalar: E::Fr) -> Self {
        match self {
            Self::Bundle(p, labels) => {
                assert_eq!(
                    labels.len(),
                    1,
                    "FflonkBundle::Mul: requires t=1; got t={}",
                    labels.len()
                );
                Self::Linear(vec![p], vec![scalar], labels)
            }
            Self::Linear(points, scalars, labels) => Self::Linear(
                points,
                scalars.into_iter().map(|s| s * scalar).collect(),
                labels,
            ),
        }
    }
}

impl<E: MultiMillerLoop> Add for FflonkBundle<E> {
    type Output = Self;

    /// Only valid when both operands have `t == 1` (`Bundle` form). Panics
    /// otherwise.
    fn add(self, other: Self) -> Self {
        let (mut points, mut scalars, mut labels) = match self {
            Self::Bundle(p, labels) => {
                assert_eq!(
                    labels.len(),
                    1,
                    "FflonkBundle::Add: requires t=1; got t={}",
                    labels.len()
                );
                (vec![p], vec![E::Fr::ONE], labels)
            }
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        let (other_points, other_scalars, other_labels) = match other {
            Self::Bundle(p, labels) => {
                assert_eq!(
                    labels.len(),
                    1,
                    "FflonkBundle::Add: requires t=1; got t={}",
                    labels.len()
                );
                (vec![p], vec![E::Fr::ONE], labels)
            }
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Self::Linear(points, scalars, labels)
    }
}

/// A fflonk commitment: one or more sub-bundles produced by a single
/// `commit` call. Length-1 with a single `t=1` `Bundle` is the
/// linearization-compatible shape.
///
/// The const generic `T_MAX_LOG` matches the scheme's: it lets
/// [`Labelable::label`] reproduce the partition that produced this
/// commitment, so the `t` of each sub-bundle does not need to be encoded
/// on the wire. At `T_MAX_LOG = 0` (no bundling) the wire format is
/// byte-identical to `KZGMultiCommitment`.
#[derive(Clone, Debug)]
pub struct FflonkCommitment<E: MultiMillerLoop, const T_MAX_LOG: u32 = 0>(pub Vec<FflonkBundle<E>>);

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> FflonkCommitment<E, T_MAX_LOG> {
    /// Asserts this commitment is a single sub-bundle (used by `Add`/`Mul`
    /// before delegating to the inner [`FflonkBundle`]).
    fn assert_single_sub_bundle(&self) {
        assert_eq!(
            self.0.len(),
            1,
            "Add/Mul on FflonkCommitment requires exactly one sub-bundle"
        );
    }

    /// Returns a reference to the inner curve point. Panics unless the
    /// commitment carries exactly one sub-bundle of `Bundle` variant.
    pub fn as_point(&self) -> &E::G1 {
        self.assert_single_sub_bundle();
        self.0[0].as_point()
    }

    /// Extracts the inner curve point. Panics unless the commitment carries
    /// exactly one sub-bundle of `Bundle` variant.
    pub fn into_point(self) -> E::G1 {
        self.assert_single_sub_bundle();
        self.0.into_iter().next().unwrap().into_point()
    }
}

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> PartialEq for FflonkCommitment<E, T_MAX_LOG>
where
    E::G1: PartialEq,
    E::Fr: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> Default for FflonkCommitment<E, T_MAX_LOG>
where
    E::G1: Default,
{
    fn default() -> Self {
        Self(vec![FflonkBundle::default()])
    }
}

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> Labelable for FflonkCommitment<E, T_MAX_LOG> {
    /// Total number of polynomials across all sub-bundles.
    ///
    /// Freshly-deserialized commitments have empty placeholder labels, so
    /// this returns `0` until [`Labelable::label`] runs. After labelling,
    /// it equals the number of polynomials originally committed.
    fn length(&self) -> usize {
        self.0.iter().map(FflonkBundle::len).sum()
    }

    /// Attaches `labels` across sub-bundles by re-running
    /// [`partition`](super::partition::partition) with the scheme's
    /// `T_MAX = 1 << T_MAX_LOG` — the same deterministic function the
    /// prover used at `commit` time, so the verifier reconstructs the same
    /// sub-bundle boundaries and slot assignments.
    ///
    /// # Panics
    /// If the partition produced by `labels` does not have the same number
    /// of sub-bundles as `self.0` (mismatch between the labels the
    /// verifier expects and the commitment the prover wrote).
    fn label(self, labels: Vec<PolynomialLabel>) -> Self {
        let t_max = 1usize << T_MAX_LOG;
        let sub_bundles = super::partition::partition(t_max, &labels);
        assert_eq!(
            sub_bundles.len(),
            self.0.len(),
            "FflonkCommitment::label: partition produced {} sub-bundles but \
             the commitment carries {} (T_MAX_LOG = {})",
            sub_bundles.len(),
            self.0.len(),
            T_MAX_LOG,
        );
        let new_bundles = self
            .0
            .into_iter()
            .zip(sub_bundles)
            .map(|(b, indices)| {
                let chunk: Vec<PolynomialLabel> =
                    indices.iter().map(|&i| labels[i].clone()).collect();
                match b {
                    FflonkBundle::Bundle(p, _) => FflonkBundle::Bundle(p, chunk),
                    FflonkBundle::Linear(ps, ss, _) => FflonkBundle::Linear(ps, ss, chunk),
                }
            })
            .collect();
        Self(new_bundles)
    }
}

/// Wire format: `u32 num_sub_bundles` followed by one G1 per sub-bundle.
/// At `T_MAX_LOG = 0` this matches `KZGMultiCommitment` byte-for-byte
/// (every sub-bundle holds one polynomial ⇒ `num_sub_bundles = num_polys`,
/// each sub-bundle writes only its G1).
impl<E: MultiMillerLoop, const T_MAX_LOG: u32> ProcessedSerdeObject
    for FflonkCommitment<E, T_MAX_LOG>
where
    E::G1: Default + ProcessedSerdeObject,
{
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut len_bytes = [0u8; 4];
        reader.read_exact(&mut len_bytes)?;
        let len = u32::from_le_bytes(len_bytes) as usize;
        let inner = (0..len)
            .map(|_| <FflonkBundle<E> as ProcessedSerdeObject>::read(reader, format))
            .collect::<io::Result<Vec<_>>>()?;
        Ok(Self(inner))
    }

    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_all(&(self.0.len() as u32).to_le_bytes())?;
        for b in &self.0 {
            b.write(writer, format)?;
        }
        Ok(())
    }

    fn byte_length(&self, format: SerdeFormat) -> usize {
        4 + self.0.iter().map(|b| b.byte_length(format)).sum::<usize>()
    }
}

impl<H: TranscriptHash, E: MultiMillerLoop, const T_MAX_LOG: u32> Hashable<H>
    for FflonkCommitment<E, T_MAX_LOG>
where
    E::G1: Hashable<H> + Default + ProcessedSerdeObject,
{
    fn to_input(&self) -> H::Input {
        self.0.iter().flat_map(|b| b.to_input()).collect()
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = (self.0.len() as u32).to_le_bytes().to_vec();
        for b in &self.0 {
            bytes.extend_from_slice(&b.to_bytes());
        }
        bytes
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut len_bytes = [0u8; 4];
        buffer.read_exact(&mut len_bytes)?;
        let len = u32::from_le_bytes(len_bytes) as usize;
        let inner = (0..len)
            .map(|_| <FflonkBundle<E> as Hashable<H>>::read(buffer))
            .collect::<io::Result<Vec<_>>>()?;
        Ok(Self(inner))
    }
}

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> Mul<E::Fr> for FflonkCommitment<E, T_MAX_LOG> {
    type Output = Self;

    fn mul(self, scalar: E::Fr) -> Self {
        self.assert_single_sub_bundle();
        Self(vec![self.0.into_iter().next().unwrap() * scalar])
    }
}

impl<E: MultiMillerLoop, const T_MAX_LOG: u32> Add for FflonkCommitment<E, T_MAX_LOG> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.assert_single_sub_bundle();
        other.assert_single_sub_bundle();
        Self(vec![
            self.0.into_iter().next().unwrap() + other.0.into_iter().next().unwrap(),
        ])
    }
}

/// Canonical synthetic label for a `t > 1` sub-bundle. Both prover and
/// verifier compute this for the same bundle (same labels → same synthetic
/// label), so it doubles as the cross-side ordering key (sort by the
/// rendered string — any deterministic order works, lex is fine).
///
/// `bundle_labels` arrives in [`partition`](super::partition::partition)'s
/// canonical order, so `bundle_labels[0]` is the family's canonical-first
/// label. Using it (rather than scanning for a fixed family like `Advice`)
/// generalises across every bundlable family: Advice bundles produce
/// `fflonk_g[advice_<min>]`, PermutationAccumulator bundles produce
/// `fflonk_g[perm_acc_<min>]`, and so on — all derived uniformly from the
/// `Display` impl of [`PolynomialLabel`].
pub(super) fn synthetic_bundle_label(bundle_labels: &[PolynomialLabel]) -> PolynomialLabel {
    let first = bundle_labels
        .first()
        .expect("fflonk: multi-poly bundle must be non-empty");
    PolynomialLabel::Custom(format!("fflonk_g[{}]", first))
}

/// Locate the [`FflonkBundle`] inside a [`FflonkCommitment`] that the
/// given query label refers to. Used by `FflonkScheme::multi_prepare` to
/// recover bundle structure from the verifier's commitment objects.
///
/// Match policy:
/// - [`FflonkBundle::Bundle`] matches if `label` is among its own labels (the
///   standard case for advice / instance / fixed / quotient commitments).
/// - [`FflonkBundle::Linear`] matches **unconditionally** — by construction,
///   `Linear` only ever appears as a linearization commitment, whose query
///   carries the synthetic [`PolynomialLabel::Collapsed`] rather than any of
///   the inner component labels. This mirrors how KZG's `multi_prepare` treats
///   `KZGCommitment::Linear`.
pub(super) fn find_bundle<'a, E: MultiMillerLoop, const T_MAX_LOG: u32>(
    commitment: &'a FflonkCommitment<E, T_MAX_LOG>,
    label: &PolynomialLabel,
) -> &'a FflonkBundle<E> {
    commitment
        .0
        .iter()
        .find(|b| match b {
            FflonkBundle::Bundle(_, labels) => labels.contains(label),
            FflonkBundle::Linear(..) => true,
        })
        .unwrap_or_else(|| {
            let bundle_labels: Vec<Vec<PolynomialLabel>> = commitment
                .0
                .iter()
                .map(|b| match b {
                    FflonkBundle::Bundle(_, ls) => ls.clone(),
                    FflonkBundle::Linear(_, _, ls) => ls.clone(),
                })
                .collect();
            panic!(
                "fflonk multi_prepare: query label {:?} not found in any bundle of its commitment; \
                 bundle labels were {:?}",
                label, bundle_labels,
            )
        })
}
