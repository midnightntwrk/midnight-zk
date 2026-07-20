//! fflonk commitment types.
//!
//! A [`FflonkCommitment`] is the output of one `commit` call: a `Vec` of
//! [`FflonkBundle`]s, one per sub-bundle produced by `partition`. Each
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
//! with `t > 1` panics.

use std::{
    io::{self, Read},
    ops::{Add, Mul},
};

use ff::Field;
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;

use super::FFLONK_T_MAX_LOG;
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
    /// Lazy linear combination `\sum scalars[i] * points[i]` with per-term
    /// labels.
    Linear(Vec<E::G1>, Vec<E::Fr>, Vec<PolynomialLabel>),
}

impl<E: MultiMillerLoop> FflonkBundle<E> {
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

// We implement `PartialEq` manually because its derivation would require
// `E: PartialEq`. In practice, only `E::G1` and `E::Fr` need it; `E` itself
// never appears directly in a comparison.
//
// This comparison is literal. Two equivalent commitments are considered
// different if their representation is different.
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
        Self::Bundle(E::G1::default(), vec![PolynomialLabel::NoLabel])
    }
}

impl<E: MultiMillerLoop> ProcessedSerdeObject for FflonkBundle<E>
where
    E::G1: Default + ProcessedSerdeObject,
{
    /// Wire format: a single G1 point. The bundle's `t` (number of
    /// polynomials packed into this sub-bundle) is not encoded as it is
    /// recovered from `partition`(super::partition::partition). Labels are an
    /// empty placeholder after deserialization and must be attached via
    /// `label`.
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

