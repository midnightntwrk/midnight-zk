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

use std::ops::{Add, Mul};

use ff::Field;
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;

use crate::poly::query::PolynomialLabel;

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
