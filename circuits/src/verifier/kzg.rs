// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Multiopen argument for GWC version of the KZG commitment scheme.
//!
//! This file provides the in-circuit version of the KZG multiopen argument from
//! halo2. In particular, we try to follow the exact same structure used in
//! halo2, concretely in halo2 files:
//!  - src/poly/kzg/utils.rs,
//!  - src/poly/query.rs
//!  - src/utils/arithmetic.rs
//!  - src/poly/kzg/mod.rs

use std::{
    collections::{BTreeSet, HashMap},
    marker::PhantomData,
};

use ff::Field;
use group::Group;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{commitment::Labelable, kzg::commitment::KZGCommitment, PolynomialLabel},
};

#[cfg(feature = "truncated-challenges")]
use crate::verifier::utils::truncate;
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    types::InnerValue,
    verifier::{
        msm::{AssignedMsm, AssignedPoint},
        pcs::{InCircuitHomomorphicCommitment, InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
        utils::{
            evaluate_interpolated_polynomial, inner_product, mul_add, mul_bounded_scalars,
            truncated_powers, AssignedBoundedScalar,
        },
        AssignedAccumulator, SelfEmulation,
    },
    CircuitField,
};

// -------------------------------------
// See proofs/src/poly/kzg/commitment.rs
// -------------------------------------

/// In-circuit analog of
/// [`KZGCommitment`](midnight_proofs::poly::kzg::commitment::KZGCommitment).
///
/// Carries a polynomial commitment (or a lazy linear combination of them)
/// together with its `PolynomialLabel`(s).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignedKZGCommitment<S: SelfEmulation> {
    /// A single committed point with its label.
    Simple(AssignedPoint<S>, PolynomialLabel),
    /// A lazy linear combination `∑ scalars[i] * points[i]` with per-term
    /// labels, accumulated during verification for MSM batching.
    Linear(
        Vec<AssignedPoint<S>>,
        Vec<AssignedBoundedScalar<S::F>>,
        Vec<PolynomialLabel>,
    ),
}

impl<S: SelfEmulation> InnerValue for AssignedKZGCommitment<S> {
    type Element = KZGCommitment<S::Engine>;

    fn value(&self) -> Value<Self::Element> {
        match self.clone() {
            Self::Simple(p, label) => {
                p.value().map(|p| KZGCommitment::Simple(*p.get_point(), label))
            }
            Self::Linear(points, scalars, labels) => {
                let points: Vec<Value<S::C>> =
                    points.iter().map(|p| p.value().map(|p| *p.get_point())).collect();
                let scalars: Vec<Value<S::F>> =
                    scalars.iter().map(|s| s.scalar.value().copied()).collect();
                Value::from_iter(points)
                    .zip(Value::from_iter(scalars))
                    .map(|(ps, ss)| KZGCommitment::Linear(ps, ss, labels))
            }
        }
    }
}

impl<S: SelfEmulation> AssignedKZGCommitment<S> {
    /// Creates a `Simple` commitment from a variable-base assigned point and
    /// label.
    pub fn simple(point: S::AssignedPoint, label: PolynomialLabel) -> Self {
        AssignedKZGCommitment::Simple(AssignedPoint::Variable(point), label)
    }

    /// Creates a `Simple` commitment for a globally-known constant point.
    ///
    /// No circuit cell is allocated for the point; it is identified by its
    /// label and will be looked up from a fixed-bases map when the
    /// accumulator is resolved.
    pub fn fixed(label: PolynomialLabel) -> Self {
        AssignedKZGCommitment::Simple(AssignedPoint::Fixed, label)
    }

    /// Assigns a curve point in the circuit and wraps it in a labeled `Simple`
    /// commitment.
    pub fn assign(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        point: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self, Error> {
        curve_chip.assign(layouter, point).map(|p| Self::simple(p, label))
    }

    /// Converts this commitment into an [`AssignedMsm`] for use in the
    /// multiopen accumulation.
    ///
    /// `Simple(p, l)` becomes a one-term MSM `[(1, p, l)]`.
    /// `Linear(points, scalars, labels)` becomes the corresponding multi-term
    /// MSM.
    pub fn into_msm(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
    ) -> Result<AssignedMsm<S>, Error> {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
        Ok(match self {
            Self::Simple(p, label) => AssignedMsm::new(&[one], &[p], &[label]),
            Self::Linear(points, scalars, labels) => AssignedMsm::new(&scalars, &points, &labels),
        })
    }
}

impl<S: SelfEmulation> AssignedKZGCommitment<S> {
    /// Attaches `label` to a freshly-read (`NoLabel`) commitment.
    ///
    /// # Panics
    ///
    /// If the commitment is not `Simple` or if it was already labeled.
    pub(crate) fn label(self, label: PolynomialLabel) -> Self {
        match self {
            Self::Simple(p, PolynomialLabel::NoLabel) => Self::Simple(p, label),
            Self::Simple(_, existing) => panic!("commitment is already labeled: {existing:?}"),
            Self::Linear(_, _, _) => panic!("KZGCommitment::Linear cannot be labeled"),
        }
    }

    /// Scales this commitment by a scalar.
    ///
    /// `Simple(p, l)` becomes `Linear([p], [scalar], [l])`.
    /// For `Linear`, all existing scalars are multiplied by `scalar`.
    fn mul(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        scalar: &AssignedNative<S::F>,
    ) -> Result<Self, Error> {
        let scalar = AssignedBoundedScalar::new(scalar, None);
        match self {
            Self::Simple(p, label) => Ok(Self::Linear(vec![p], vec![scalar], vec![label])),
            Self::Linear(points, scalars, labels) => Ok(Self::Linear(
                points,
                scalars
                    .iter()
                    .map(|s| mul_bounded_scalars(layouter, scalar_chip, s, &scalar))
                    .collect::<Result<Vec<_>, _>>()?,
                labels,
            )),
        }
    }

    /// Adds two commitments, merging them into a `Linear` combination.
    fn add(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: Self,
    ) -> Result<Self, Error> {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
        let (mut points, mut scalars, mut labels) = match self {
            Self::Simple(p, label) => (vec![p], vec![one.clone()], vec![label]),
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        let (other_points, other_scalars, other_labels) = match other {
            Self::Simple(p, label) => (vec![p], vec![one.clone()], vec![label]),
            Self::Linear(points, scalars, labels) => (points, scalars, labels),
        };
        points.extend(other_points);
        scalars.extend(other_scalars);
        labels.extend(other_labels);
        Ok(Self::Linear(points, scalars, labels))
    }
}

/// In-circuit analog of
/// [`KZGMultiCommitment`](midnight_proofs::poly::kzg::commitment::KZGMultiCommitment):
/// a commitment to one or more polynomials.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignedKZGMultiCommitment<S: SelfEmulation>(pub Vec<AssignedKZGCommitment<S>>);

impl<S: SelfEmulation> AssignedKZGMultiCommitment<S> {
    fn assert_single(&self) {
        assert_eq!(
            self.0.len(),
            1,
            "operation on AssignedKZGMultiCommitment requires exactly one polynomial"
        );
    }

    /// Returns the single inner [`AssignedKZGCommitment`], panicking if this
    /// commitment does not hold exactly one polynomial.
    pub(crate) fn into_single(self) -> AssignedKZGCommitment<S> {
        self.assert_single();
        self.0.into_iter().next().unwrap()
    }

    /// In-circuit commitment to the zero polynomial (the identity point),
    /// tagged with `label`. Used e.g. for empty committed-instance columns.
    pub fn commitment_to_zero(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        label: PolynomialLabel,
    ) -> Result<Self, Error>
    where
        S::CurveChip: AssignmentInstructions<S::F, S::AssignedPoint>,
    {
        let point = curve_chip.assign_fixed(layouter, S::C::identity())?;
        Ok(Self(vec![AssignedKZGCommitment::simple(point, label)]))
    }
}

impl<S: SelfEmulation> InnerValue for AssignedKZGMultiCommitment<S> {
    type Element = midnight_proofs::poly::kzg::commitment::KZGMultiCommitment<S::Engine>;

    fn value(&self) -> Value<Self::Element> {
        Value::from_iter(self.0.iter().map(|c| c.value()))
            .map(midnight_proofs::poly::kzg::commitment::KZGMultiCommitment)
    }
}

impl<S: SelfEmulation> Labelable for AssignedKZGMultiCommitment<S> {
    /// Attaches one label per inner polynomial.
    ///
    /// # Panics
    ///
    /// If `labels.len() != self.length()`.
    fn label(self, labels: &[PolynomialLabel]) -> Self {
        assert_eq!(
            labels.len(),
            self.0.len(),
            "label count must match polynomial count"
        );
        Self(self.0.into_iter().zip(labels).map(|(c, l)| c.label(l.clone())).collect())
    }

    fn length(&self) -> usize {
        self.0.len()
    }
}

impl<S: SelfEmulation> InCircuitHomomorphicCommitment<S> for AssignedKZGMultiCommitment<S> {
    fn mul(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        scalar: &AssignedNative<S::F>,
    ) -> Result<Self, Error> {
        self.assert_single();
        let inner = self.0.into_iter().next().unwrap().mul(layouter, scalar_chip, scalar)?;
        Ok(Self(vec![inner]))
    }

    fn add(
        self,
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        other: Self,
    ) -> Result<Self, Error> {
        self.assert_single();
        other.assert_single();
        let inner = self.0.into_iter().next().unwrap().add(
            layouter,
            scalar_chip,
            other.0.into_iter().next().unwrap(),
        )?;
        Ok(Self(vec![inner]))
    }
}

// --------------------------------
// See proofs/src/poly/kzg/utils.rs
// --------------------------------

#[derive(Clone, Debug)]
pub(crate) struct CommitmentData<S: SelfEmulation> {
    label: PolynomialLabel,
    set_index: usize,
    point_indices: Vec<usize>,
    evals: Vec<AssignedNative<S::F>>,
}

impl<S: SelfEmulation> CommitmentData<S> {
    fn new(label: PolynomialLabel) -> Self {
        CommitmentData {
            label,
            set_index: 0,
            point_indices: vec![],
            evals: vec![],
        }
    }
}

type IntermediateSets<S> = (
    Vec<CommitmentData<S>>,
    Vec<Vec<AssignedNative<<S as SelfEmulation>::F>>>,
);

#[allow(clippy::type_complexity)]
fn construct_intermediate_sets<S: SelfEmulation>(
    queries: &[(PolynomialLabel, AssignedNative<S::F>, AssignedNative<S::F>)],
    default_eval: AssignedNative<S::F>,
) -> Result<IntermediateSets<S>, Error> {
    // Construct sets of unique commitments and corresponding information about
    // their queries.
    let mut commitment_map: Vec<CommitmentData<S>> = vec![];

    // Also construct mapping from a unique point to a point_index. This defines
    // an ordering on the points.
    // Note that we use a HashMap, whereas halo2 uses a BTreeMap. This is because
    // `AssignedScalar` does not implement `Ord`, but implements `Hash`.
    // This difference is not a problem, since the order of keys does not matter
    // for this algorithm.
    let mut point_index_map = HashMap::new();

    // Iterate over all of the queries, computing the ordering of the points
    // while also creating new commitment data.
    for (query_label, query_point, _query_eval) in queries.iter() {
        let num_points = point_index_map.len();
        let point_idx = point_index_map.entry(query_point).or_insert(num_points);

        if let Some(pos) = commitment_map.iter().position(|comm| &comm.label == query_label) {
            if commitment_map[pos].point_indices.contains(point_idx) {
                return Err(Error::Synthesis("repeated query".into()));
            }
            commitment_map[pos].point_indices.push(*point_idx);
        } else {
            let mut tmp = CommitmentData::new(query_label.clone());
            tmp.point_indices.push(*point_idx);
            commitment_map.push(tmp);
        }
    }

    // Also construct inverse mapping from point_index to the point
    let mut inverse_point_index_map = HashMap::new();
    for (&point, &point_index) in point_index_map.iter() {
        inverse_point_index_map.insert(point_index, point.clone());
    }

    // Construct map of unique ordered point_idx_sets to their set_idx.
    let mut point_idx_sets = HashMap::new();
    // Also construct mapping from commitment to point_idx_set
    let mut commitment_set_map = Vec::new();

    for commitment_data in commitment_map.iter() {
        let mut point_index_set = BTreeSet::new();
        // Note that point_index_set is ordered, unlike point_indices
        for &point_index in commitment_data.point_indices.iter() {
            point_index_set.insert(point_index);
        }

        // Push point_index_set to CommitmentData for the relevant commitment
        commitment_set_map.push((commitment_data.label.clone(), point_index_set.clone()));

        let num_sets = point_idx_sets.len();
        point_idx_sets.entry(point_index_set).or_insert(num_sets);
    }

    // Initialise empty evals vec for each unique commitment
    for commitment_data in commitment_map.iter_mut() {
        let len = commitment_data.point_indices.len();
        commitment_data.evals = vec![default_eval.clone(); len];
    }

    // Populate set_index, evals and points for each commitment using point_idx_sets
    for (query_label, query_point, query_eval) in queries.iter() {
        // The index of the point at which the commitment is queried
        let point_index = point_index_map.get(&query_point).unwrap();

        // The point_index_set at which the commitment was queried
        let mut point_index_set = BTreeSet::new();
        for (l, point_idx_set) in commitment_set_map.iter() {
            if l == query_label {
                point_index_set.clone_from(point_idx_set);
            }
        }
        assert!(!point_index_set.is_empty());

        // The set_index of the point_index_set
        let set_index = point_idx_sets.get(&point_index_set).unwrap();
        for commitment_data in commitment_map.iter_mut() {
            if query_label == &commitment_data.label {
                commitment_data.set_index = *set_index;
            }
        }
        let point_index_set: Vec<usize> = point_index_set.iter().cloned().collect();

        // The offset of the point_index in the point_index_set
        let point_index_in_set = point_index_set.iter().position(|i| i == point_index).unwrap();

        for commitment_data in commitment_map.iter_mut() {
            if *query_label == commitment_data.label {
                // Insert the eval using the ordering of the point_index_set
                commitment_data.evals[point_index_in_set] = query_eval.clone();
            }
        }
    }

    // Get actual points in each point set
    let mut point_sets: Vec<Vec<AssignedNative<S::F>>> = vec![Vec::new(); point_idx_sets.len()];
    for (point_idx_set, &set_idx) in point_idx_sets.iter() {
        for &point_idx in point_idx_set.iter() {
            let point = inverse_point_index_map.get(&point_idx).unwrap();
            point_sets[set_idx].push((*point).clone());
        }
    }

    Ok((commitment_map, point_sets))
}

// ----------------------------------
// See proofs/src/utils/arithmetic.rs
// ----------------------------------

fn msm_inner_product<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    scalar_chip: &S::ScalarChip,
    msms: &[AssignedMsm<S>],
    scalars: &[AssignedBoundedScalar<S::F>],
) -> Result<AssignedMsm<S>, Error> {
    let mut res = AssignedMsm::empty();
    let mut msms = msms.to_vec();
    for (msm, s) in msms.iter_mut().zip(scalars) {
        msm.scale(layouter, scalar_chip, s)?;
        res.add_msm(msm)?;
    }
    Ok(res)
}

/// Computes the inner product of a set of polynomial evaluations and a set of
/// scalar values. This function computes the weighted sum of polynomial
/// evaluations. Each vector in `evals_set` is multiplied element-wise by a
/// corresponding scalar from `scalars`, and the results are accumulated
/// into a single vector.
fn evals_inner_product<F: CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    evals_set: &[Vec<AssignedNative<F>>],
    scalars: &[AssignedBoundedScalar<F>],
) -> Result<Vec<AssignedNative<F>>, Error> {
    let zero = scalar_chip.assign_fixed(layouter, F::ZERO)?;
    let mut res = vec![zero.clone(); evals_set[0].len()];
    for (poly_evals, s) in evals_set.iter().zip(scalars) {
        for i in 0..res.len() {
            // res[i] := s.scalar * poly_evals[i] + res[i]
            res[i] = mul_add(layouter, scalar_chip, &s.scalar, &poly_evals[i], &res[i])?;
        }
    }
    Ok(res)
}

// ------------------------------
// See proofs/src/poly/kzg/mod.rs
// ------------------------------

/// Verifies a bunch of KZG queries in a multi-open argument.
/// The resulting accumulator satisfies the invariant iff all queries are valid.
pub(crate) fn multi_prepare_kzg<S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    #[cfg(feature = "truncated-challenges")] curve_chip: &S::CurveChip,
    scalar_chip: &S::ScalarChip,
    transcript_gadget: &mut TranscriptGadget<S>,
    queries: &[VerifierQuery<S, InCircuitKZG<S>>],
) -> Result<AssignedAccumulator<S>, Error> {
    let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;

    // Add dummy queries to reduce the number of distinct multi-open point sets.
    #[cfg(feature = "fewer-point-sets")]
    let queries = &{
        let pairs: Vec<_> = queries.iter().map(|q| (q.label.clone(), q.point.clone())).collect();
        let dummy_openings = midnight_proofs::poly::kzg::compute_dummy_queries(&pairs);
        let mut queries = queries.to_vec();
        for (idx, dummy_point) in dummy_openings {
            queries.push(VerifierQuery {
                point: dummy_point,
                commitment: queries[idx].commitment,
                label: queries[idx].label.clone(),
                eval: transcript_gadget.read_scalar(layouter)?,
            });
        }
        queries
    };

    let x1 = transcript_gadget.squeeze_challenge(layouter)?;
    let x2 = transcript_gadget.squeeze_challenge(layouter)?;

    // Peel each query's multi-commitment down to the single inner commitment it
    // targets, keyed by the query label. A length-1 commitment (the common case,
    // including the `Linear` linearization commitment) peels to its sole inner;
    // a batched commitment holds several `Simple`s, so we pick the one whose own
    // label matches the query.
    let label_to_commitment: HashMap<PolynomialLabel, &AssignedKZGCommitment<S>> = queries
        .iter()
        .map(|q| {
            let inners = &q.commitment.0;
            let inner = if inners.len() == 1 {
                &inners[0]
            } else {
                inners
                    .iter()
                    .find(|c| matches!(c, AssignedKZGCommitment::Simple(_, label) if *label == q.label))
                    .expect("batched commitment has no polynomial matching the query label")
            };
            (q.label.clone(), inner)
        })
        .collect();

    let default_eval = scalar_chip.assign_fixed(layouter, S::F::default())?;
    let kzg_queries = queries
        .iter()
        .map(|query| (query.label.clone(), query.point.clone(), query.eval.clone()))
        .collect::<Vec<_>>();
    let (commitment_map, point_sets) =
        construct_intermediate_sets::<S>(&kzg_queries, default_eval)?;

    let mut q_coms: Vec<_> = vec![vec![]; point_sets.len()];
    let mut q_eval_sets = vec![vec![]; point_sets.len()];

    for com_data in commitment_map.into_iter() {
        let mut msm = AssignedMsm::empty();
        match label_to_commitment[&com_data.label] {
            AssignedKZGCommitment::Simple(p, label) => msm.add_term(&one, p, label),
            AssignedKZGCommitment::Linear(points, scalars, labels) => {
                msm.add_msm(&AssignedMsm::new(scalars, points, labels))?;
            }
        }
        q_coms[com_data.set_index].push(msm);
        q_eval_sets[com_data.set_index].push(com_data.evals);
    }

    let truncated_x1_powers = {
        let nb_x1_powers = q_coms.iter().map(|v| v.len()).max().unwrap_or(0);
        assert!(nb_x1_powers >= q_eval_sets.iter().map(|v| v.len()).max().unwrap_or(0));
        truncated_powers(layouter, scalar_chip, &x1, nb_x1_powers)?
    };

    let q_coms = q_coms
        .iter()
        .map(|msms| msm_inner_product(layouter, scalar_chip, msms, &truncated_x1_powers))
        .collect::<Result<Vec<_>, Error>>()?;

    let q_eval_sets = q_eval_sets
        .iter()
        .map(|evals| evals_inner_product(layouter, scalar_chip, evals, &truncated_x1_powers))
        .collect::<Result<Vec<_>, Error>>()?;

    // Sort point sets by ascending cardinality to ensure the first set is the one
    // that contains fixed commitments (which are evaluated at x only). This
    // property is not necessary for the actual proving system, but it is important
    // for in-circuit verification of proofs. (It enables an optimization based on
    // an internal collapse.)
    //
    // The (len, i) key provides a deterministic total order even when two sets
    // share the same cardinality.
    let (q_coms, q_eval_sets, point_sets) = {
        let mut order: Vec<usize> = (0..point_sets.len()).collect();
        order.sort_by_key(|&i| (point_sets[i].len(), i));
        let q_coms: Vec<_> = order.iter().map(|&i| q_coms[i].clone()).collect();
        let q_eval_sets: Vec<_> = order.iter().map(|&i| q_eval_sets[i].clone()).collect();
        let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
        (q_coms, q_eval_sets, point_sets)
    };

    let f_com = transcript_gadget
        .read_commitment(layouter, 1)?
        .label(&[PolynomialLabel::Custom("kzg_batch".into())])
        .into_single();

    let x3 = transcript_gadget.squeeze_challenge(layouter)?;
    #[cfg(feature = "truncated-challenges")]
    let x3 = truncate::<S::F>(layouter, scalar_chip, &x3)?;
    #[cfg(not(feature = "truncated-challenges"))]
    let x3 = AssignedBoundedScalar::new(&x3, None);

    let mut q_evals_on_x3 = Vec::with_capacity(q_eval_sets.len());
    for _ in 0..q_eval_sets.len() {
        q_evals_on_x3.push(transcript_gadget.read_scalar(layouter)?);
    }

    let zero = scalar_chip.assign_fixed(layouter, S::F::ZERO)?;
    let f_eval = point_sets
        .iter()
        .zip(q_eval_sets.iter())
        .zip(q_evals_on_x3.iter())
        .rev()
        .try_fold(zero, |acc_eval, ((points, evals), proof_eval)| {
            let r_eval =
                evaluate_interpolated_polynomial(layouter, scalar_chip, points, evals, &x3.scalar)?;

            // eval = (proof_eval - r_eval) / prod_i (x3 - point_i)
            let den = points.iter().skip(1).try_fold(
                scalar_chip.sub(layouter, &x3.scalar, &points[0])?,
                |acc, point| {
                    // acc * (x3 - point) computed as acc * x3 - acc * point
                    scalar_chip.add_and_double_mul(
                        layouter,
                        (S::F::ZERO, &acc),
                        (S::F::ZERO, &x3.scalar),
                        (S::F::ZERO, point),
                        S::F::ZERO,
                        (S::F::ONE, -S::F::ONE),
                    )
                },
            )?;
            let mut eval = scalar_chip.sub(layouter, proof_eval, &r_eval)?;
            eval = scalar_chip.div(layouter, &eval, &den)?;

            // acc_eval * x2 + eval
            mul_add(layouter, scalar_chip, &acc_eval, &x2, &eval)
        })?;

    let x4 = transcript_gadget.squeeze_challenge(layouter)?;
    let truncated_x4_powers =
        truncated_powers::<S::F>(layouter, scalar_chip, &x4, q_coms.len() + 1)?;

    let final_com = {
        let mut coms = q_coms;

        // We collapse all AssignedMsm at this point to later leverage the fact that x4
        // powers are truncated. Exceptionally, the first one is not collapsed,
        // as the first x4 power is 1.
        #[cfg(feature = "truncated-challenges")]
        coms.iter_mut().skip(1).try_for_each(|com| {
            com.collapse(layouter, curve_chip, scalar_chip, PolynomialLabel::NoLabel)
        })?;
        coms.push(f_com.into_msm(layouter, scalar_chip)?);

        msm_inner_product(layouter, scalar_chip, &coms, &truncated_x4_powers)?
    };

    let v = {
        let mut evals = q_evals_on_x3;
        evals.push(f_eval);

        let scalar_x4_powers: Vec<_> =
            truncated_x4_powers.iter().map(|s| s.scalar.clone()).collect();

        AssignedBoundedScalar::new(
            &inner_product(layouter, scalar_chip, &evals, &scalar_x4_powers)?,
            None,
        )
    };

    let pi = transcript_gadget
        .read_commitment(layouter, 1)
        .map(|c| c.label(&[PolynomialLabel::Custom("π".into())]))?
        .into_single();
    let pi_msm = pi.into_msm(layouter, scalar_chip)?;

    // Scale zπ
    let mut scaled_pi = pi_msm.clone();
    scaled_pi.scale(layouter, scalar_chip, &x3)?;

    // (π, C − vG + zπ)
    let left = pi_msm; // π

    let right = {
        let mut right = final_com; // C
        let minus_v_gen = AssignedMsm::from_fixed_term(v, PolynomialLabel::Custom("-G".into()));
        right.add_msm(&minus_v_gen)?; // -vG
        right.add_msm(&scaled_pi)?; // zπ
        right
    };

    Ok(AssignedAccumulator::new(left, right))
}

/// KZG instantiation of [`InCircuitPCS`].
#[derive(Clone, Copy, Debug)]
pub struct InCircuitKZG<S: SelfEmulation>(PhantomData<S>);

impl<S: SelfEmulation> InCircuitPCS<S> for InCircuitKZG<S> {
    type AssignedCommitment = AssignedKZGMultiCommitment<S>;

    fn fixed_commitment(label: PolynomialLabel) -> Self::AssignedCommitment {
        AssignedKZGMultiCommitment(vec![AssignedKZGCommitment::fixed(label)])
    }

    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        length: usize,
    ) -> Result<Self::AssignedCommitment, Error> {
        transcript.read_commitment(layouter, length)
    }

    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error> {
        Ok(AssignedKZGMultiCommitment(vec![
            AssignedKZGCommitment::assign(layouter, curve_chip, value, label)?,
        ]))
    }

    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &AssignedKZGMultiCommitment<S>,
    ) -> Result<(), Error> {
        transcript.common_commitment(layouter, commitment)
    }

    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        _curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
        queries: &[VerifierQuery<'_, S, Self>],
    ) -> Result<AssignedAccumulator<S>, Error> {
        multi_prepare_kzg(
            layouter,
            #[cfg(feature = "truncated-challenges")]
            _curve_chip,
            scalar_chip,
            transcript,
            queries,
        )
    }
}
