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

//! In-circuit multi-point opening argument, shared by every scheme built on a
//! KZG-style SRS.
//!
//! In-circuit analog of `proofs/src/pcs/multi_open.rs`: an `InCircuitPCS`
//! implementation of `multi_prepare` is its own query expansion followed by a
//! call into `multi_prepare_core`. Everything from the first squeezed
//! challenge onwards is scheme-independent and lives here.
//!
//! Refer to the [Halo 2 Book](https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html)
//! for the argument itself.

use std::collections::{BTreeSet, HashMap};

use ff::Field;
use midnight_proofs::{
    circuit::Layouter,
    plonk::Error::{self, Synthesis},
    poly::PolynomialLabel,
};

#[cfg(feature = "truncated-challenges")]
use crate::verifier::utils::truncate;
use crate::{
    CircuitField,
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    verifier::{
        AssignedAccumulator, SelfEmulation,
        msm::{AssignedMsm, AssignedPoint},
        transcript_gadget::TranscriptGadget,
        utils::{
            AssignedBoundedScalar, evaluate_interpolated_polynomial, inner_product, mul_add,
            truncated_powers,
        },
    },
};

/// Labels carried by the argument's own two commitments, the batch commitment
/// `f` and the opening proof `π`. Both are variable bases, so neither label is
/// ever resolved.
const BATCH_LABEL: &str = "kzg_batch";
const PROOF_LABEL: &str = "π";

// --------------------------------
// See proofs/src/pcs/utils.rs
// --------------------------------

#[derive(Clone, Debug)]
struct CommitmentData<S: SelfEmulation> {
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

/// A `(label, point, eval)` opening claim, after any scheme-specific query
/// expansion.
pub(crate) type QueryTriple<S> = (
    PolynomialLabel,
    AssignedNative<<S as SelfEmulation>::F>,
    AssignedNative<<S as SelfEmulation>::F>,
);

type IntermediateSets<S> = (
    Vec<CommitmentData<S>>,
    Vec<Vec<AssignedNative<<S as SelfEmulation>::F>>>,
);

fn construct_intermediate_sets<S: SelfEmulation>(
    queries: &[QueryTriple<S>],
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

/// Sort point sets by ascending cardinality, so the first set is the one
/// holding commitments evaluated at a single point (the fixed ones). Not
/// needed by the proving system itself, but the in-circuit verifier relies on
/// it for a collapse optimization.
///
/// The `(len, i)` key gives a deterministic total order when two sets share a
/// cardinality.
fn point_set_order<F>(point_sets: &[Vec<F>]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..point_sets.len()).collect();
    order.sort_by_key(|&i| (point_sets[i].len(), i));
    order
}

// ------------------------------
// See proofs/src/pcs/multi_open.rs
// ------------------------------

/// Checks the multi-point opening argument, returning the pairing accumulator
/// that satisfies the invariant iff all queries are valid.
///
/// `triples` are the `(label, point, eval)` claims after any scheme-specific
/// expansion, and `label_to_com` resolves each label to the MSM it refers to
/// (one term for a plain commitment, several for a linearization one).
/// `read_point` reads one of the argument's two group elements off the
/// transcript; it is a parameter because each scheme serializes its
/// commitments differently, and both reads have to land at these exact points
/// of the transcript.
#[allow(clippy::too_many_arguments)]
pub(crate) fn multi_prepare_core<S: SelfEmulation, L: Layouter<S::F>>(
    layouter: &mut L,
    #[cfg(feature = "truncated-challenges")] curve_chip: &S::CurveChip,
    scalar_chip: &S::ScalarChip,
    transcript: &mut TranscriptGadget<S>,
    triples: &[QueryTriple<S>],
    label_to_com: &HashMap<PolynomialLabel, AssignedMsm<S>>,
    read_point: impl Fn(
        &mut L,
        &mut TranscriptGadget<S>,
        PolynomialLabel,
    ) -> Result<AssignedPoint<S>, Error>,
) -> Result<AssignedAccumulator<S>, Error> {
    let x1 = transcript.squeeze_challenge(layouter)?;
    let x2 = transcript.squeeze_challenge(layouter)?;

    let default_eval = scalar_chip.assign_fixed(layouter, S::F::default())?;
    let (commitment_map, point_sets) = construct_intermediate_sets::<S>(triples, default_eval)?;

    let mut q_coms: Vec<Vec<AssignedMsm<S>>> = vec![vec![]; point_sets.len()];
    let mut q_eval_sets = vec![vec![]; point_sets.len()];

    for com_data in commitment_map.into_iter() {
        let msm = label_to_com.get(&com_data.label).cloned().ok_or_else(|| {
            Synthesis(format!(
                "multi_prepare: no commitment registered for label {}",
                com_data.label
            ))
        })?;
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

    let (q_coms, q_eval_sets, point_sets) = {
        let order = point_set_order(&point_sets);
        let q_coms: Vec<_> = order.iter().map(|&i| q_coms[i].clone()).collect();
        let q_eval_sets: Vec<_> = order.iter().map(|&i| q_eval_sets[i].clone()).collect();
        let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
        (q_coms, q_eval_sets, point_sets)
    };

    let f_point = read_point(
        layouter,
        transcript,
        PolynomialLabel::Custom(BATCH_LABEL.into()),
    )?;

    let x3 = transcript.squeeze_challenge(layouter)?;
    #[cfg(feature = "truncated-challenges")]
    let x3 = truncate::<S::F>(layouter, scalar_chip, &x3)?;
    #[cfg(not(feature = "truncated-challenges"))]
    let x3 = AssignedBoundedScalar::new(&x3, None);

    let mut q_evals_on_x3 = Vec::with_capacity(q_eval_sets.len());
    for _ in 0..q_eval_sets.len() {
        q_evals_on_x3.push(transcript.read_scalar(layouter)?);
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

    let x4 = transcript.squeeze_challenge(layouter)?;
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
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
        coms.push(AssignedMsm::from_term(
            one,
            f_point,
            PolynomialLabel::Custom(BATCH_LABEL.into()),
        ));

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

    let pi_point = read_point(
        layouter,
        transcript,
        PolynomialLabel::Custom(PROOF_LABEL.into()),
    )?;
    let pi_msm = {
        let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;
        AssignedMsm::from_term(one, pi_point, PolynomialLabel::Custom(PROOF_LABEL.into()))
    };

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
