// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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
    fmt::Debug,
};

use ff::{Field, PrimeField};
use midnight_proofs::{circuit::Layouter, plonk::Error};

#[cfg(feature = "truncated-challenges")]
use crate::verifier::utils::truncate;
use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssignmentInstructions},
    verifier::{
        msm::AssignedMsm,
        transcript_gadget::TranscriptGadget,
        utils::{
            evaluate_interpolated_polynomial, inner_product, mul_add, truncated_powers,
            AssignedBoundedScalar,
        },
        AssignedAccumulator, SelfEmulation,
    },
};

// -------------------------------
// See halo2 src/poly/kzg/utils.rs
// -------------------------------

#[derive(Clone, Debug)]
pub(crate) struct CommitmentData<S: SelfEmulation> {
    commitment: AssignedMsm<S>,
    set_index: usize,
    point_indices: Vec<usize>,
    evals: Vec<AssignedNative<S::F>>,
}

impl<S: SelfEmulation> CommitmentData<S> {
    fn new(commitment: AssignedMsm<S>) -> Self {
        CommitmentData {
            commitment,
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

fn construct_intermediate_sets<S: SelfEmulation, I>(
    queries: I,
    default_eval: AssignedNative<S::F>,
) -> Result<IntermediateSets<S>, Error>
where
    I: IntoIterator<Item = VerifierQuery<S>> + Clone,
{
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
    for query in queries.clone() {
        let num_points = point_index_map.len();
        let point_idx = point_index_map.entry(query.get_point()).or_insert(num_points);

        if let Some(pos) =
            commitment_map.iter().position(|comm| comm.commitment == query.get_commitment())
        {
            if commitment_map[pos].point_indices.contains(point_idx) {
                return Err(Error::Synthesis("repeated query".into()));
            }
            commitment_map[pos].point_indices.push(*point_idx);
        } else {
            let mut tmp = CommitmentData::new(query.get_commitment());
            tmp.point_indices.push(*point_idx);
            commitment_map.push(tmp);
        }
    }

    // Also construct inverse mapping from point_index to the point
    let mut inverse_point_index_map = HashMap::new();
    for (point, &point_index) in point_index_map.iter() {
        inverse_point_index_map.insert(point_index, point.clone());
    }

    // Construct map of unique ordered point_idx_sets to their set_idx
    // Again, mind the difference of `HashMap` vs halo2's `BTreeMap`.
    // This difference is not significant, it leads to equivalent code,
    // as the key order is not relevant here.
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
        commitment_set_map.push((commitment_data.commitment.clone(), point_index_set.clone()));

        let num_sets = point_idx_sets.len();
        point_idx_sets.entry(point_index_set).or_insert(num_sets);
    }

    // Initialise empty evals vec for each unique commitment
    for commitment_data in commitment_map.iter_mut() {
        let len = commitment_data.point_indices.len();
        commitment_data.evals = vec![default_eval.clone(); len];
    }

    // Populate set_index, evals and points for each commitment using point_idx_sets
    for query in queries {
        // The index of the point at which the commitment is queried
        let point_index = point_index_map.get(&query.get_point()).unwrap();

        // The point_index_set at which the commitment was queried
        let mut point_index_set = BTreeSet::new();
        for (commitment, point_idx_set) in commitment_set_map.iter() {
            if query.get_commitment() == *commitment {
                point_index_set.clone_from(point_idx_set);
            }
        }
        assert!(!point_index_set.is_empty());

        // The set_index of the point_index_set
        let set_index = point_idx_sets.get(&point_index_set).unwrap();
        for commitment_data in commitment_map.iter_mut() {
            if query.get_commitment() == commitment_data.commitment {
                commitment_data.set_index = *set_index;
            }
        }
        let point_index_set: Vec<usize> = point_index_set.iter().cloned().collect();

        // The offset of the point_index in the point_index_set
        let point_index_in_set = point_index_set.iter().position(|i| i == point_index).unwrap();

        for commitment_data in commitment_map.iter_mut() {
            if query.get_commitment() == commitment_data.commitment {
                // Insert the eval using the ordering of the point_index_set
                commitment_data.evals[point_index_in_set] = query.get_eval();
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

// ---------------------------
// See halo2 src/poly/query.rs
// ---------------------------

#[derive(Clone, Debug)]
/// Structure to store a VerifierQuery
pub(crate) struct VerifierQuery<S: SelfEmulation> {
    /// Point at which polynomial is queried
    point: AssignedNative<S::F>,
    /// Commitment to the polynomial
    commitment: AssignedMsm<S>,
    /// Evaluation of polynomial at query point
    eval: AssignedNative<S::F>,
}

impl<S: SelfEmulation> VerifierQuery<S> {
    /// Create a verifier query on a commitment.
    /// This function requires an assigned bounded scalar of one as input.
    pub(crate) fn new(
        one: &AssignedBoundedScalar<S::F>,
        point: &AssignedNative<S::F>,
        commitment: &S::AssignedPoint,
        eval: &AssignedNative<S::F>,
    ) -> Self {
        Self {
            point: point.clone(),
            commitment: AssignedMsm::from_term(one, commitment),
            eval: eval.clone(),
        }
    }

    /// Create a verifier query on a commitment (respresented as an MSM).
    pub(crate) fn new_from_msm(
        point: &AssignedNative<S::F>,
        commitment: &AssignedMsm<S>,
        eval: &AssignedNative<S::F>,
    ) -> Self {
        Self {
            point: point.clone(),
            commitment: commitment.clone(),
            eval: eval.clone(),
        }
    }

    /// Create a verifier query on a fixed commitment (given its name).
    /// This function requires an assigned bounded scalar of one as input.
    pub(crate) fn new_fixed(
        one: &AssignedBoundedScalar<S::F>,
        point: &AssignedNative<S::F>,
        commitment_name: &str,
        eval: &AssignedNative<S::F>,
    ) -> Self {
        Self {
            point: point.clone(),
            commitment: AssignedMsm::from_fixed_term(one, commitment_name),
            eval: eval.clone(),
        }
    }

    fn get_point(&self) -> AssignedNative<S::F> {
        self.point.clone()
    }

    fn get_eval(&self) -> AssignedNative<S::F> {
        self.eval.clone()
    }

    fn get_commitment(&self) -> AssignedMsm<S> {
        self.commitment.clone()
    }
}

// ---------------------------------
// See halo2 src/utils/arithmetic.rs
// ---------------------------------

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
        res.add_msm(layouter, scalar_chip, msm)?;
    }
    Ok(res)
}

/// Computes the inner product of a set of polynomial evaluations and a set of
/// scalar values. This function computes the weighted sum of polynomial
/// evaluations. Each vector in `evals_set` is multiplied element-wise by a
/// corresponding scalar from `scalars`, and the results are accumulated
/// into a single vector.
fn evals_inner_product<F: PrimeField>(
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

// -----------------------------
// See halo2 src/poly/kzg/mod.rs
// -----------------------------

/// Verifies a bunch of KZG queries in a multi-open argument.
/// The resulting accumulator satisfies the invariant iff all queries are valid.
pub(crate) fn multi_prepare<I, S: SelfEmulation>(
    layouter: &mut impl Layouter<S::F>,
    #[cfg(feature = "truncated-challenges")] curve_chip: &S::CurveChip,
    scalar_chip: &S::ScalarChip,
    transcript_gadget: &mut TranscriptGadget<S>,
    queries: I,
) -> Result<AssignedAccumulator<S>, Error>
where
    I: IntoIterator<Item = VerifierQuery<S>> + Clone,
{
    let x1 = transcript_gadget.squeeze_challenge(layouter)?;
    let x2 = transcript_gadget.squeeze_challenge(layouter)?;

    let default_eval = scalar_chip.assign_fixed(layouter, S::F::default())?;
    let (commitment_map, point_sets) = construct_intermediate_sets(queries, default_eval)?;

    let mut q_coms: Vec<_> = vec![vec![]; point_sets.len()];
    let mut q_eval_sets = vec![vec![]; point_sets.len()];

    for com_data in commitment_map.into_iter() {
        q_coms[com_data.set_index].push(com_data.commitment);
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

    let f_com = transcript_gadget.read_point(layouter)?;

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
            let mut den = scalar_chip.sub(layouter, &x3.scalar, &points[0])?;
            for point in points.iter().skip(1) {
                // TODO: This can be optimized with add_and_double_mul
                let x3_minus_point = scalar_chip.sub(layouter, &x3.scalar, point)?;
                den = scalar_chip.mul(layouter, &den, &x3_minus_point, None)?;
            }
            let mut eval = scalar_chip.sub(layouter, proof_eval, &r_eval)?;
            eval = scalar_chip.div(layouter, &eval, &den)?;

            // acc_eval * x2 + eval
            mul_add(layouter, scalar_chip, &acc_eval, &x2, &eval)
        })?;

    let x4 = transcript_gadget.squeeze_challenge(layouter)?;
    let truncated_x4_powers =
        truncated_powers::<S::F>(layouter, scalar_chip, &x4, q_coms.len() + 1)?;

    let one = AssignedBoundedScalar::one(layouter, scalar_chip)?;

    let final_com = {
        let mut coms = q_coms;
        let f_com_as_msm = AssignedMsm::from_term(&one, &f_com);

        // We collapse all AssignedMsm at this point to later leverage the fact that x4
        // powers are truncated. Exceptionally, the first one is not collapsed,
        // as the first x4 power is 1.
        #[cfg(feature = "truncated-challenges")]
        coms.iter_mut()
            .skip(1)
            .try_for_each(|com| com.collapse(layouter, curve_chip, scalar_chip))?;
        coms.push(f_com_as_msm);

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

    let pi = transcript_gadget.read_point(layouter)?;
    let pi_msm = AssignedMsm::from_term(&one, &pi);

    // Scale zπ
    let mut scaled_pi = pi_msm.clone();
    scaled_pi.scale(layouter, scalar_chip, &x3)?;

    // (π, C − vG + zπ)
    let left = pi_msm; // π

    let right = {
        let mut right = final_com; // C
        let minus_v_gen = AssignedMsm::from_fixed_term(&v, "~G");
        right.add_msm(layouter, scalar_chip, &minus_v_gen)?; // -vG
        right.add_msm(layouter, scalar_chip, &scaled_pi)?; // zπ
        right
    };

    Ok(AssignedAccumulator::new(left, right))
}
