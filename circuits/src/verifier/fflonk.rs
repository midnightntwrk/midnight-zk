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

//! In-circuit fflonk over a generic in-circuit PCS.
//!
//! In-circuit analog of [`midnight_proofs::poly::fflonk`]: the polynomials of
//! a group are committed in chunks of at most `T_MAX`, each chunk under the
//! label `Collection(chunk)`, and opening a chunk at `x` amounts to opening it
//! with the inner PCS at the `t`-th roots of `x`.

use std::{
    collections::{BTreeMap, HashMap, hash_map::Entry},
    marker::PhantomData,
};

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{
        PolynomialLabel::{self, Collection},
        fflonk::{Fflonk, roots},
    },
};

use crate::{
    field::AssignedNative,
    instructions::{ArithInstructions, AssertionInstructions, AssignmentInstructions},
    verifier::{
        AssignedAccumulator, SelfEmulation,
        pcs::{InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
        utils::mul_add,
    },
};

/// fflonk over the in-circuit PCS `P`, combining at most `T_MAX = 2^LOG2_T_MAX`
/// polynomials per chunk. Verifies the proofs of
/// [`Fflonk<P::OffCircuit, LOG2_T_MAX>`](Fflonk).
#[derive(Clone, Copy, Debug)]
pub struct InCircuitFflonk<P, const LOG2_T_MAX: u32>(PhantomData<P>);

impl<P, const LOG2_T_MAX: u32> InCircuitFflonk<P, LOG2_T_MAX> {
    /// The maximum number of polynomials combined into one.
    const T_MAX: usize = 1 << LOG2_T_MAX;

    /// The labels of the inner commitments to the group `labels`.
    fn chunk_labels(labels: &[PolynomialLabel]) -> Vec<PolynomialLabel> {
        PolynomialLabel::assert_distinct(labels);
        labels.chunks(Self::T_MAX).map(|l| Collection(l.to_vec())).collect()
    }
}

impl<S, P, const LOG2_T_MAX: u32> InCircuitPCS<S> for InCircuitFflonk<P, LOG2_T_MAX>
where
    S: SelfEmulation,
    P: InCircuitPCS<S>,
{
    type OffCircuit = Fflonk<P::OffCircuit, LOG2_T_MAX>;
    type AssignedCommitment = P::AssignedCommitment;

    fn fixed_commitment(labels: &[PolynomialLabel]) -> Self::AssignedCommitment {
        P::fixed_commitment(&Self::chunk_labels(labels))
    }

    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<S::C>,
        label: PolynomialLabel,
    ) -> Result<Self::AssignedCommitment, Error> {
        P::assign_commitment(layouter, curve_chip, value, Collection(vec![label]))
    }

    fn commitment_to_zero(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        P::commitment_to_zero(layouter, curve_chip, &Self::chunk_labels(labels))
    }

    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        P::read_commitment(transcript, layouter, &Self::chunk_labels(labels))
    }

    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &Self::AssignedCommitment,
    ) -> Result<(), Error> {
        P::common_commitment(transcript, layouter, commitment)
    }

    fn commitment_labels(commitment: &Self::AssignedCommitment) -> Vec<PolynomialLabel> {
        P::commitment_labels(commitment)
            .into_iter()
            .flat_map(|label| match label {
                Collection(labels) => labels,
                label => panic!("fflonk commitment tagged with {label}, not a collection"),
            })
            .collect()
    }

    fn squeeze_evaluation_point(
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let x = P::squeeze_evaluation_point(layouter, scalar_chip, transcript)?;
        scalar_chip.pow(layouter, &x, Self::T_MAX as u64)
    }

    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
        queries: &[VerifierQuery<'_, S, Self>],
    ) -> Result<AssignedAccumulator<S>, Error> {
        // Maps the labels of every queried chunk to its commitment and the points
        // its polynomials are queried at, in query order. Points are cells: the
        // verifier gadget hands out one cell per rotation of `x`.
        let mut chunks_info = BTreeMap::<Vec<PolynomialLabel>, (_, Vec<_>)>::new();
        for q in queries {
            let labels = (Self::commitment_labels(q.commitment).chunks(Self::T_MAX))
                .find(|labels| labels.contains(&q.label))
                .map_or_else(|| vec![q.label.clone()], <[_]>::to_vec);
            let (_, points) = chunks_info.entry(labels).or_insert((q.commitment, Vec::new()));
            if !points.contains(&q.point) {
                points.push(q.point.clone());
            }
        }

        // The evaluations of the chunks at all the points: the explicit ones from
        // the queries, the implicit ones read from the transcript here.
        let mut evals: HashMap<_, _> = queries
            .iter()
            .map(|q| ((q.label.clone(), q.point.clone()), q.eval.clone()))
            .collect();
        for (labels, (_, points)) in &chunks_info {
            for point in points {
                for label in labels {
                    if let Entry::Vacant(entry) = evals.entry((label.clone(), point.clone())) {
                        entry.insert(transcript.read_scalar(layouter)?);
                    }
                }
            }
        }

        // Each chunk is opened at the `t`-th roots `r` of each of its points `x`,
        // with value `g(r) = Σ_i r^i f_i(x)`.
        let mut inner_queries = Vec::new();
        let mut roots_cache = RootsCache::default();
        for (labels, (commitment, points)) in &chunks_info {
            let t = labels.len().next_power_of_two();
            for x in points {
                let f_evals: Vec<_> =
                    labels.iter().map(|l| &evals[&(l.clone(), x.clone())]).collect();
                for root in roots_cache.get(layouter, scalar_chip, x, t)? {
                    let eval = horner(layouter, scalar_chip, &f_evals, &root)?;
                    let label = Collection(labels.clone());
                    inner_queries.push(VerifierQuery::new(&root, *commitment, label, &eval));
                }
            }
        }

        P::multi_prepare(
            layouter,
            curve_chip,
            scalar_chip,
            transcript,
            &inner_queries,
        )
    }
}

/// The `t`-th roots of the points computed so far, keyed by the cell of the
/// point and `t`.
///
/// Two chunks opened at the same point must share the very same root cells:
/// the inner multi-open groups the queries by point cell, so distinct cells for
/// equal roots would split a point set that the off-circuit verifier keeps
/// whole.
struct RootsCache<F: PrimeField>(HashMap<(AssignedNative<F>, usize), Vec<AssignedNative<F>>>);

impl<F: PrimeField> Default for RootsCache<F> {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

impl<F: PrimeField> RootsCache<F> {
    /// The roots `[z, z ω_t, ..., z ω_t^{t-1}]` of `x`, for a witness `z`
    /// constrained by `z^t = x`, in the order of
    /// [`roots`](midnight_proofs::poly::fflonk::roots).
    fn get<S>(
        &mut self,
        layouter: &mut impl Layouter<F>,
        scalar_chip: &S,
        x: &AssignedNative<F>,
        t: usize,
    ) -> Result<Vec<AssignedNative<F>>, Error>
    where
        S: ArithInstructions<F, AssignedNative<F>>
            + AssertionInstructions<F, AssignedNative<F>>
            + AssignmentInstructions<F, AssignedNative<F>>,
        F: crate::CircuitField,
    {
        if let Some(roots) = self.0.get(&(x.clone(), t)) {
            return Ok(roots.clone());
        }

        let z = if t == 1 {
            x.clone()
        } else {
            // A point with no `t`-th root gets 0, which fails `z^t = x`.
            let z = x.value().map(|x| roots(*x, t).map_or(F::ZERO, |roots| roots[0]));
            let z = scalar_chip.assign(layouter, z)?;
            let z_pow_t = scalar_chip.pow(layouter, &z, t as u64)?;
            scalar_chip.assert_equal(layouter, &z_pow_t, x)?;
            z
        };

        let omega_t = F::ROOT_OF_UNITY.pow_vartime([1u64 << (F::S - t.trailing_zeros())]);
        let mut roots = vec![z.clone()];
        let mut omega_pow = omega_t;
        for _ in 1..t {
            roots.push(scalar_chip.mul_by_constant(layouter, &z, omega_pow)?);
            omega_pow *= omega_t;
        }

        self.0.insert((x.clone(), t), roots.clone());
        Ok(roots)
    }
}

/// `Σ_i root^i coeffs[i]`, by Horner.
fn horner<F: crate::CircuitField>(
    layouter: &mut impl Layouter<F>,
    scalar_chip: &impl ArithInstructions<F, AssignedNative<F>>,
    coeffs: &[&AssignedNative<F>],
    root: &AssignedNative<F>,
) -> Result<AssignedNative<F>, Error> {
    let (last, rest) = coeffs.split_last().expect("a chunk holds at least one polynomial");
    (rest.iter().rev()).try_fold((*last).clone(), |acc, c| {
        mul_add(layouter, scalar_chip, &acc, root, c)
    })
}
