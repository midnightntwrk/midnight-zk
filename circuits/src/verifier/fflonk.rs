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
//! a group are committed in the [`balanced_chunks`] of at most `T_MAX`, each
//! chunk under the label `Collection(chunk)`, and opening a chunk at `x`
//! amounts to opening it with the inner PCS at the `t`-th roots of `x`.

use std::{
    collections::{BTreeMap, HashMap, hash_map::Entry},
    marker::PhantomData,
};

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{
        PolynomialLabel::{self, Collection},
        commitment::InterleavedCommit,
        fflonk::{Fflonk, balanced_chunks},
    },
};

use crate::{
    field::AssignedNative,
    instructions::ArithInstructions,
    types::InnerValue,
    verifier::{
        AssignedAccumulator, SelfEmulation,
        pcs::{InCircuitPCS, VerifierQuery},
        transcript_gadget::TranscriptGadget,
        utils::{RootsCache, cached_roots, eval_polynomial},
    },
};

/// fflonk over the inner in-circuit `PCS`, combining at most `T_MAX =
/// 2^LOG2_T_MAX` polynomials per chunk. Verifies the proofs of
/// [`Fflonk<PCS::OffCircuitPCS, LOG2_T_MAX>`](Fflonk).
#[derive(Clone, Copy, Debug)]
pub struct InCircuitFflonk<PCS, const LOG2_T_MAX: u32>(PhantomData<PCS>);

impl<PCS, const LOG2_T_MAX: u32> InCircuitFflonk<PCS, LOG2_T_MAX> {
    /// The maximum number of polynomials combined into one.
    const T_MAX: usize = 1 << LOG2_T_MAX;

    /// The labels of the inner commitments to the group `labels`.
    fn chunk_labels(labels: &[PolynomialLabel]) -> Vec<PolynomialLabel> {
        PolynomialLabel::assert_distinct(labels);
        balanced_chunks(labels, Self::T_MAX).map(|l| Collection(l.to_vec())).collect()
    }
}

impl<S, PCS, const LOG2_T_MAX: u32> InCircuitPCS<S> for InCircuitFflonk<PCS, LOG2_T_MAX>
where
    S: SelfEmulation,
    PCS: InCircuitPCS<S, OffCircuitPCS: InterleavedCommit<S::F>>,
{
    type OffCircuitPCS = Fflonk<PCS::OffCircuitPCS, LOG2_T_MAX>;
    type AssignedCommitment = PCS::AssignedCommitment;

    fn fixed_commitment(labels: &[PolynomialLabel]) -> Self::AssignedCommitment {
        PCS::fixed_commitment(&Self::chunk_labels(labels))
    }

    fn fixed_base_labels(labels: &[PolynomialLabel]) -> Vec<PolynomialLabel> {
        PCS::fixed_base_labels(&Self::chunk_labels(labels))
    }

    fn assign_commitment(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        value: Value<<Self::AssignedCommitment as InnerValue>::Element>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        PCS::assign_commitment(layouter, curve_chip, value, &Self::chunk_labels(labels))
    }

    fn commitment_as_public_input(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        commitment: &Self::AssignedCommitment,
    ) -> Result<Vec<AssignedNative<S::F>>, Error> {
        PCS::commitment_as_public_input(layouter, curve_chip, commitment)
    }

    fn read_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        PCS::read_commitment(transcript, layouter, &Self::chunk_labels(labels))
    }

    fn common_commitment(
        transcript: &mut TranscriptGadget<S>,
        layouter: &mut impl Layouter<S::F>,
        commitment: &Self::AssignedCommitment,
    ) -> Result<(), Error> {
        PCS::common_commitment(transcript, layouter, commitment)
    }

    fn squeeze_evaluation_point(
        layouter: &mut impl Layouter<S::F>,
        scalar_chip: &S::ScalarChip,
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedNative<S::F>, Error> {
        let x = PCS::squeeze_evaluation_point(layouter, scalar_chip, transcript)?;
        scalar_chip.pow(layouter, &x, Self::T_MAX as u64)
    }

    fn commitment_labels(commitment: &Self::AssignedCommitment) -> Vec<PolynomialLabel> {
        PCS::commitment_labels(commitment)
            .into_iter()
            .flat_map(|label| match label {
                Collection(labels) => labels,
                label => panic!("fflonk commitment tagged with {label}, not a collection"),
            })
            .collect()
    }

    fn multi_prepare(
        layouter: &mut impl Layouter<S::F>,
        curve_chip: &S::CurveChip,
        scalar_chip: &S::ScalarChip,
        queries: &[VerifierQuery<'_, S, Self>],
        transcript: &mut TranscriptGadget<S>,
    ) -> Result<AssignedAccumulator<S>, Error> {
        // Maps the labels of every queried chunk to its commitment and the points
        // its polynomials are queried at, in query order: `labels -> (commitment,
        // points)`.
        let chunks_info = queries.iter().fold(BTreeMap::new(), |mut chunks_info, q| {
            let labels = balanced_chunks(&Self::commitment_labels(q.commitment), Self::T_MAX)
                .find(|labels| labels.contains(&q.label))
                .map_or_else(|| vec![q.label.clone()], <[_]>::to_vec);
            let (_, points) = chunks_info.entry(labels).or_insert((q.commitment, Vec::new()));
            if !points.contains(&q.point) {
                points.push(q.point.clone());
            }
            chunks_info
        });

        // The evaluations of the chunks at all the points, both the explicit (taken
        // from the queries) and the implicit (read from the transcript here) ones.
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

        // Opening a chunk at `x` amounts to opening its `g` polynomial at
        // the `t`-th roots of `x`, where computing `g(r) = Σ_i r^i f_i(x)` for
        // such a root `r` is equivalent to evaluating at `r` the polynomial with
        // coefficients `f_i(x)`.
        let mut inner_queries = Vec::new();
        let mut roots_cache = RootsCache::new();
        for (labels, (commitment, points)) in &chunks_info {
            let t = labels.len().next_power_of_two();
            for x in points {
                let f_evals: Vec<_> =
                    labels.iter().map(|l| &evals[&(l.clone(), x.clone())]).collect();
                for root in cached_roots(layouter, scalar_chip, &mut roots_cache, x, t)? {
                    let eval = eval_polynomial(layouter, scalar_chip, &f_evals, root)?;
                    let label = Collection(labels.clone());
                    let query = VerifierQuery::<S, PCS>::new(root, *commitment, label, &eval);
                    inner_queries.push(query.with_root_of(x, t));
                }
            }
        }

        PCS::multi_prepare(
            layouter,
            curve_chip,
            scalar_chip,
            &inner_queries,
            transcript,
        )
    }
}
