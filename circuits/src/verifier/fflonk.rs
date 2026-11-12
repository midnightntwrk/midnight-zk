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

use std::collections::{BTreeMap, HashMap, hash_map::Entry};

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{
        PolynomialLabel::{self, Collection},
        commitment::InterleavedCommit,
        fflonk::{Fflonk, balanced_chunks},
    },
    transcript::Hashable,
};

use crate::{
    CircuitField,
    field::AssignedNative,
    instructions::ArithInstructions,
    types::InnerValue,
    verifier::{
        ScalarChip,
        pcs::{InCircuitPCS, VerifierQuery},
        transcript_gadget::InCircuitTranscript,
        utils::{PowersCache, RootsCache, cached_roots, eval_polynomial_on_roots},
    },
};

/// In circuit implementation of Fflonk.
impl<F, PCS, const LOG2_T_MAX: u32> InCircuitPCS<F> for Fflonk<PCS, LOG2_T_MAX>
where
    F: CircuitField,
    PCS: InCircuitPCS<F> + InterleavedCommit<F>,
{
    type CommitmentChip = PCS::CommitmentChip;
    type AssignedVerificationGuard = PCS::AssignedVerificationGuard;
    type AssignedCommitment = PCS::AssignedCommitment;

    fn fixed_commitment(labels: &[PolynomialLabel]) -> Self::AssignedCommitment {
        PCS::fixed_commitment(&Self::chunk_labels(labels))
    }

    fn fixed_base_labels(labels: &[PolynomialLabel]) -> Vec<PolynomialLabel> {
        PCS::fixed_base_labels(&Self::chunk_labels(labels))
    }

    fn assign_commitment(
        layouter: &mut impl Layouter<F>,
        commitment_chip: &Self::CommitmentChip,
        value: Value<<Self::AssignedCommitment as InnerValue>::Element>,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error> {
        PCS::assign_commitment(
            layouter,
            commitment_chip,
            value,
            &Self::chunk_labels(labels),
        )
    }

    fn read_commitment<T>(
        layouter: &mut impl Layouter<F>,
        commitment_chip: &Self::CommitmentChip,
        transcript: &mut T,
        labels: &[PolynomialLabel],
    ) -> Result<Self::AssignedCommitment, Error>
    where
        Self::Commitment: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
        let labels = Self::chunk_labels(labels);
        <PCS as InCircuitPCS<F>>::read_commitment(layouter, commitment_chip, transcript, &labels)
    }

    fn squeeze_evaluation_point<T: InCircuitTranscript<F>>(
        layouter: &mut impl Layouter<F>,
        scalar_chip: &ScalarChip<F>,
        transcript: &mut T,
    ) -> Result<AssignedNative<F>, Error> {
        let x =
            <PCS as InCircuitPCS<F>>::squeeze_evaluation_point(layouter, scalar_chip, transcript)?;
        scalar_chip.pow(layouter, &x, Self::T_MAX as u64)
    }

    fn commitment_labels(commitment: &Self::AssignedCommitment) -> Vec<PolynomialLabel> {
        <PCS as InCircuitPCS<F>>::commitment_labels(commitment)
            .into_iter()
            .flat_map(|label| match label {
                Collection(labels) => labels,
                label => panic!("fflonk commitment tagged with {label}, not a collection"),
            })
            .collect()
    }

    fn multi_prepare<T>(
        layouter: &mut impl Layouter<F>,
        commitment_chip: &Self::CommitmentChip,
        scalar_chip: &ScalarChip<F>,
        queries: &[VerifierQuery<'_, F, Self>],
        transcript: &mut T,
    ) -> Result<Self::AssignedVerificationGuard, Error>
    where
        F: Hashable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>,
        T: InCircuitTranscript<F>,
    {
        // Maps the labels of every queried chunk to its commitment and the points
        // its polynomials are queried at, in query order: `labels -> (commitment,
        // points)`.
        let chunks_info = queries.iter().fold(BTreeMap::new(), |mut chunks_info, q| {
            let labels = balanced_chunks(
                &<Self as InCircuitPCS<F>>::commitment_labels(q.commitment),
                Self::T_MAX,
            )
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
                        entry.insert(transcript.read(layouter, scalar_chip, &())?);
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
        let mut powers_cache = PowersCache::new();
        for (labels, (commitment, points)) in &chunks_info {
            let t = labels.len().next_power_of_two();
            for x in points {
                let f_evals: Vec<_> =
                    labels.iter().map(|l| &evals[&(l.clone(), x.clone())]).collect();
                let roots = cached_roots(layouter, scalar_chip, &mut roots_cache, x, t)?;
                let root_evals = eval_polynomial_on_roots(
                    layouter,
                    scalar_chip,
                    &mut powers_cache,
                    &f_evals,
                    &roots[0],
                    t,
                )?;
                for (root, eval) in roots.iter().zip(root_evals) {
                    let label = Collection(labels.clone());
                    let query = VerifierQuery::<F, PCS>::new(root, *commitment, label, &eval);
                    inner_queries.push(query.with_root_of(x, t));
                }
            }
        }

        <PCS as InCircuitPCS<F>>::multi_prepare(
            layouter,
            commitment_chip,
            scalar_chip,
            &inner_queries,
            transcript,
        )
    }
}
