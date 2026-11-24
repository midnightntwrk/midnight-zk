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

//! No bucket record carries an earlier MSM's coordinates into the next one
//! (sppark patch in `ec/xyzz_t.hpp`, see `third_party/sppark/PATCHES.md`):
//! two MSMs on one reused context, the second with almost every scalar zero
//! so that most buckets are empty. After the second MSM every word of an
//! empty (infinite) record is zero, and every occupied record has other
//! coordinates than the same record after the first MSM.
#![cfg(feature = "test-fault")]

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_core::SeedableRng;

#[test]
fn reused_context_leaves_no_bucket_residue() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let n = 1 << 12;
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(14);
    let g = G1Projective::generator();
    let bases: Vec<G1Affine> = (1..=n as u64).map(|i| (g * Fq::from(i)).to_affine()).collect();
    let first: Vec<Fq> = (0..n).map(|_| Fq::random(&mut rng)).collect();
    let mut second = vec![Fq::ZERO; n];
    for (i, s) in second.iter_mut().take(4).enumerate() {
        *s = Fq::from(3 + i as u64);
    }
    let (a, b, w) = gpu::fault::msm_bucket_records(
        adapter::affine(&bases),
        adapter::scalars(&first),
        adapter::scalars(&second),
    )
    .expect("the probe runs");
    assert_eq!(w % 4, 0, "four equal coordinates per record");
    assert_eq!(a.len(), b.len());
    let c = w / 4;
    let (mut empty, mut primed, mut occupied) = (0usize, 0usize, 0usize);
    for (i, (ra, rb)) in a.chunks(w).zip(b.chunks(w)).enumerate() {
        let (xy_a, xy_b) = (&ra[..2 * c], &rb[..2 * c]);
        let inf = rb[2 * c..].iter().all(|v| *v == 0);
        if inf {
            empty += 1;
            primed += usize::from(xy_a.iter().any(|v| *v != 0));
            assert!(
                rb.iter().all(|v| *v == 0),
                "record {i}: empty after the second MSM but X or Y is not zero"
            );
        } else {
            occupied += 1;
            assert_ne!(
                xy_a, xy_b,
                "record {i}: occupied with the first MSM's coordinates"
            );
        }
    }
    eprintln!(
        "records {}: empty {empty} (held first-MSM X/Y before: {primed}), occupied {occupied}",
        a.len() / w
    );
    assert!(
        primed > 0,
        "the first MSM left coordinates in buckets the second leaves empty"
    );
    assert!(occupied > 0);
    assert!(gpu::end_request());
}
