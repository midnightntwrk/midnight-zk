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

//! `MIDNIGHT_GPU_WIPE_CHECK=1` alone turns on the check of the CUDA core's
//! frees too (sppark's blocks), not only the Rust side's. In its own test
//! binary (the variable is read once per process).

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_core::SeedableRng;

#[test]
fn env_check_reaches_the_core() {
    // SAFETY: the only test of this binary, before any device call.
    unsafe { std::env::set_var("MIDNIGHT_GPU_WIPE_CHECK", "1") };
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    assert!(gpu::wipe::check());
    gpu::set_min_k(1);
    let n = 1 << 10;
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
    let g = G1Projective::generator();
    let bases: Vec<G1Affine> = (1..=n as u64).map(|i| (g * Fq::from(i)).to_affine()).collect();
    let s: Vec<Fq> = (0..n).map(|_| Fq::random(&mut rng)).collect();
    // a one-shot MSM: sppark allocates and frees its own blocks
    assert!(gpu::msm_g1(adapter::scalars(&s), adapter::affine(&bases)).is_some());
    let w = gpu::wipe::stats();
    assert!(w.core[0] > 0, "sppark blocks were zeroed: {w:?}");
    assert_eq!(w.core[2], w.core[0], "each one was checked: {w:?}");
    assert_eq!(w.core[3], 0);
    assert!(gpu::end_request());
}
