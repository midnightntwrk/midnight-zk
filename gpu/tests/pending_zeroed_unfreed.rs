// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The pending-erasure report under a failed free after a confirmed
//! zeroing: the block holds no witness bytes, so it is reported as
//! zeroed but unfreed and the report stays clear; it is held in the
//! core's quarantine until the end-of-request retry frees it. In its
//! own test binary: the failure count never resets.
#![cfg(feature = "test-fault")]

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_core::SeedableRng;

#[test]
fn failed_free_after_zeroing_is_zeroed_unfreed_until_retried() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    gpu::set_min_k(1);
    let n = 1 << 10;
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(7);
    let g = G1Projective::generator();
    let bases: Vec<G1Affine> = (1..=n as u64).map(|i| (g * Fq::from(i)).to_affine()).collect();
    let s: Vec<Fq> = (0..n).map(|_| Fq::random(&mut rng)).collect();
    let want = G1Affine::multi_exp_affine(&bases, &s);

    assert!(gpu::end_request(), "a clean start");
    let p0 = gpu::wipe::pending_erasure();
    assert_eq!(p0, gpu::wipe::PendingErasure::default(), "nothing pending");
    assert!(p0.clear());
    let f0 = gpu::wipe::erasure_failures();

    // the next free of a library block after its confirmed zeroing
    // counts as failed without freeing
    gpu::fault::fail_lib_frees(1);
    let got = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&bases));
    gpu::fault::fail_lib_frees(0);
    assert_eq!(
        got.map(|r| adapter::from_jacobian(r).to_affine()),
        Some(want.to_affine()),
        "the MSM result is right"
    );
    let p = gpu::wipe::pending_erasure();
    assert!(
        p.lib_zeroed_unfreed >= 1,
        "a zeroed block waits for its free: {p:?}"
    );
    assert_eq!(
        p.lib_unerased, 0,
        "its zeroing was confirmed, so nothing is unerased: {p:?}"
    );
    assert_eq!(p.lib_unerased_bytes, 0, "{p:?}");
    assert_eq!(p.rust_blocks, 0, "no region of this crate is held: {p:?}");
    assert!(
        p.clear(),
        "clear: the held block holds no witness bytes: {p:?}"
    );
    assert!(
        gpu::wipe::erasure_failures() > f0,
        "the failed free is counted"
    );
    assert!(
        gpu::wipe::quarantined() >= 1,
        "the block is held for the retry of its free"
    );

    // the retry frees it; the failure stays counted (sticky)
    assert!(
        !gpu::end_request(),
        "end_request reports the sticky failure"
    );
    let p = gpu::wipe::pending_erasure();
    assert_eq!(
        p,
        gpu::wipe::PendingErasure::default(),
        "everything is erased and freed"
    );
    assert!(p.clear());
    assert_eq!(
        gpu::wipe::quarantined(),
        0,
        "the core's quarantine is empty"
    );
}
