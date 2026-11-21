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

//! The pending-erasure report under a failed pre-zeroing
//! synchronisation: the synchronisation still runs and the memset is
//! attempted, but the block's zeroing is not confirmed, so it is
//! pending and the report is not clear. The end-of-request retry
//! zeroes and frees it; the synchronisation failure stays counted.
//! In its own test binary: the failure counts never reset.
#![cfg(feature = "test-fault")]

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_core::SeedableRng;

#[test]
fn failed_presync_is_pending_until_retried() {
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

    // the next pre-zeroing synchronisation of a library block counts as
    // failed (the synchronisation and the memset still run)
    gpu::fault::fail_wipe_presync(1);
    let got = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&bases));
    gpu::fault::fail_wipe_presync(0);
    assert_eq!(
        got.map(|r| adapter::from_jacobian(r).to_affine()),
        Some(want.to_affine()),
        "the MSM result is right"
    );
    let p = gpu::wipe::pending_erasure();
    assert_eq!(
        p.presync_failures,
        p0.presync_failures + 1,
        "the failed synchronisation is counted: {p:?}"
    );
    assert!(
        p.lib_unerased >= 1,
        "its zeroing is not confirmed, so the block is pending: {p:?}"
    );
    assert!(p.lib_unerased_bytes > 0, "with its bytes: {p:?}");
    assert_eq!(p.rust_blocks, 0, "no region of this crate is held: {p:?}");
    assert!(!p.clear(), "not clear while a block is unconfirmed");

    // the retry zeroes and frees it; both failure counts stay (sticky)
    assert!(
        !gpu::end_request(),
        "end_request reports the sticky failure"
    );
    let p = gpu::wipe::pending_erasure();
    assert_eq!(p.lib_unerased, 0, "the retry confirmed the zeroing: {p:?}");
    assert_eq!(p.lib_unerased_bytes, 0, "{p:?}");
    assert_eq!(p.lib_zeroed_unfreed, 0, "and freed the block: {p:?}");
    assert_eq!(p.rust_blocks, 0, "{p:?}");
    assert_eq!(
        p.presync_failures,
        p0.presync_failures + 1,
        "the failed synchronisation still shows: {p:?}"
    );
    assert!(p.clear(), "clear once nothing unconfirmed is held");
    assert_eq!(gpu::wipe::quarantined(), 0);
}
