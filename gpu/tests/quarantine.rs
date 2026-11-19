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

//! sppark's own device blocks: a zeroing that fails keeps the block in
//! quarantine and counts a sticky erasure failure; the end of the request
//! retries the block and frees it. In its own test binary: the failure count
//! never resets.
#![cfg(feature = "test-fault")]

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_core::SeedableRng;

#[test]
fn failed_lib_wipe_is_quarantined_and_retried() {
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
    let (q0, f0) = (gpu::wipe::quarantined(), gpu::wipe::erasure_failures());
    // the next zeroing of an sppark block (the one-shot context's blob) fails
    gpu::fault::fail_lib_wipes(1);
    let got = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&bases));
    gpu::fault::fail_lib_wipes(0);
    assert_eq!(
        got.map(|r| adapter::from_jacobian(r).to_affine()),
        Some(want.to_affine()),
        "the MSM result is right"
    );
    assert_eq!(gpu::wipe::quarantined(), q0 + 1, "the block is kept");
    assert_eq!(
        gpu::wipe::erasure_failures(),
        f0 + 1,
        "the failure is counted"
    );
    let live = gpu::device_bytes().0;
    // the retry zeroes and frees it; the failure stays counted (sticky)
    assert!(
        !gpu::end_request(),
        "end_request reports the sticky failure"
    );
    assert_eq!(gpu::wipe::quarantined(), q0, "the retry freed the block");
    assert!(gpu::device_bytes().0 < live, "its bytes are released");
    assert!(gpu::end_request_report().is_err());

    // one block kept by both a failed release and a failed teardown is one
    // quarantine entry and one failure (a second entry would make the retry
    // zero and free an address that may be reused)
    let (q1, f1) = (gpu::wipe::quarantined(), gpu::wipe::erasure_failures());
    assert_eq!(gpu::fault::double_quarantine(), Some((1, 1)));
    assert_eq!(gpu::wipe::quarantined(), q1 + 1);
    assert_eq!(gpu::wipe::erasure_failures(), f1 + 1);
    let _ = gpu::end_request();
    assert_eq!(gpu::wipe::quarantined(), q1, "the retry frees it once");
}
