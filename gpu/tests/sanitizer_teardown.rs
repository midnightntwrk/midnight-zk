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

//! Run separately from the proof tests because erasure failures are
//! process-wide and sticky.
#![cfg(feature = "test-fault")]

use group::{Curve, prime::PrimeCurveAffine};
use midnight_curves::{Fq, G1Affine};
use midnight_gpu::{
    self as gpu,
    fault::{self, Class, Point},
};
use midnight_proofs::gpu::adapter;

#[test]
#[ignore = "requires a CUDA device under compute-sanitizer"]
fn sanitizer_teardown() {
    assert!(gpu::device());
    gpu::set_min_k(1);
    gpu::wipe::set_check(true);
    gpu::end_request_report().unwrap();

    // Keep one Rust-owned scratch region and one sppark context alive.
    let mut scratch = [gpu::field::one(); 64];
    assert!(gpu::fft(
        &mut scratch,
        gpu::field::std_root(6).unwrap().0,
        6
    ));
    let g = G1Affine::generator();
    let bases = [g; 32];
    let scalars = [Fq::from(1); 32];
    let table = gpu::register_srs(adapter::affine(&bases));
    let result = gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).unwrap();
    assert_eq!(
        adapter::from_jacobian(result).to_affine(),
        (g * Fq::from(32)).to_affine()
    );

    // Arm after the last MSM so only the context destructor can consume the fault.
    let live = gpu::device_bytes().0;
    fault::fail_lib_wipes(1);
    drop(table);
    assert_eq!(gpu::wipe::quarantined(), 1);
    assert_eq!(gpu::wipe::erasure_failures(), 1);
    assert_eq!(gpu::device_bytes().0, live);
    let confirmed = gpu::wipe::stats().core[2];

    // The scratch release and its first retry both fail. The sppark retry succeeds.
    fault::arm(Class::Erase, Point::Launch, 2);
    let first = gpu::end_request_report().unwrap_err();
    assert_eq!(fault::fired(Class::Erase), 2);
    assert_eq!(first.erasure_failures, 2);
    assert_eq!(first.quarantined, 1);
    assert!(first.core[2] > confirmed);
    let held = gpu::device_bytes().0;
    assert!(held < live);

    let second = gpu::end_request_report().unwrap_err();
    assert_eq!(second.erasure_failures, 2);
    assert_eq!(second.quarantined, 0);
    assert!(second.device_checked > first.device_checked);
    assert_eq!(
        held - gpu::device_bytes().0,
        std::mem::size_of_val(&scratch) as u64
    );
}
