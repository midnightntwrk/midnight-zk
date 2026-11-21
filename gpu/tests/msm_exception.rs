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

//! An exception inside sppark's MSM other than a CUDA error (here injected
//! after the bucket-row copies are enqueued) never reaches Rust: the MSM
//! drains its streams, returns an error and the hook declines, and the
//! process lives on. Without the catch-all arms the exception crosses the C
//! boundary and the process aborts, so the MSM runs in a child process.
#![cfg(feature = "test-fault")]

use ff::Field;
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_core::SeedableRng;

const MARK: &str = "msm-exception-child-survived";

#[test]
fn msm_exception_never_reaches_rust() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "child",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("MIDNIGHT_GPU_TEST_CHILD", "1")
        .output()
        .expect("the child starts");
    let text = String::from_utf8_lossy(&out.stdout);
    let err = String::from_utf8_lossy(&out.stderr);
    eprintln!("child status {:?}", out.status);
    assert!(
        out.status.success() && text.contains(MARK),
        "the child did not survive the injected exception: {:?}\n{}",
        out.status,
        err.lines().rev().take(5).collect::<Vec<_>>().join("\n")
    );
}

#[test]
#[ignore = "run by msm_exception_never_reaches_rust in a child process"]
fn child() {
    if std::env::var_os("MIDNIGHT_GPU_TEST_CHILD").is_none() {
        return;
    }
    gpu::set_min_k(1);
    let n = 1 << 14;
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(21);
    let g = G1Projective::generator();
    let bases: Vec<G1Affine> = (1..=n as u64).map(|i| (g * Fq::from(i)).to_affine()).collect();
    let s: Vec<Fq> = (0..n).map(|_| Fq::random(&mut rng)).collect();
    let before = gpu::stats().device_errors;
    gpu::fault::msm_throw_next(1);
    let r = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&bases));
    assert!(
        r.is_none(),
        "the MSM returns an error, the caller falls back"
    );
    assert_eq!(gpu::stats().device_errors, before + 1, "counted");
    // the device still works
    let ok = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&bases));
    assert!(ok.is_some(), "the next MSM runs");
    println!("{MARK}");
}
