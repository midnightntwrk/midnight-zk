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

//! After a successful context reset every device pointer is dead:
//! dropping the holders and the end-of-request calls must make no CUDA
//! call, count no new erasure failure and make no fresh context. The
//! teardown state is sticky, so each sequence runs in a child process
//! and the parent checks that it exited with status 0.
#![cfg(feature = "test-fault")]

use group::prime::PrimeCurveAffine;
use midnight_curves::{Fq, G1Affine};
use midnight_gpu::{self as gpu, abi::QuotientJobAbi, field};
use midnight_proofs::gpu::{self as hooks, GpuHooks, adapter, test_switches::RandomCircuit};

const CHILD: &str = "MGPU_TEARDOWN_HOLDERS_CHILD";

fn run_child(test: &str) {
    let exe = std::env::current_exe().expect("test binary path");
    let out = std::process::Command::new(exe)
        .args(["--exact", test, "--nocapture"])
        .env(CHILD, "1")
        .output()
        .expect("run the child test process");
    assert!(
        out.status.success(),
        "child exited with {:?}\nstdout: {}\nstderr: {}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

fn declined(reason: &str) -> u64 {
    gpu::declines()
        .into_iter()
        .filter(|(c, r, _)| *c == "quotient" && *r == reason)
        .map(|(_, _, n)| n)
        .sum()
}

#[test]
fn holders_after_teardown_make_no_device_call() {
    if std::env::var_os(CHILD).is_none() {
        run_child("holders_after_teardown_make_no_device_call");
        assert!(!gpu::teardown::device_disabled());
        return;
    }
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    gpu::set_min_k(1);
    assert!(hooks::install(GpuHooks {
        msm_g1: Some(gpu::msm_g1),
        fft: Some(gpu::fft),
        ifft: Some(gpu::ifft),
        quotient: Some(gpu::quotient),
    }));

    // A proof (the quotient runs, its read-back uses the private host
    // buffer) and a transform large enough to allocate the staging
    // bounce buffer (a copy of 16 MiB or more).
    let (proof, valid) = RandomCircuit::new(5, true, 6).prove();
    assert!(valid);
    assert!(!proof.is_empty());
    let mut a = vec![field::one(); 1usize << 19];
    assert!(gpu::fft(&mut a, field::std_root(19).unwrap().0, 19));
    drop(a);

    // A registered SRS with a live device context, and a registered
    // proving key.
    let bases = [G1Affine::generator(); 32];
    let scalars = [Fq::from(1); 32];
    let srs = gpu::register_srs(adapter::affine(&bases));
    assert!(gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_some());
    let poly = vec![field::one(); 64];
    let key = gpu::register_key(&[&poly[..]]);

    assert!(gpu::teardown::teardown_context(), "the reset succeeded");
    assert!(gpu::teardown::device_disabled());

    // Nothing below may free or use a dead device pointer: no CUDA
    // call, no new erasure failure, no fresh context.
    let failures = gpu::wipe::erasure_failures();
    drop(srs);
    drop(key);
    gpu::evict_tables();
    let _ = gpu::end_request();
    assert_eq!(
        gpu::wipe::erasure_failures(),
        failures,
        "no erasure failure after the teardown"
    );
    assert_eq!(gpu::wipe::quarantined(), 0, "nothing is held for a retry");
    assert_ne!(
        gpu::context_active(),
        Some(true),
        "no call made a fresh context"
    );
}

/// The public quotient path keeps its header-first order while the
/// device is retired: a job whose header fails declines for its header
/// reason, and only a job that passes the header declines for the
/// teardown. This runs without a device too (the retirement is the
/// same, only no context is reset).
#[test]
fn quotient_after_teardown_keeps_header_first_order() {
    if std::env::var_os(CHILD).is_none() {
        run_child("quotient_after_teardown_keeps_header_first_order");
        assert!(!gpu::teardown::device_disabled());
        return;
    }
    gpu::set_min_k(14);
    assert!(gpu::teardown::teardown_context());
    assert!(gpu::teardown::device_disabled());

    let job = |z: gpu::Scalar| {
        // SAFETY: a plain repr(C) struct of integers and pointers; zero
        // is valid. A header only: every check below fails (or, for the
        // passing header, stops at the teardown) before any pointer
        // field is read.
        let mut j: QuotientJobAbi = unsafe { std::mem::zeroed() };
        j.abi = gpu::abi::QUOTIENT_ABI;
        (j.k, j.ext_k) = (15, 16);
        let z2 = field::square(&z);
        j.zeta = [z, z2];
        j.zeta_out = [z2, z];
        j
    };
    let try_job = |j: &QuotientJobAbi| {
        let mut out = vec![[7u64; 4]; 8];
        // SAFETY: the header-only job, as above.
        let ok = unsafe { gpu::quotient(j as *const _ as *const std::ffi::c_void, &mut out) };
        assert!(!ok);
        assert!(
            out.iter().all(|v| *v == [7u64; 4]),
            "the output is untouched"
        );
    };

    // A header that fails (2 is no cube root of unity): `shape`, and no
    // teardown decline is counted for it.
    let (shape, teardown) = (declined("shape"), declined("teardown"));
    try_job(&job(field::from_u64(2)));
    assert_eq!(
        declined("shape"),
        shape + 1,
        "the header reason comes first"
    );
    assert_eq!(declined("teardown"), teardown, "not counted as a teardown");

    // A header that passes: the teardown decline, counted once.
    let retired = gpu::teardown::declined_after_teardown();
    try_job(&job(field::primitive_cube_root()));
    assert_eq!(declined("teardown"), teardown + 1, "the teardown reason");
    assert_eq!(gpu::teardown::declined_after_teardown(), retired + 1);
}

/// A host buffer kept after an unconfirmed drain is zeroed when the
/// context teardown runs: the reset ended every transfer, so the
/// bounce buffer and the read-back buffer can be wiped on the host
/// (the page-locked one is then leaked, the plain one freed), without
/// counting the erasure failure that the keeping already counted.
/// The counters are read before the driver so the test holds whether
/// the retirement runs at the driver call or at the explicit
/// teardown below. On the code before the fix the read-back buffer
/// was kept unwiped by its free path, so the zeroed count was one
/// short. Without a device the child takes its skip path.
#[test]
fn held_host_buffers_are_zeroed_at_teardown() {
    if std::env::var_os(CHILD).is_none() {
        run_child("held_host_buffers_are_zeroed_at_teardown");
        assert!(!gpu::teardown::device_disabled());
        return;
    }
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let (wiped0, failures0) = (gpu::wipe::stats().stage[0], gpu::wipe::erasure_failures());
    let p = gpu::fault::stage_paths_after_unconfirmed_drain().expect("the driver runs");
    assert!(gpu::teardown::teardown_context(), "the reset succeeded");
    assert!(gpu::teardown::device_disabled());
    let held = if p[0] == 2 { 1 } else { 2 };
    assert_eq!(
        gpu::wipe::stats().stage[0] - wiped0,
        held,
        "every held host buffer is zeroed at the teardown: {p:?}"
    );
    assert_eq!(
        gpu::wipe::erasure_failures() - failures0,
        held,
        "one erasure failure per held buffer, none counted again"
    );
    assert_eq!(
        gpu::xfer::stats().stage[7],
        0,
        "no bounce bytes are held after the teardown"
    );
}
