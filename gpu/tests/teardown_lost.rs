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

//! A context teardown must not report a quarantined block whose zeroing
//! was never confirmed as gone: the reset frees device memory but does
//! not zero it. The teardown state is sticky, so each sequence runs in
//! a child process and the parent checks that it exited with status 0.
//! Without a device the child takes its skip path.
#![cfg(feature = "test-fault")]

use group::prime::PrimeCurveAffine;
use midnight_curves::{Fq, G1Affine};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;

const CHILD: &str = "MGPU_TEARDOWN_LOST_CHILD";

fn run_child(test: &str, mode: &str) {
    let exe = std::env::current_exe().expect("test binary path");
    let out = std::process::Command::new(exe)
        .args(["--exact", test, "--nocapture"])
        .env(CHILD, mode)
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

/// One one-shot MSM: its library blocks are zeroed by the CUDA core when
/// the temporary context is freed at the end of the call.
fn one_msm() {
    let bases = [G1Affine::generator(); 32];
    let scalars = [Fq::from(1); 32];
    assert!(gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_some());
}

#[test]
fn context_teardown_counts_unerased_quarantine() {
    if std::env::var_os(CHILD).is_none() {
        run_child("context_teardown_counts_unerased_quarantine", "lost");
        // The state is per process: the parent is untouched.
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

    // Every library zeroing fails: the wipe at the release of the MSM
    // blocks and every later one, the pre-reset attempt included. The
    // switch is consumed once per `wipe_block` call of the core, in
    // both places, so a large count keeps the blocks unconfirmed.
    gpu::fault::fail_lib_wipes(10_000);
    one_msm();
    let p = gpu::wipe::pending_erasure();
    assert!(p.lib_unerased >= 1, "an unconfirmed block is held: {p:?}");
    assert!(p.lib_unerased_bytes > 0, "with its bytes: {p:?}");
    assert!(!p.clear(), "not clear while a block is unconfirmed");

    assert!(
        gpu::teardown::teardown_context(),
        "the context reset succeeded"
    );
    gpu::fault::fail_lib_wipes(0);
    assert!(gpu::teardown::device_disabled());
    assert!(gpu::teardown::erasure_failed());
    // The reset freed the block's memory without zeroing it: the erasure
    // stays pending for the rest of the process. On the code before
    // this accounting the quarantine was simply cleared at the reset,
    // so this assertion failed there (`clear()` was true).
    let p = gpu::wipe::pending_erasure();
    assert!(
        !p.clear(),
        "an unerased block lost at the reset stays pending: {p:?}"
    );
    assert!(p.reset_unerased >= 1, "lost unerased at the reset: {p:?}");
    assert!(p.reset_unerased_bytes > 0, "with its bytes: {p:?}");
    assert_eq!(p.lib_unerased, 0, "no block is still held: {p:?}");
    assert_eq!(gpu::wipe::quarantined(), 0, "the lists are cleared");
}

#[test]
fn context_teardown_zeroes_quarantine_before_reset() {
    if std::env::var_os(CHILD).is_none() {
        run_child("context_teardown_zeroes_quarantine_before_reset", "zeroed");
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

    // One library zeroing fails at its release; the pre-reset attempt of
    // the teardown then succeeds, so nothing is lost unerased.
    gpu::fault::fail_lib_wipes(1);
    one_msm();
    gpu::fault::fail_lib_wipes(0);
    let p = gpu::wipe::pending_erasure();
    assert!(p.lib_unerased >= 1, "an unconfirmed block is held: {p:?}");

    assert!(
        gpu::teardown::teardown_context(),
        "the context reset succeeded"
    );
    let p = gpu::wipe::pending_erasure();
    assert_eq!(
        p.lib_unerased, 0,
        "the block was zeroed before the reset: {p:?}"
    );
    assert_eq!(p.reset_unerased, 0, "nothing was lost unerased: {p:?}");
    assert_eq!(
        p.reset_unerased_bytes, 0,
        "nothing was lost unerased: {p:?}"
    );
    assert!(p.clear(), "nothing is pending: {p:?}");
}
