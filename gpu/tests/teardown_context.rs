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

//! An unconfirmed drain retires the device for the rest of the process:
//! the state is sticky, so the sequence runs in a child process and the
//! parent checks that it did not abort and exited with status 0. The
//! child runs the same sequence in a stub build (no context is reset
//! there, but the state and the declines are the same).
#![cfg(feature = "test-fault")]

use group::prime::PrimeCurveAffine;
use midnight_curves::{Fq, G1Affine};
use midnight_gpu as gpu;
use midnight_proofs::gpu::{self as hooks, GpuHooks, adapter, test_switches::RandomCircuit};

const CHILD: &str = "MGPU_TEARDOWN_CONTEXT_CHILD";

fn declined(class: &str) -> u64 {
    gpu::declines()
        .into_iter()
        .filter(|(c, r, _)| *c == class && *r == "teardown")
        .map(|(_, _, n)| n)
        .sum()
}

#[test]
fn unconfirmed_drain_retires_device() {
    if std::env::var_os(CHILD).is_none() {
        assert!(!gpu::teardown::device_disabled());
        assert!(!gpu::teardown::erasure_failed());
        assert_eq!(gpu::teardown::declined_after_teardown(), 0);
        let exe = std::env::current_exe().expect("test binary path");
        let out = std::process::Command::new(exe)
            .args(["--exact", "unconfirmed_drain_retires_device", "--nocapture"])
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
        // The state is per process: the parent is untouched.
        assert!(!gpu::teardown::device_disabled());
        assert!(!gpu::teardown::erasure_failed());
        return;
    }

    assert!(!gpu::teardown::device_disabled());
    assert!(!gpu::teardown::erasure_failed());
    assert_eq!(gpu::teardown::declined_after_teardown(), 0);
    gpu::set_min_k(1);

    if gpu::device() {
        // Build the NTT tables and run one MSM, so device state exists
        // when the context is reset.
        let mut a = [gpu::field::one(); 64];
        assert!(gpu::fft(&mut a, gpu::field::std_root(6).unwrap().0, 6));
        let bases = [G1Affine::generator(); 32];
        let scalars = [Fq::from(1); 32];
        assert!(gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_some());
    }

    gpu::teardown::trigger_unconfirmed_drain_for_test();
    assert!(gpu::teardown::device_disabled());
    assert!(gpu::teardown::erasure_failed());
    assert!(!gpu::device());

    // A second trigger does not reset again; the state stays set.
    gpu::teardown::trigger_unconfirmed_drain_for_test();
    assert!(gpu::teardown::device_disabled());
    assert!(gpu::teardown::erasure_failed());
    assert!(gpu::teardown::teardown_context());

    let n0 = gpu::teardown::declined_after_teardown();

    let bases = [G1Affine::generator(); 32];
    let scalars = [Fq::from(1); 32];
    assert!(gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_none());
    assert_eq!(gpu::teardown::declined_after_teardown(), n0 + 1);
    assert_eq!(declined("msm"), 1);

    let mut a = [gpu::field::one(); 64];
    let keep = a;
    assert!(!gpu::fft(&mut a, gpu::field::std_root(6).unwrap().0, 6));
    assert_eq!(a, keep);
    assert_eq!(gpu::teardown::declined_after_teardown(), n0 + 2);
    assert_eq!(declined("ntt"), 1);

    // Through the hooks, a proof still completes on the CPU and its
    // quotient declines for the same reason.
    assert!(hooks::install(GpuHooks {
        msm_g1: Some(gpu::msm_g1),
        fft: Some(gpu::fft),
        ifft: Some(gpu::ifft),
        quotient: Some(gpu::quotient),
    }));
    let (proof, valid) = RandomCircuit::new(5, true, 6).prove();
    assert!(valid);
    assert!(!proof.is_empty());
    assert!(declined("quotient") >= 1, "{:?}", gpu::declines());
    assert!(gpu::teardown::declined_after_teardown() > n0 + 2);

    assert!(!gpu::end_request());
}
