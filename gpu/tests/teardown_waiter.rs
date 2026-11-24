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

//! A device call that passed the check for the retired state and then
//! queued a request to the device-owner actor while another call reset
//! the context must not run on the dead context: the actor drops the
//! queued request unrun, the call declines, and no fresh context is
//! made. The state is sticky, so the sequence runs in a child process
//! and the parent checks that it exited with status 0. Without a device
//! the child takes its skip path.
#![cfg(feature = "test-fault")]

use std::time::Duration;

use group::prime::PrimeCurveAffine;
use midnight_curves::{Fq, G1Affine};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;

const CHILD: &str = "MGPU_TEARDOWN_WAITER_CHILD";

#[test]
fn a_call_waiting_for_the_lock_across_the_reset_declines() {
    if std::env::var_os(CHILD).is_none() {
        let exe = std::env::current_exe().expect("test binary path");
        let out = std::process::Command::new(exe)
            .args([
                "--exact",
                "a_call_waiting_for_the_lock_across_the_reset_declines",
                "--nocapture",
            ])
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
    let root = gpu::field::std_root(6).unwrap().0;
    // One good transform: the context and the transform scratch exist.
    let mut warm = [gpu::field::one(); 64];
    assert!(gpu::fft(&mut warm, root, 6));
    let bases = [G1Affine::generator(); 32];
    let scalars = [Fq::from(1); 32];

    // The holder occupies the actor, waits, and resets the context
    // at the end of its operation.
    let holder = std::thread::spawn(|| {
        gpu::teardown::retire_after_holding_lock_for_test(Duration::from_millis(1500));
    });
    // The waiters start while the actor is occupied and the device
    // is still live, so they pass the check for the retired state
    // and queue their requests.
    std::thread::sleep(Duration::from_millis(300));
    assert!(!gpu::teardown::device_disabled(), "the holder still waits");
    let input = [gpu::field::one(); 64];
    let ntt_waiter = std::thread::spawn(move || {
        let mut a = input;
        let ok = gpu::fft(&mut a, root, 6);
        (ok, a == input)
    });
    let msm_waiter = std::thread::spawn(move || {
        gpu::msm_g1(adapter::scalars(&scalars), adapter::affine(&bases)).is_none()
    });
    holder.join().unwrap();
    let (ok, intact) = ntt_waiter.join().unwrap();
    let msm_declined = msm_waiter.join().unwrap();

    assert!(gpu::teardown::device_disabled());
    assert_ne!(
        gpu::context_active(),
        Some(true),
        "a waiter ran on the dead context and made a fresh one"
    );
    assert!(!ok, "the waiting transform declined");
    assert!(intact, "its input is unchanged");
    assert!(msm_declined, "the waiting MSM declined");
    assert!(!gpu::end_request());
    assert_ne!(gpu::context_active(), Some(true));
}
