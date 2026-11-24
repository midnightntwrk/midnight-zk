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

//! A failed erasure of a device region of this crate: the region is kept in
//! quarantine, the proof is still valid and equal to the CPU proof, the
//! failure is counted and sticky (`end_request` reports it from then on), and
//! the end of the request retries and frees the region. In its own test
//! binary: the failure count never resets.
#![cfg(feature = "test-fault")]

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks,
    test_switches::{self, RandomCircuit},
};

#[test]
fn failed_erasure_is_quarantined_and_sticky() {
    use gpu::fault::{self, Class, Point};
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
    let c = RandomCircuit::new(11, true, 8);
    let (cpu, ok) = test_switches::without_hooks(|| c.prove());
    assert!(ok);
    assert!(gpu::end_request(), "a clean start");
    let f0 = gpu::wipe::erasure_failures();
    fault::reset();
    fault::arm(Class::Erase, Point::Launch, 3);
    let (dev, ok) = c.prove();
    assert!(
        ok && dev == cpu,
        "the proof is valid and equal to the CPU proof"
    );
    assert!(fault::fired(Class::Erase) > 0);
    assert!(gpu::wipe::erasure_failures() > f0, "counted");
    assert!(gpu::wipe::quarantined() > 0, "kept");
    fault::reset();
    assert!(!gpu::end_request(), "sticky");
    assert_eq!(gpu::wipe::quarantined(), 0, "the retry freed them");
    assert!(gpu::end_request_report().is_err());
}
