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

//! A failed check-mode count of a zeroed device region (the call returns an
//! error, so no count comes back) is a check failure, not a non-zero region:
//! `check_failures` grows, `device_nonzero` does not. The region is still
//! kept in quarantine and the erasure failure is still counted, so the
//! request ends as failed (the retirement rule is unchanged). In its own test
//! binary: the failure count never resets.
#![cfg(feature = "test-fault")]

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks,
    test_switches::{self, RandomCircuit},
};

#[test]
fn failed_check_call_is_a_check_failure_not_nonzero() {
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
    gpu::wipe::set_check(true);
    let f0 = gpu::wipe::erasure_failures();
    fault::reset();
    fault::arm(Class::Erase, Point::Check, 1);
    let (dev, ok) = c.prove();
    assert!(
        ok && dev == cpu,
        "the proof is valid and equal to the CPU proof"
    );
    assert_eq!(
        fault::fired(Class::Erase),
        1,
        "the injected check failure ran"
    );
    let s = gpu::wipe::stats();
    assert_eq!(s.check_failures, 1, "counted as a check failure: {s:?}");
    assert_eq!(
        s.device_nonzero, 0,
        "not counted as a non-zero region: {s:?}"
    );
    assert!(
        s.device_checked > 0,
        "the other regions were checked: {s:?}"
    );
    assert!(
        gpu::wipe::erasure_failures() > f0,
        "the erasure failure is counted"
    );
    assert!(gpu::wipe::quarantined() > 0, "the region is kept");
    fault::reset();
    assert!(
        !gpu::end_request(),
        "sticky: the request still ends as failed"
    );
    assert_eq!(gpu::wipe::quarantined(), 0, "the retry freed it");
    let r = gpu::end_request_report();
    assert!(r.is_err(), "the report is a failure");
    gpu::wipe::set_check(false);
}
