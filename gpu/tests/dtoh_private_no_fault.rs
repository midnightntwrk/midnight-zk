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

//! In a build without the feature `test-fault`, the fault argument of
//! `mgpu_dtoh_private` must have no effect: the injected read-back
//! failure exists only in a `test-fault` build (the core is then
//! compiled with `MGPU_TEST_FAULT`). This binary is empty in stub and
//! `test-fault` builds.
//!
//! The symbols are declared here because the crate's FFI module is
//! private; their signatures mirror `gpu/src/ffi.rs`. The crate sends
//! every device call to its device-owner thread. This binary runs a
//! single device test, makes the CUDA context through the public
//! `device()` first (on that thread), and then calls the core directly
//! from the test thread, in sequence, while the crate itself makes no
//! device call: the owner thread is idle for the whole test. The private buffer
//! that `mgpu_dtoh_private` returns is owned by the core: the bytes are
//! copied out with `mgpu_host_copy`, and `mgpu_stage_end` (what
//! `end_request` calls) zeroes and frees it.
#![cfg(all(midnight_gpu_cuda, not(feature = "test-fault")))]

use std::ffi::{CStr, c_char, c_void};

use midnight_gpu as gpu;

unsafe extern "C" {
    fn mgpu_dev_alloc(bytes: usize) -> *mut c_void;
    fn mgpu_dev_free(p: *mut c_void) -> i32;
    fn mgpu_htod(dst: *mut c_void, src: *const c_void, bytes: usize) -> i32;
    fn mgpu_dtoh_private(src: *const c_void, bytes: usize, fault: i32) -> *const c_void;
    fn mgpu_host_copy(dst: *mut c_void, src: *const c_void, bytes: usize);
    fn mgpu_stage_end() -> i32;
    fn mgpu_last_error() -> *const c_char;
}

fn last_error() -> String {
    // SAFETY: the core returns a NUL-terminated thread-local buffer.
    unsafe { CStr::from_ptr(mgpu_last_error()) }.to_string_lossy().into_owned()
}

#[test]
fn dtoh_private_with_fault_argument_succeeds_without_test_fault() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let pattern: Vec<u8> = (0..8192usize).map(|i| (i * 31 + 7) as u8).collect();
    let bytes = pattern.len();

    // SAFETY: plain allocation of `bytes`.
    let dev = unsafe { mgpu_dev_alloc(bytes) };
    assert!(!dev.is_null(), "mgpu_dev_alloc: {}", last_error());
    // SAFETY: both regions are valid for `bytes`.
    let up = unsafe { mgpu_htod(dev, pattern.as_ptr() as *const c_void, bytes) };

    let mut results = Vec::new();
    for fault in [0, 1] {
        // SAFETY: `dev` is a device region of `bytes`.
        let p = unsafe { mgpu_dtoh_private(dev, bytes, fault) };
        let mut out = vec![0u8; bytes];
        if !p.is_null() {
            // SAFETY: the private buffer holds `bytes`; `out` is valid
            // for them.
            unsafe { mgpu_host_copy(out.as_mut_ptr() as *mut c_void, p, bytes) };
        }
        results.push((fault, p.is_null(), out, last_error()));
    }

    // SAFETY: `dev` is freed once; `mgpu_stage_end` releases the
    // private read-back buffer of the calls above.
    let freed = unsafe { mgpu_dev_free(dev) };
    // SAFETY: no argument; the end of a request.
    let ended = unsafe { mgpu_stage_end() };

    assert_eq!(up, 0, "mgpu_htod");
    for (fault, null, out, err) in &results {
        assert!(
            !null,
            "mgpu_dtoh_private with fault argument {fault} failed without test-fault: {err}"
        );
        assert_eq!(out, &pattern, "read-back with fault argument {fault}");
    }
    assert_eq!(freed, 0, "mgpu_dev_free");
    assert_eq!(ended, 0, "mgpu_stage_end");
}
