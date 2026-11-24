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

//! Every error exit of a device call that enqueued work waits for it before
//! it returns: copy, read-back, zeta, scale, periodic multiply (copy and
//! kernel) and the two MSM entry points. Each arm is failed once with a
//! spinning kernel still queued; the call must return an error, the stream
//! must be idle when it returns, and each drain is counted. Without the
//! drains the call returns while the kernel still runs.
#![cfg(feature = "test-fault")]

use midnight_gpu as gpu;

#[test]
fn every_error_arm_drains_its_stream() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let (run0, bad0) = gpu::error_drains();
    let arms = gpu::fault::error_arms().expect("the arms run");
    let (run1, bad1) = gpu::error_drains();
    for (arm, failed, idle) in &arms {
        eprintln!("{arm}: error {failed}, idle {idle}");
    }
    for (arm, failed, idle) in &arms {
        assert!(failed, "{arm}: the injected failure returns an error");
        assert!(idle, "{arm}: returned with work still queued");
    }
    assert!(
        run1 - run0 >= arms.len() as u64,
        "every arm counts its drain: {} for {} arms",
        run1 - run0,
        arms.len()
    );
    assert_eq!(bad1, bad0, "every drain confirmed");
}
