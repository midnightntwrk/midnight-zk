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

//! A test switch in a build without the test feature is refused: with
//! `MIDNIGHT_GPU_FAULT` set and no feature `test-fault`, the device is not
//! used. In its own test binary (the decision is made once per process).
#![cfg(not(feature = "test-fault"))]

use midnight_gpu as gpu;

#[test]
fn fault_switch_refused_without_test_feature() {
    // SAFETY: the only test of this binary; nothing reads the environment
    // concurrently.
    unsafe { std::env::set_var("MIDNIGHT_GPU_FAULT", "msm:launch") };
    assert_eq!(gpu::device_count(), 0);
    assert!(gpu::present().is_none());
    assert!(!gpu::device());
    let mut a = vec![[0u64; 4]; 1 << 4];
    assert!(
        !gpu::fft(&mut a, gpu::field::one(), 4),
        "every call declines"
    );
}
