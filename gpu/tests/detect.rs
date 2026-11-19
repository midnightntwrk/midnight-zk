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

//! Device detection makes no CUDA context. In its own test binary: the
//! first device call of the process makes the context.

use midnight_gpu as gpu;

#[test]
fn detection_makes_no_context() {
    let n = gpu::device_count();
    let present = gpu::present().is_some();
    if n == 0 || !present {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let Some(active) = gpu::context_active() else {
        eprintln!("skipped: the driver does not report the primary context state");
        return;
    };
    assert!(!active, "device_count() and present() made no CUDA context");
    assert!(gpu::device());
    assert_eq!(gpu::context_active(), Some(true), "device() makes it");
}
