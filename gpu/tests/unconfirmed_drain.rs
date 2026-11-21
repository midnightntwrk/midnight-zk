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

//! After a drain that could not be confirmed (a transfer may still target a
//! host buffer), the CUDA core's own host buffers are kept as they are: the
//! bounce buffer is not handed out again (the copy takes the direct path) and
//! is neither wiped nor freed, and the read-back buffer is neither wiped nor
//! freed. Each held buffer counts as an erasure failure. One driver call sets
//! the state up; each test checks one path. In its own test binary: the held
//! buffers stay for the rest of the process.
#![cfg(feature = "test-fault")]

use std::sync::OnceLock;

use midnight_gpu as gpu;

fn paths() -> Option<[u64; 3]> {
    static P: OnceLock<Option<[u64; 3]>> = OnceLock::new();
    *P.get_or_init(|| {
        if !gpu::device() {
            eprintln!(
                "skipped: no device (CUDA core built: {})",
                gpu::cuda_built()
            );
            return None;
        }
        let p = gpu::fault::stage_paths_after_unconfirmed_drain().expect("the driver runs");
        eprintln!(
            "stage_get refuses {}, stage_free keeps {}, rb_free keeps {}",
            p[0], p[1], p[2]
        );
        Some(p)
    })
}

#[test]
fn stage_get_refuses_after_unconfirmed_drain() {
    let Some(p) = paths() else { return };
    assert_ne!(p[0], 2, "this device does not stage copies");
    assert_eq!(p[0], 1, "the bounce buffer was handed out again");
}

#[test]
fn stage_free_keeps_after_unconfirmed_drain() {
    let Some(p) = paths() else { return };
    assert_ne!(p[1], 2, "this device does not stage copies");
    assert_eq!(p[1], 1, "the bounce buffer was wiped or freed");
}

#[test]
fn rb_free_keeps_after_unconfirmed_drain() {
    let Some(p) = paths() else { return };
    assert_eq!(p[2], 1, "the read-back buffer was wiped or freed");
}
