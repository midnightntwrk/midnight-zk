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

//! `quotient::need_bytes` is the arithmetic of the job's memory check: with
//! `MIDNIGHT_GPU_MAX_BYTES` one byte below it the job declines (`memory`)
//! and the proof is unchanged; at it the job runs on the device. In its own
//! test binary (it sets the environment).

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks,
    test_switches::{self, RandomCircuit},
};

#[test]
fn need_bytes_is_the_memory_check() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let info = gpu::present().unwrap();
    assert!(info.runtime_version >= 11000, "{info:?}");
    assert!(
        info.driver_version >= info.runtime_version / 1000 * 1000,
        "{info:?}"
    );
    gpu::set_min_k(1);
    assert!(hooks::install(GpuHooks {
        quotient: Some(gpu::quotient),
        ..GpuHooks::default()
    }));
    let c = RandomCircuit::new(5, true, 8);
    let s = c.shape().expect("the job takes the random system");
    assert_eq!(
        hooks::quotient_shape(c.pk()),
        Some(s.clone()),
        "pk() is the key"
    );
    let need = gpu::quotient::need_bytes(s.ext_k, s.proof_polys, s.key_polys, s.nslots);
    let (cpu, ok) = test_switches::without_hooks(|| c.prove());
    assert!(ok);

    let run = |limit: usize| {
        // SAFETY: the only test of this binary; no other thread reads the
        // environment.
        unsafe { std::env::set_var("MIDNIGHT_GPU_MAX_BYTES", limit.to_string()) };
        let before = gpu::quotient::quotient_counts().0;
        let (dev, ok) = c.prove();
        assert!(ok && dev == cpu, "the proof is unchanged");
        assert!(gpu::end_request());
        gpu::quotient::quotient_counts().0 > before
    };
    let memory = || gpu::declines().iter().filter(|d| d.1 == "memory").map(|d| d.2).sum::<u64>();
    let m0 = memory();
    assert!(!run(need - 1), "one byte short: declined");
    assert_eq!(memory(), m0 + 1, "with reason memory");
    assert!(run(need), "exactly enough: runs on the device");
}
