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

//! Installing accelerator hooks (feature `gpu`). In its own test binary:
//! hooks are installed once per process.
#![cfg(feature = "gpu")]

use midnight_proofs::gpu::{self, GpuHooks, adapter::Scalar};

fn decline_fft(_: &mut [Scalar], _: Scalar, _: u32) -> bool {
    false
}

fn decline_ifft(_: &mut [Scalar], _: Scalar, _: u32, _: Scalar) -> bool {
    false
}

unsafe fn decline_quotient(job: *const std::ffi::c_void, _: &mut [Scalar]) -> bool {
    // SAFETY: the prover passes a valid job.
    let abi = unsafe { &*(job as *const gpu::abi::QuotientJobAbi) };
    assert_eq!(abi.abi, gpu::abi::QUOTIENT_ABI);
    false
}

/// Hooks that decline everything change no proof byte, and a second install
/// is rejected.
#[test]
fn install_once_and_decline() {
    #[cfg(feature = "gpu-test")]
    let before = {
        let c = gpu::test_switches::RandomCircuit::new(5, true, 6);
        let (proof, ok) = c.prove();
        assert!(ok);
        (c, proof)
    };
    assert!(gpu::hooks().is_none());
    let hooks = GpuHooks {
        msm_g1: Some(|_, _| None),
        fft: Some(decline_fft),
        ifft: Some(decline_ifft),
        quotient: Some(decline_quotient),
    };
    assert!(gpu::install(hooks));
    assert!(
        !gpu::install(GpuHooks::default()),
        "a second install is rejected"
    );
    assert!(
        gpu::hooks().unwrap().quotient.is_some(),
        "the first install stays"
    );
    #[cfg(feature = "gpu-test")]
    {
        let (c, proof) = before;
        gpu::reset_hook_declines();
        let declines = gpu::quotient_declines();
        let (again, ok) = c.prove();
        assert!(ok);
        assert_eq!(proof, again, "declining hooks change no byte");
        assert_eq!(
            gpu::quotient_declines(),
            declines,
            "the job reached the hook"
        );
        // Every decline is counted with its reason: here the hooks
        // themselves declined each call.
        let counts = gpu::hook_declines();
        let count = |class, reason| {
            counts.iter().find(|e| e.0 == class && e.1 == reason).map_or(0, |e| e.2)
        };
        // (a proof calls no forward base-domain FFT)
        for class in ["msm", "ifft", "quotient"] {
            assert!(count(class, "hook") > 0, "{class}: {counts:?}");
        }
        assert_eq!(count("quotient", "hook"), 1, "{counts:?}");
        assert!(
            counts.iter().all(|e| e.1 == "hook"),
            "no early decline on a BLS12-381 proof: {counts:?}"
        );

        gpu::test_switches::FORCE_QUOTIENT_DECLINE
            .store(true, std::sync::atomic::Ordering::Relaxed);
        let (forced, ok) = c.prove();
        gpu::test_switches::FORCE_QUOTIENT_DECLINE
            .store(false, std::sync::atomic::Ordering::Relaxed);
        assert!(ok);
        assert_eq!(proof, forced);
        let counts = gpu::hook_declines();
        assert!(counts.contains(&("quotient", "forced", 1)), "{counts:?}");
        assert_eq!(gpu::quotient_declines(), declines + 1);
    }
}
