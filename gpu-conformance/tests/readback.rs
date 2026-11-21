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

//! GPU-038: what the device reads back during a proof, checked against the
//! data-movement policy of the Lean oracle (`datamove.json` in the golden
//! vectors). Passes with a message when there is no device or the build is
//! the stub, unless MIDNIGHT_GPU_REQUIRE_CUDA=1.

use std::sync::{Mutex, Once, atomic::Ordering};

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks,
    test_switches::{self, RandomCircuit},
};

#[path = "oracle/datamove.rs"]
mod datamove;

/// The tests share process-wide switches: one at a time.
static SERIAL: Mutex<()> = Mutex::new(());

fn setup() -> Option<std::sync::MutexGuard<'static, ()>> {
    static INSTALL: Once = Once::new();
    let g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return None;
    }
    gpu::set_min_k(1);
    INSTALL.call_once(|| {
        assert!(hooks::install(GpuHooks {
            msm_g1: Some(gpu::msm_g1),
            fft: Some(gpu::fft),
            ifft: Some(gpu::ifft),
            quotient: Some(gpu::quotient),
        }));
    });
    Some(g)
}

/// GPU-038 on two requests: a device quotient and an explicit CPU quotient
/// with device MSM, base transforms and wipe checking still enabled.
#[test]
fn readback_is_base_transforms_and_quotient() {
    use gpu::xfer;

    let permitted = datamove::permitted();
    let Some(_g) = setup() else {
        assert_ne!(
            std::env::var("MIDNIGHT_GPU_REQUIRE_CUDA").as_deref(),
            Ok("1"),
            "GPU-038 requires a usable CUDA device"
        );
        return;
    };
    let c = test_switches::without_hooks(|| RandomCircuit::new(4, true, 10));
    let shape = c.shape().unwrap();
    let field_bytes = size_of::<gpu::Scalar>();
    let base_bytes = (1usize << shape.k) * field_bytes;
    let extended_bytes = (1usize << shape.ext_k) * field_bytes;
    assert!(base_bytes < extended_bytes && shape.len * field_bytes < extended_bytes);
    for cpu_quotient in [false, true] {
        gpu::wipe::set_check(cpu_quotient);
        xfer::take_d2h_log();
        let before = xfer::stats();
        let runs_before = gpu::stats();
        let declines_before = hooks::quotient_declines();
        test_switches::FORCE_QUOTIENT_DECLINE.store(cpu_quotient, Ordering::Relaxed);
        xfer::record_d2h(true);
        let (_, verified) = c.prove();
        let cleanup = gpu::end_request_report();
        xfer::record_d2h(false);
        test_switches::FORCE_QUOTIENT_DECLINE.store(false, Ordering::Relaxed);
        gpu::wipe::set_check(false);

        let trace = xfer::take_d2h_log();
        let after = xfer::stats();
        let runs = gpu::stats();
        let msm_rows = after.msm_d2h_copies - before.msm_d2h_copies;
        let msm_bytes = after.msm_d2h_bytes - before.msm_d2h_bytes;
        let extended = trace.iter().filter(|&&bytes| bytes == extended_bytes).count();
        let result_bytes = after.d2h_bytes - before.d2h_bytes;
        let result_copies = after.d2h_copies - before.d2h_copies;
        eprintln!(
            "GPU-038 cpu_quotient={cpu_quotient} result_copies={result_copies} result_bytes={result_bytes} msm_bucket_copies={msm_rows} msm_bucket_bytes={msm_bytes} extended_copies={extended} trace={trace:?}"
        );
        assert!(verified);
        let wipe = cleanup.expect("confirmed request cleanup");
        assert!(runs.msm > runs_before.msm && runs.ntt > runs_before.ntt);
        assert_eq!(runs.device_errors, runs_before.device_errors);
        assert_eq!(
            runs.quotient - runs_before.quotient,
            u64::from(!cpu_quotient)
        );
        assert_eq!(
            hooks::quotient_declines() - declines_before,
            u64::from(cpu_quotient)
        );

        assert_eq!(extended, 0, "extended-domain payload in result log");
        assert_eq!(result_copies, trace.len() as u64);
        assert_eq!(result_bytes, trace.iter().map(|&n| n as u64).sum::<u64>());
        assert!(msm_rows > 0 && msm_bytes > 0 && msm_rows.is_multiple_of(2));
        let check_kind = |name| {
            if let Some(allowed) = &permitted {
                assert!(
                    allowed.contains_key(name),
                    "oracle forbids observed kind {name}"
                );
            }
        };
        check_kind("msm-buckets");
        if cpu_quotient {
            assert!(wipe.device_checked > 0);
            check_kind("counter");
        }
        let mut transforms = 0;
        let mut quotients = 0;
        let quotient_bytes = shape.len * field_bytes;
        assert_ne!(
            base_bytes, quotient_bytes,
            "distinguish result types by size"
        );
        for bytes in trace {
            if bytes == base_bytes {
                check_kind("base-transform");
                transforms += 1;
            } else {
                assert_eq!(bytes, quotient_bytes, "unexpected result copy size");
                check_kind("quotient-coeffs");
                quotients += 1;
            }
        }
        assert_eq!(transforms, runs.ntt - runs_before.ntt);
        assert_eq!(quotients, runs.quotient - runs_before.quotient);
    }
}
