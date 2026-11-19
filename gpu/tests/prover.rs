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

//! midnight-proofs with these kernels installed as its hooks: the device
//! quotient against the stock quotient on random constraint systems, seeded
//! proofs byte for byte against the CPU, fault injection and the erasure
//! check. Every test passes with a message when there is no device or the
//! build is the stub.

use std::sync::{Mutex, Once, atomic::Ordering};

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks,
    test_switches::{self, QUOTIENT_CHECK, RandomCircuit},
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

/// The proof on the CPU (hooks suspended) and on the device, with the same
/// seeds, on a pool of a fixed thread count.
fn both(c: &RandomCircuit) -> ((Vec<u8>, bool), (Vec<u8>, bool)) {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(4).build().unwrap();
    pool.install(|| (test_switches::without_hooks(|| c.prove()), c.prove()))
}

/// The device quotient equals the stock quotient (the prover's check mode
/// compares every coefficient) on random constraint systems with gates, a
/// permutation, LogUp lookups and trash arguments.
/// Returns the node coverage: operations by kind (`OP_ADD ..= OP_MUL_ADD`),
/// then reads by column kind (fixed, advice, instance) and rotated reads.
fn fuzz(seeds: std::ops::Range<u64>, k: u32) -> [usize; 11] {
    QUOTIENT_CHECK.store(true, Ordering::Relaxed);
    let (diffs, declines) = (hooks::quotient_check_diffs(), hooks::quotient_declines());
    let checks = hooks::quotient_checks();
    let (runs, _) = gpu::quotient::quotient_counts();
    let n = seeds.end - seeds.start;
    let mut cover = [0usize; 11];
    for seed in seeds {
        let c = RandomCircuit::new(seed, false, k);
        let shape = c.shape().expect("the job takes every random system");
        for (c, v) in cover.iter_mut().zip(shape.op_kinds.iter().chain(&shape.read_kinds)) {
            *c += v;
        }
        let _ = c.prove();
        assert_eq!(
            hooks::quotient_check_diffs(),
            diffs,
            "seed {seed}: device quotient differs"
        );
        assert!(gpu::end_request());
    }
    QUOTIENT_CHECK.store(false, Ordering::Relaxed);
    assert_eq!(
        hooks::quotient_declines(),
        declines,
        "a job was declined before the hook"
    );
    assert_eq!(
        gpu::quotient::quotient_counts().0,
        runs + n,
        "every quotient ran on the device"
    );
    assert_eq!(
        hooks::quotient_checks(),
        checks + n,
        "every quotient was checked"
    );
    const NAMES: [&str; 11] = [
        "add", "sub", "mul", "square", "double", "negate", "mul_add", "fixed", "advice",
        "instance", "rotated",
    ];
    let line: Vec<String> = NAMES.iter().zip(&cover).map(|(n, c)| format!("{n}={c}")).collect();
    eprintln!("node coverage over {n} systems: {}", line.join(" "));
    cover
}

#[test]
fn quotient_fuzz_small() {
    let Some(_g) = setup() else {
        return;
    };
    fuzz(0..12, 6);
    fuzz(100..102, 9);
}

/// Every operation kind, every column kind and rotated reads appear in a
/// fuzz run of the default size.
#[test]
fn quotient_fuzz_covers_every_node() {
    let Some(_g) = setup() else {
        return;
    };
    let cover = fuzz(200..216, 6);
    assert!(
        cover.iter().all(|c| *c > 0),
        "a node kind was never generated: {cover:?}"
    );
}

/// The 10,000-system run (slow).
#[test]
#[ignore]
fn quotient_fuzz_10000() {
    let Some(_g) = setup() else {
        return;
    };
    let cover = fuzz(10_000..20_000, 6);
    assert!(
        cover.iter().all(|c| *c > 0),
        "a node kind was never generated: {cover:?}"
    );
}

#[test]
fn seeded_proofs_equal_cpu() {
    let Some(_g) = setup() else {
        return;
    };
    for (seed, k) in [(1, 7), (2, 10), (3, 12)] {
        let c = RandomCircuit::new(seed, true, k);
        let before = gpu::stats();
        let ((cpu, cpu_ok), (dev, dev_ok)) = both(&c);
        let after = gpu::stats();
        assert!(cpu_ok && dev_ok, "k={k}: proofs verify");
        assert_eq!(cpu, dev, "k={k}: proof bytes");
        assert!(
            after.quotient > before.quotient,
            "the quotient ran on the device"
        );
        assert!(after.msm > before.msm && after.ntt > before.ntt);
        assert!(gpu::end_request());
    }
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

#[test]
fn erasure_check_reads_zero() {
    let Some(_g) = setup() else {
        return;
    };
    gpu::wipe::set_check(true);
    let c = RandomCircuit::new(9, true, 8);
    let (_, ok) = c.prove();
    assert!(ok);
    assert!(gpu::end_request());
    let s = gpu::wipe::stats();
    gpu::wipe::set_check(false);
    assert!(s.device_checked > 0, "{s:?}");
    assert_eq!(s.device_nonzero, 0, "{s:?}");
    assert_eq!(s.core[3], 0, "{s:?}");
    assert_eq!(s.stage[3], 0, "{s:?}");
    assert!(s.host_vecs > 0, "the masked MSM scalars were zeroed");
    assert_eq!(s.erasure_failures, 0);
    assert_eq!(s.quarantined, 0);
}

/// Every armed fault gives a valid proof equal to the CPU proof (the caller
/// runs the CPU code on its unchanged input).
#[cfg(feature = "test-fault")]
#[test]
fn faults_give_valid_proofs() {
    use gpu::fault::{self, Class, Point};
    let Some(_g) = setup() else {
        return;
    };
    let c = RandomCircuit::new(11, true, 8);
    let (cpu, ok) = test_switches::without_hooks(|| c.prove());
    assert!(ok);
    let cases = [
        (Class::Msm, Point::Upload),
        (Class::Msm, Point::Launch),
        (Class::Ntt, Point::Upload),
        (Class::Ntt, Point::Launch),
        (Class::Ntt, Point::Readback),
        (Class::Quotient, Point::Upload),
        (Class::Quotient, Point::Launch),
        (Class::Quotient, Point::Divide),
        (Class::Quotient, Point::Readback),
    ];
    for (class, point) in cases {
        fault::reset();
        fault::arm(class, point, 3);
        let (dev, ok) = c.prove();
        assert!(ok, "{class:?}/{point:?}: the proof verifies");
        assert_eq!(dev, cpu, "{class:?}/{point:?}: proof bytes");
        assert!(fault::fired(class) > 0, "{class:?}/{point:?} fired");
        assert!(gpu::end_request());
    }
    fault::reset();
    assert!(gpu::end_request());
    assert!(gpu::declines().iter().any(|d| d.1 == "fault" || d.1 == "device-error"));

    // a corrupted quotient: the prover's check mode sees it and proves with
    // the stock values
    QUOTIENT_CHECK.store(true, Ordering::Relaxed);
    let diffs = hooks::quotient_check_diffs();
    fault::arm(Class::Quotient, Point::Corrupt, 1);
    let (dev, ok) = c.prove();
    QUOTIENT_CHECK.store(false, Ordering::Relaxed);
    fault::reset();
    assert!(ok);
    assert_eq!(dev, cpu);
    assert!(
        hooks::quotient_check_diffs() > diffs,
        "check mode sees the corruption"
    );
    assert!(gpu::end_request());
}

/// A fault in the in-place transform leaves the caller's buffer unchanged.
#[cfg(feature = "test-fault")]
#[test]
fn faulted_transform_leaves_input() {
    use gpu::fault::{self, Class, Point};
    let Some(_g) = setup() else {
        return;
    };
    let (w, _) = gpu::field::std_root(10).unwrap();
    let a: Vec<gpu::Scalar> = (0..1024u64).map(gpu::field::from_u64).collect();
    for point in [Point::Upload, Point::Launch, Point::Readback] {
        fault::reset();
        fault::arm(Class::Ntt, point, 1);
        let mut b = a.clone();
        assert!(!gpu::fft(&mut b, w, 10), "{point:?}");
        assert_eq!(a, b, "{point:?}: the input is unchanged");
    }
    fault::reset();
    assert!(gpu::end_request());
}
