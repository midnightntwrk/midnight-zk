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

//! Concurrent batch proving: CPU behaviour everywhere, and the device
//! MSM isolation at k >= 14 where a device is present. The device test
//! passes with a message when there is no device or the build is the
//! stub, like the other device tests.

use std::{
    sync::Mutex,
    time::{Duration, Instant},
};

use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks,
    batch::{BatchHooks, JobPanicked, prove_batch, prove_batch_with_rng, seeded_rng_factory},
    test_switches::{self, RandomCircuit},
};

/// Isolate process-wide test settings and bound the entire device operation,
/// including worker shutdown and the final request cleanup.
fn in_child(require_device: bool, body: impl FnOnce()) {
    let name = std::thread::current().name().unwrap().to_owned();
    const COMPLETE: i32 = 42;
    const NO_DEVICE: i32 = 77;
    if std::env::var("MIDNIGHT_BATCH_DEVICE_TEST").as_deref() == Ok(&name) {
        if require_device && !gpu::device() {
            eprintln!(
                "skipped: no device (CUDA core built: {})",
                gpu::cuda_built()
            );
            std::process::exit(NO_DEVICE);
        }
        body();
        std::process::exit(COMPLETE);
    }
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", &name, "--nocapture"])
        .env("MIDNIGHT_BATCH_DEVICE_TEST", &name)
        .env("RAYON_NUM_THREADS", "4")
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(600);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(
                status.code() == Some(COMPLETE)
                    || (require_device && status.code() == Some(NO_DEVICE)),
                "device test did not complete"
            );
            return;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            let reap = Instant::now() + Duration::from_secs(5);
            while child.try_wait().unwrap().is_none() {
                assert!(Instant::now() < reap, "device test child did not exit");
                std::thread::sleep(Duration::from_millis(10));
            }
            panic!("device test exceeded its deadline");
        }
        std::thread::sleep(Duration::from_millis(25));
    }
}

// Each fixture runs with the default blinding source on entry.
struct QuotientSeed;

impl QuotientSeed {
    fn set(seed: u64) -> Self {
        test_switches::set_quotient_blinding_seed(Some(seed));
        Self
    }
}

impl Drop for QuotientSeed {
    fn drop(&mut self) {
        test_switches::set_quotient_blinding_seed(None);
    }
}

#[test]
fn mixed_fixture_wave_matches_standalone_proofs() {
    static CIRCUITS: std::sync::OnceLock<[RandomCircuit; 2]> = std::sync::OnceLock::new();
    thread_local! {
        static NESTED: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    }
    // Suspend each job at its first instance transform. Run a proof with
    // the opposite shape on that same worker before resuming synthesis.
    fn interleave(_: &mut [gpu::Scalar], _: gpu::Scalar, _: u32, _: gpu::Scalar) -> bool {
        if let Some(i) = NESTED.take() {
            let (_, ok) = CIRCUITS.get().unwrap()[i].prove_with_rng(seeded_rng_factory(31)(i));
            assert_eq!(ok, i == 0);
        }
        false
    }
    static HOOKS: GpuHooks = GpuHooks {
        ifft: Some(interleave),
        fft: None,
        msm_g1: None,
        quotient: None,
    };
    in_child(false, || {
        let circuits = CIRCUITS.get_or_init(|| {
            [
                RandomCircuit::new(3, true, 6),
                RandomCircuit::new(5, false, 6),
            ]
        });
        let _seed = QuotientSeed::set(67);
        let prove = |i: usize, rng| circuits[i % 2].prove_with_rng(rng);
        for width in [1, 3] {
            let pool = rayon::ThreadPoolBuilder::new().num_threads(width).build().unwrap();
            pool.install(|| {
                let rng = seeded_rng_factory(89);
                let alone: Vec<_> = (0..4).map(|i| prove(i, rng(i))).collect();
                let waves = std::cell::Cell::new(0);
                let result = prove_batch_with_rng(
                    &[1; 4],
                    4,
                    4,
                    Some(&HOOKS),
                    rng,
                    |i, rng| {
                        NESTED.set(Some(1 - i % 2));
                        let proof = prove(i, rng);
                        assert!(NESTED.take().is_none(), "instance transform did not run");
                        proof
                    },
                    || {
                        waves.set(waves.get() + 1);
                        true
                    },
                )
                .unwrap();
                assert_eq!(waves.get(), 1);
                assert_eq!(result.jobs.len(), 4);
                for (i, (job, expected)) in result.jobs.into_iter().zip(alone).enumerate() {
                    let actual = job.expect("job completed");
                    assert_eq!(actual.1, i % 2 == 0);
                    assert!(actual == expected, "fixture proof differed from standalone");
                }
                assert!(!result.erasure_failed);
            });
        }
    });
}

/// A batch of seeded proofs on the CPU equals the proofs made alone,
/// and a panicking job neither stops the others nor skips the wave
/// boundary. Runs everywhere, device or not.
#[test]
fn cpu_batch_matches_alone_and_isolates_panics() {
    in_child(false, || {
        let circuits: Vec<RandomCircuit> = (0..3).map(|s| RandomCircuit::new(s, true, 6)).collect();
        let blinding = QuotientSeed::set(67);
        let alone: Vec<Vec<u8>> = circuits
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let (proof, ok) = c.prove_with_rng(seeded_rng_factory(89)(i));
                assert!(ok, "the proof made alone verifies");
                proof
            })
            .collect();
        let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD)
            .expect("device session admission");
        let results = prove_batch_with_rng(
            &[1, 1, 1, 1],
            2,
            2,
            None,
            seeded_rng_factory(89),
            |i, rng| {
                if i == 3 {
                    panic!("job failure");
                }
                circuits[i].prove_with_rng(rng)
            },
            || session.end_wave(),
        )
        .unwrap();
        assert!(session.finish() && !results.erasure_failed);
        let results = results.jobs;
        for (i, r) in results.iter().enumerate().take(3) {
            let (proof, ok) = r.as_ref().expect("job ran");
            assert!(*ok, "batch proof {i} verifies");
            assert!(
                proof == &alone[i],
                "batch proof {i} differs from the proof made alone"
            );
        }
        assert!(
            matches!(results[3], Err(JobPanicked)),
            "the panicking job is reported alone"
        );
        // Move the fixture into an unwind while keeping the caller RNG fixed.
        assert!(
            std::panic::catch_unwind(move || {
                let _blinding = blinding;
                panic!("end seeded fixture");
            })
            .is_err()
        );
        let (fresh, ok) = circuits[0].prove_with_rng(seeded_rng_factory(89)(0));
        assert!(
            ok && fresh != alone[0],
            "quotient blinding source was not restored"
        );
    });
}

/// (Registered base address, job index).
static JOB_BASES: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());
static MSM_SEQ: Mutex<Vec<usize>> = Mutex::new(Vec::new());

fn observed_msm(
    scalars: &[gpu::Scalar],
    bases: &[gpu::G1AffineLimbs],
) -> Option<gpu::G1JacobianLimbs> {
    // Serialize sampling with the call so another job cannot take credit
    // for its hit, upload, or checked release.
    let mut seq = MSM_SEQ.lock().unwrap();
    let job = JOB_BASES
        .lock()
        .unwrap()
        .iter()
        .find(|(ptr, _)| *ptr == bases.as_ptr() as usize)
        .map(|(_, job)| *job);
    let (cached, _, uploads) = gpu::msm::msm_counts();
    let (calls, evictions, _) = gpu::batch::batch_msm_counts();
    let checked = gpu::wipe::stats().core[2];
    let result = gpu::batch::isolated_msm_g1(scalars, bases)?;
    if let Some(job) = job {
        let (after_cached, _, after_uploads) = gpu::msm::msm_counts();
        let (after_calls, after_evictions, _) = gpu::batch::batch_msm_counts();
        assert_eq!(after_cached, cached + 1);
        assert_eq!(after_uploads, uploads + 1);
        assert_eq!(after_calls, calls + 1);
        assert_eq!(after_evictions, evictions + 1);
        assert!(
            gpu::wipe::stats().core[2] > checked,
            "registered context was checked before return"
        );
        seq.push(job);
        let first = seq.len() == 1;
        drop(seq);
        if first {
            let deadline = Instant::now() + Duration::from_secs(120);
            while !MSM_SEQ.lock().unwrap().iter().any(|&other| other != job) {
                assert!(
                    Instant::now() < deadline,
                    "second proof missed its MSM deadline"
                );
                rayon::yield_now();
            }
        }
    }
    Some(result)
}

static OBSERVED_HOOKS: GpuHooks = GpuHooks {
    msm_g1: Some(observed_msm),
    fft: Some(gpu::batch::batch_fft),
    ifft: Some(gpu::batch::batch_ifft),
    quotient: Some(gpu::batch::batch_quotient),
};

#[test]
fn displaced_key_copies_wait_for_final_boundary() {
    in_child(true, || {
        gpu::set_min_k(1);
        gpu::quotient::set_keep_resident(true);
        let circuit = RandomCircuit::new(11, true, 8);
        let polys = circuit.pk().gpu_resident_polys().expect("quotient shape");
        let first = hooks::adapter::scalars(polys[0]);
        let second = hooks::adapter::scalars(polys[1]);
        let a = gpu::register_key(&[first]);
        let b = gpu::register_key(&[second]);
        let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD).unwrap();
        static HOOKS: GpuHooks = GpuHooks {
            quotient: Some(gpu::batch::batch_quotient),
            msm_g1: None,
            fft: None,
            ifft: None,
        };
        let before = gpu::stats().quotient;
        let result = prove_batch(
            &[1],
            1,
            1,
            BatchHooks::new(Some(&HOOKS), &|on| session.set_worker(on)),
            |_, rng| circuit.prove_with_rng(rng).1,
            || session.end_wave(),
        )
        .unwrap();
        assert!(matches!(result.jobs[..], [Ok(true)]));
        assert!(!result.erasure_failed);
        assert_eq!(gpu::stats().quotient, before + 1);
        let live = gpu::device_bytes().0;
        let bytes = (std::mem::size_of_val(first) + std::mem::size_of_val(second)) as u64;
        let replaced = gpu::register_key(&[first]);
        drop((a, b));
        assert_eq!(gpu::device_bytes().0, live);
        assert!(session.end_wave());
        assert_eq!(gpu::batch::deferred_releases(), 0);
        assert!(session.finish());
        assert_eq!(gpu::batch::deferred_releases(), 2);
        assert_eq!(live - gpu::device_bytes().0, bytes);
        drop(replaced);
    });
}

/// At k >= 14, in ONE batch wave: both proofs hit live registered SRS
/// tables on the device, their MSMs alternate, and between consecutive
/// MSMs of different jobs a live context was evicted and its erasure
/// checked (zero-content check on). The only skip is the explicit
/// no-device return at the top.
#[test]
fn device_batch_evicts_msm_contexts_between_proofs() {
    use midnight_proofs::poly::{
        Coeff, LagrangeCoeff, LagrangeDeltaCoeff, LagrangeDoubleDeltaCoeff,
    };
    in_child(true, || {
        gpu::set_min_k(14);
        gpu::wipe::set_check(true);
        let circuits: Vec<RandomCircuit> =
            (20..22).map(|s| RandomCircuit::new(s, true, 14)).collect();
        // Register every SRS basis slice of each circuit, so the batch MSMs
        // hit live registered contexts. The handles live until the end.
        let mut handles = Vec::new();
        {
            let mut job_bases = JOB_BASES.lock().unwrap_or_else(|e| e.into_inner());
            job_bases.clear();
            for (job, c) in circuits.iter().enumerate() {
                let params = c.params();
                for bases in [
                    params.bases::<Coeff>(),
                    params.bases::<LagrangeCoeff>(),
                    params.bases::<LagrangeDeltaCoeff>(),
                    params.bases::<LagrangeDoubleDeltaCoeff>(),
                ] {
                    job_bases.push((bases.as_ptr() as usize, job));
                    handles.push(gpu::register_srs(hooks::adapter::affine(bases)));
                }
            }
        }
        let weights: Vec<u64> = circuits
            .iter()
            .map(|c| {
                let s = c.shape().expect("the job takes the random circuit");
                gpu::quotient::need_bytes(s.ext_k, s.proof_polys, s.key_polys, s.nslots) as u64
            })
            .collect();
        let budget: u64 = weights.iter().sum();
        let waves = std::cell::Cell::new(0);
        let _blinding = QuotientSeed::set(67);
        let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD)
            .expect("device session admission");
        let results = prove_batch_with_rng(
            &weights,
            budget,
            2,
            BatchHooks::new(Some(&OBSERVED_HOOKS), &|on| session.set_worker(on)),
            seeded_rng_factory(89),
            |i, rng| circuits[i].prove_with_rng(rng),
            || {
                waves.set(waves.get() + 1);
                session.end_wave()
            },
        )
        .unwrap();
        assert!(session.finish() && !results.erasure_failed);
        assert_eq!(waves.get(), 1);
        let results = results.jobs;
        for (i, r) in results.iter().enumerate() {
            let (proof, ok) = r.as_ref().expect("job ran");
            assert!(*ok, "batch proof {i} verifies");
            assert!(!proof.is_empty());
            let (alone, alone_ok) = circuits[i].prove_with_rng(seeded_rng_factory(89)(i));
            assert!(alone_ok);
            assert!(
                proof == &alone,
                "device batch proof {i} differs from the CPU proof made alone"
            );
        }
        let seq = MSM_SEQ.lock().unwrap();
        assert!(seq.len() >= 4);
        let interior = &seq[1..seq.len() - 1];
        assert!(interior.contains(&0) && interior.contains(&1));
        assert!(
            seq.windows(2).filter(|p| p[0] != p[1]).count() >= 2,
            "registered MSMs alternated between proofs"
        );
        let w = gpu::wipe::stats();
        assert_eq!(w.erasure_failures, 0, "no erasure failed");
        assert_eq!(w.device_nonzero, 0, "no checked region was non-zero");
        assert_eq!(w.check_failures, 0, "no erasure check call failed");
        assert_eq!(w.core[3], 0, "no checked core block was non-zero");
        assert!(
            !gpu::batch::batch_erasure_failed(),
            "the batch erasure check passed throughout"
        );
        drop(handles);
    });
}

#[test]
fn smaller_transform_checks_the_entire_allocation_per_call() {
    in_child(true, || {
        gpu::set_min_k(8);
        gpu::wipe::set_check(true);
        let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD)
            .expect("device session admission");
        let filled = std::sync::atomic::AtomicBool::new(false);
        let waves = std::cell::Cell::new(0);
        let result = prove_batch(
            &[1, 1],
            2,
            2,
            BatchHooks::new(Some(&OBSERVED_HOOKS), &|on| session.set_worker(on)),
            |job, _| {
                use std::sync::atomic::Ordering;
                // An impulse fills every output slot with the same pattern.
                let (k, value) = if job == 0 { (19, 37) } else { (8, 19) };
                if job == 1 {
                    let deadline = Instant::now() + Duration::from_secs(120);
                    while !filled.load(Ordering::Acquire) {
                        assert!(Instant::now() < deadline, "first transform timed out");
                        rayon::yield_now();
                    }
                }
                let mut data = vec![gpu::field::ZERO; 1 << k];
                let expected = gpu::field::from_u64(value);
                data[0] = expected;
                let hooks = hooks::hooks().unwrap();
                let (root, inverse) = gpu::field::std_root(k).unwrap();
                let before = gpu::wipe::stats();
                if job == 0 {
                    assert!(hooks.fft.unwrap()(&mut data, root, k));
                } else {
                    assert!(hooks.ifft.unwrap()(
                        &mut data,
                        inverse,
                        k,
                        gpu::field::one()
                    ));
                }
                assert!(
                    data.iter().all(|v| *v == expected),
                    "incorrect transform result"
                );
                let after = gpu::wipe::stats();
                assert_eq!(after.device_checked, before.device_checked + 1);
                assert_eq!(after.device_bytes - before.device_bytes, (32 << k) as u64);
                assert!(after.stage[2] > before.stage[2]);
                assert!(after.stage[1] - before.stage[1] >= (32 << k) as u64);
                assert_eq!(gpu::xfer::stats().stage[7], 0);
                assert_eq!(after.device_nonzero, 0);
                assert_eq!(after.stage[3], 0);
                filled.store(true, Ordering::Release);
            },
            || {
                waves.set(waves.get() + 1);
                session.end_wave()
            },
        )
        .unwrap();
        assert!(matches!(result.jobs[..], [Ok(()), Ok(())]));
        assert!(!result.erasure_failed);
        assert_eq!(waves.get(), 1);
        assert!(session.finish());
    });
}

#[cfg(feature = "test-fault")]
#[test]
fn failed_call_erasure_declines_the_next_transform() {
    in_child(true, || {
        gpu::set_min_k(8);
        gpu::wipe::set_check(true);
        let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD)
            .expect("device session admission");
        let result = prove_batch(
            &[1],
            1,
            1,
            BatchHooks::new(Some(&OBSERVED_HOOKS), &|on| session.set_worker(on)),
            |_, _| {
                let mut data = vec![gpu::field::one(); 256];
                let root = gpu::field::std_root(8).unwrap().0;
                let before = gpu::wipe::stats();
                gpu::fault::arm(gpu::fault::Class::Erase, gpu::fault::Point::Check, 1);
                assert!(gpu::batch::batch_fft(&mut data, root, 8));
                assert!(gpu::batch::batch_erasure_failed());
                assert_eq!(gpu::wipe::stats().check_failures, before.check_failures + 1);
                assert!(!gpu::batch::batch_fft(&mut data, root, 8));
            },
            || session.end_wave(),
        )
        .unwrap();
        assert!(matches!(result.jobs[..], [Ok(())]));
        assert!(result.erasure_failed);
        assert!(!session.finish());
    });
}

#[cfg(feature = "test-fault")]
#[test]
fn quotient_readback_is_erased_on_success_and_decline() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    unsafe fn observe(job: *const std::ffi::c_void, out: &mut [gpu::Scalar]) -> bool {
        let first = CALLS.fetch_add(1, Ordering::Relaxed) == 0;
        if !first {
            gpu::fault::arm(gpu::fault::Class::Quotient, gpu::fault::Point::Readback, 1);
        }
        let before = gpu::wipe::stats();
        // SAFETY: the prover owns the job and output for the duration of the hook.
        let taken = unsafe { gpu::batch::batch_quotient(job, out) };
        assert_eq!(taken, first);
        let after = gpu::wipe::stats();
        assert!(after.stage[2] > before.stage[2]);
        assert_eq!(after.stage[3], 0);
        taken
    }
    static HOOKS: GpuHooks = GpuHooks {
        msm_g1: None,
        fft: None,
        ifft: None,
        quotient: Some(observe),
    };
    in_child(true, || {
        gpu::set_min_k(1);
        gpu::wipe::set_check(true);
        let circuit = RandomCircuit::new(11, true, 8);
        let session = gpu::batch::BatchSession::begin(&hooks::batch::BATCH_THREAD)
            .expect("device session admission");
        let result = prove_batch(
            &[1, 1],
            1,
            1,
            BatchHooks::new(Some(&HOOKS), &|on| session.set_worker(on)),
            |_, rng| circuit.prove_with_rng(rng).1,
            || session.end_wave(),
        )
        .unwrap();
        assert!(matches!(result.jobs[..], [Ok(true), Ok(true)]));
        assert_eq!(CALLS.load(Ordering::Relaxed), 2);
        assert_eq!(gpu::fault::fired(gpu::fault::Class::Quotient), 1);
        assert!(!result.erasure_failed && session.finish());
    });
}
