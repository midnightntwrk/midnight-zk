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

//! Concurrency stress on the real device path through the
//! device-owner actor: N threads issue FFTs, MSMs and quotient-sized
//! workloads (large FFTs) of random sizes, with injected failures, an
//! unconfirmed drain and a teardown at a random point. Asserts every
//! call returned (watchdog), successful results equal the CPU
//! results, the pending-erasure report accounts for every block at
//! the end, `end_request` semantics hold, and no freed device buffer
//! was observed non-zero (check mode). The teardown state is sticky,
//! so the sequence runs in a child process. Without a device the
//! child takes its skip path, like the other device tests; the
//! reviewer runs it on a real device.
#![cfg(feature = "test-fault")]

use std::{
    sync::{Arc, Mutex, mpsc},
    time::Duration,
};

use ff::{Field, PrimeField};
use group::{Curve, Group};
use midnight_curves::{Fq, G1Affine, G1Projective, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

const CHILD: &str = "MGPU_ACTOR_DEVICE_STRESS_CHILD";
const SEEDS: [u64; 3] = [11, 0xA6705, 99_991];

fn root(k: u32) -> Fq {
    let mut w = Fq::ROOT_OF_UNITY;
    for _ in k..Fq::S {
        w = w.square();
    }
    w
}

fn values(n: usize, seed: u64) -> Vec<Fq> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    (0..n).map(|_| Fq::random(&mut rng)).collect()
}

struct Outcome {
    fft_ok: usize,
    fft_bad: usize,
    msm_ok: usize,
    msm_bad: usize,
    declines: usize,
}

#[test]
fn actor_device_stress() {
    if std::env::var_os(CHILD).is_none() {
        let exe = std::env::current_exe().expect("test binary path");
        let out = std::process::Command::new(exe)
            .args(["--exact", "actor_device_stress", "--nocapture"])
            .env(CHILD, "1")
            .output()
            .expect("run the child test process");
        assert!(
            out.status.success(),
            "child exited with {:?}\nstdout: {}\nstderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(!gpu::teardown::device_disabled());
        return;
    }
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    gpu::set_min_k(1);
    gpu::wipe::set_check(true);
    let leaks_before = gpu::wipe::pending_erasure();

    for (round, seed) in SEEDS.iter().enumerate() {
        let seed = *seed;
        gpu::begin_request();
        // Injected failures on the real fault points.
        gpu::fault::arm(gpu::fault::Class::Ntt, gpu::fault::Point::Readback, 2);
        gpu::fault::arm(gpu::fault::Class::Msm, gpu::fault::Point::Launch, 1);

        let outcomes = Arc::new(Mutex::new(Vec::new()));
        let mut threads = Vec::new();
        for t in 0..6u64 {
            let outcomes = outcomes.clone();
            threads.push(std::thread::spawn(move || {
                let mut o = Outcome {
                    fft_ok: 0,
                    fft_bad: 0,
                    msm_ok: 0,
                    msm_bad: 0,
                    declines: 0,
                };
                for i in 0..4u32 {
                    let k = 4 + ((seed + t + i as u64) % 6) as u32; // 2^4..2^9, and one quotient-sized below
                    let n = 1usize << k;
                    let a = values(n, seed ^ (t << 8) ^ i as u64);
                    let mut cpu = a.clone();
                    best_fft(&mut cpu, root(k), k);
                    let mut dev = a.clone();
                    if gpu::fft(adapter::scalars_mut(&mut dev), adapter::scalar(root(k)), k) {
                        if dev == cpu {
                            o.fft_ok += 1;
                        } else {
                            o.fft_bad += 1;
                        }
                    } else {
                        // A declined transform must leave its input intact.
                        if dev != a {
                            o.fft_bad += 1;
                        }
                        o.declines += 1;
                    }

                    let mut rng = ChaCha20Rng::seed_from_u64(seed + t);
                    let g = G1Projective::random(&mut rng);
                    let mut acc = g;
                    let p: Vec<G1Affine> = (0..64)
                        .map(|_| {
                            acc += g;
                            acc.to_affine()
                        })
                        .collect();
                    let s = values(64, seed + 1000 + t);
                    match gpu::msm_g1(adapter::scalars(&s), adapter::affine(&p)) {
                        Some(dev) => {
                            if adapter::from_jacobian(dev) == G1Affine::multi_exp_affine(&p, &s) {
                                o.msm_ok += 1;
                            } else {
                                o.msm_bad += 1;
                            }
                        }
                        None => o.declines += 1,
                    }
                }
                // One quotient-sized transform per thread.
                let k = 14;
                let a = values(1 << k, seed ^ 0xB16);
                let mut cpu = a.clone();
                best_fft(&mut cpu, root(k), k);
                let mut dev = a;
                if gpu::fft(adapter::scalars_mut(&mut dev), adapter::scalar(root(k)), k) {
                    if dev == cpu {
                        o.fft_ok += 1;
                    } else {
                        o.fft_bad += 1;
                    }
                } else {
                    o.declines += 1;
                }
                outcomes.lock().unwrap().push(o);
            }));
        }

        // Watchdog: every thread must return.
        let (done_tx, done_rx) = mpsc::channel();
        std::thread::spawn(move || {
            for t in threads {
                let _ = t.join();
            }
            let _ = done_tx.send(());
        });
        if round == SEEDS.len() - 1 {
            // Last round: an unconfirmed drain and the teardown land
            // while work is in flight. The drain is made to report
            // unconfirmed on the next failing call.
            gpu::fault::unconfirm_next_drains(1);
            gpu::fault::arm(gpu::fault::Class::Ntt, gpu::fault::Point::Launch, 4);
        }
        done_rx
            .recv_timeout(Duration::from_secs(120))
            .unwrap_or_else(|_| panic!("seed {seed}: a device call never returned (watchdog)"));
        let outcomes = outcomes.lock().unwrap();
        assert_eq!(outcomes.len(), 6, "seed {seed}: every thread reported");
        for o in outcomes.iter() {
            assert_eq!(
                o.fft_bad, 0,
                "seed {seed}: an FFT result differed from the CPU"
            );
            assert_eq!(
                o.msm_bad, 0,
                "seed {seed}: an MSM result differed from the CPU"
            );
        }
        drop(outcomes);
        gpu::fault::reset();

        if round < SEEDS.len() - 1 {
            // Between rounds the request ends cleanly and nothing is
            // left unerased.
            assert!(gpu::end_request(), "seed {seed}: end_request");
            let p = gpu::wipe::pending_erasure();
            assert!(p.clear(), "seed {seed}: pending erasure after end: {p:?}");
        }
    }

    // The teardown retires the device; every later call declines.
    assert!(gpu::teardown::teardown_context());
    assert!(gpu::teardown::device_disabled());
    let mut a = [gpu::field::one(); 16];
    assert!(!gpu::fft(&mut a, gpu::field::std_root(4).unwrap().0, 4));
    assert!(!gpu::end_request() || gpu::wipe::erasure_failures() == 0);

    // Every block is accounted for: clear, or counted lost at the
    // reset (the report carries the lost counts).
    let p = gpu::wipe::pending_erasure();
    assert_eq!(
        p.rust_blocks, 0,
        "rust blocks left: {p:?} (before: {leaks_before:?})"
    );
    assert_eq!(p.lib_unerased, 0, "library blocks left unerased: {p:?}");
    let stats = gpu::wipe::stats();
    assert_eq!(
        stats.device_nonzero, 0,
        "a freed buffer was observed non-zero in check mode: {stats:?}"
    );
    assert_eq!(stats.core[3], 0, "a core block checked non-zero: {stats:?}");
    eprintln!("actor device stress ok; pending at end: {p:?}");
}
