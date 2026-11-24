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

//! Kernel harness: every device kernel against the CPU function the prover
//! calls, at sizes `2^14 ..= 2^21`, and the MSM time for skewed scalar
//! vectors against uniform ones. Writes one TSV row per measurement and
//! exits non-zero when a result differs from the CPU or a skewed MSM takes
//! more than 1.5 times the uniform one.
//!
//! Usage: `cargo run --release --example kernels --features cuda -- [OUT.tsv]`
//! (default `kernels.tsv`). `MIDNIGHT_GPU_HARNESS_MAX_K` lowers the top size
//! (default 21). Run it alone on the device.

use std::{io::Write, sync::atomic::Ordering, time::Instant};

use ff::{Field, PrimeField};
use group::{Curve, Group, prime::PrimeCurveAffine};
use midnight_curves::{Fq, G1Affine, G1Projective, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::gpu::{
    self as hooks, GpuHooks, adapter,
    test_switches::{self, QUOTIENT_CHECK, RandomCircuit},
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

fn med(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

/// The fastest of `runs` timings: the MSM ratio check compares cases, and on
/// a shared device the fastest run is the one least disturbed by other work.
fn time_min<R>(mut f: impl FnMut() -> R, runs: usize) -> (R, f64) {
    let mut best = f64::INFINITY;
    let mut last = None;
    for _ in 0..runs {
        let t = Instant::now();
        last = Some(f());
        best = best.min(t.elapsed().as_secs_f64());
    }
    (last.unwrap(), best)
}

fn time<R>(f: impl FnMut() -> R, runs: usize) -> (R, f64) {
    let mut f = f;
    let mut ts = Vec::with_capacity(runs);
    let mut last = None;
    for _ in 0..runs {
        let t = Instant::now();
        last = Some(f());
        ts.push(t.elapsed().as_secs_f64());
    }
    (last.unwrap(), med(ts))
}

fn root(k: u32) -> Fq {
    let mut w = Fq::ROOT_OF_UNITY;
    for _ in k..Fq::S {
        w = w.square();
    }
    w
}

fn main() {
    let out = std::env::args().nth(1).unwrap_or_else(|| "kernels.tsv".into());
    let max_k: u32 = std::env::var("MIDNIGHT_GPU_HARNESS_MAX_K")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(21)
        .clamp(14, 21);
    if !gpu::device() {
        eprintln!(
            "no device (CUDA core built: {}): nothing measured",
            gpu::cuda_built()
        );
        return;
    }
    let info = gpu::present().unwrap();
    let mut tsv = std::fs::File::create(&out).expect("output file");
    // skew_ratio: an MSM case's device time over the uniform case's at the
    // same size (both the fastest of 7 warm runs); empty for other kernels
    writeln!(
        tsv,
        "device\tkernel\tlog_n\tcase\tgpu_s\tcpu_s\tequal\tskew_ratio"
    )
    .unwrap();
    let failed = std::cell::RefCell::new(Vec::<String>::new());
    // the largest skew ratio of each MSM case, and its size
    let skew = std::cell::RefCell::new(Vec::<(String, f64, u32)>::new());
    let mut row =
        |kernel: &str, k: u32, case: &str, g: f64, c: f64, eq: bool, ratio: Option<f64>| {
            let r = ratio.map_or(String::new(), |r| format!("{r:.3}"));
            writeln!(
                tsv,
                "{}\t{kernel}\t{k}\t{case}\t{g:.6}\t{c:.6}\t{eq}\t{r}",
                info.name
            )
            .unwrap();
            eprintln!("{kernel} 2^{k} {case}: gpu {g:.4}s cpu {c:.4}s equal {eq} skew {r}");
            if !eq {
                failed.borrow_mut().push(format!("{kernel} 2^{k} {case}: differs from the CPU"));
            }
        };
    gpu::set_min_k(1);
    let mut r = ChaCha20Rng::seed_from_u64(42);

    // transforms
    for k in 14..=max_k {
        let n = 1usize << k;
        let v: Vec<Fq> = (0..n).map(|_| Fq::random(&mut r)).collect();
        let w = root(k);
        let (cpu, cs) = time(
            || {
                let mut x = v.clone();
                best_fft(&mut x, w, k);
                x
            },
            3,
        );
        let (dev, gs) = time(
            || {
                let mut x = v.clone();
                let ok = gpu::fft(adapter::scalars_mut(&mut x), adapter::scalar(w), k);
                (ok, x)
            },
            5,
        );
        row("fft", k, "random", gs, cs, dev.0 && dev.1 == cpu, None);
        let wi = w.invert().unwrap();
        let ninv = Fq::from(n as u64).invert().unwrap();
        let (cpu, cs) = time(
            || {
                let mut x = v.clone();
                best_fft(&mut x, wi, k);
                x.iter_mut().for_each(|a| *a *= ninv);
                x
            },
            3,
        );
        let (dev, gs) = time(
            || {
                let mut x = v.clone();
                let ok = gpu::ifft(
                    adapter::scalars_mut(&mut x),
                    adapter::scalar(wi),
                    k,
                    adapter::scalar(ninv),
                );
                (ok, x)
            },
            5,
        );
        row("ifft", k, "random", gs, cs, dev.0 && dev.1 == cpu, None);
    }

    // MSM on a registered table, with the skew cases at every size
    let nmax = 1usize << max_k;
    let step = G1Projective::random(&mut r);
    let mut proj = Vec::with_capacity(nmax);
    let mut acc = G1Projective::random(&mut r);
    for _ in 0..nmax {
        proj.push(acc);
        acc += step;
    }
    let mut bases = vec![G1Affine::identity(); nmax];
    G1Projective::batch_normalize(&proj, &mut bases);
    drop(proj);
    let limbs = adapter::affine(&bases);
    let h = gpu::register_srs(limbs);
    for k in 14..=max_k {
        let n = 1usize << k;
        let b = &bases[..n];
        let mut cases: Vec<(&str, Vec<Fq>)> = vec![
            ("uniform", (0..n).map(|_| Fq::random(&mut r)).collect()),
            ("repeated", vec![Fq::random(&mut r); n]),
            (
                "zero90",
                (0..n)
                    .map(|i| {
                        if i % 10 == 0 {
                            Fq::random(&mut r)
                        } else {
                            Fq::ZERO
                        }
                    })
                    .collect(),
            ),
            (
                "small16",
                (0..n).map(|i| Fq::from((i as u64 * 7919) % 65536)).collect(),
            ),
        ];
        let mut uniform = 0.0;
        for (case, s) in cases.drain(..) {
            let (want, cs) = time(
                || G1Affine::multi_exp_affine(b, &s),
                if k < 19 { 3 } else { 1 },
            );
            // the first call computes the mask MSM of the length; time the warm ones
            let _ = gpu::msm_g1(adapter::scalars(&s), &limbs[..n]);
            let (got, gs) = time_min(|| gpu::msm_g1(adapter::scalars(&s), &limbs[..n]), 7);
            let eq = got.is_some_and(|g| adapter::from_jacobian(g).to_affine() == want.to_affine());
            if case == "uniform" {
                uniform = gs;
            }
            let ratio = gs / uniform;
            row("msm", k, case, gs, cs, eq, Some(ratio));
            {
                let mut sk = skew.borrow_mut();
                match sk.iter_mut().find(|e| e.0 == case) {
                    Some(e) if ratio > e.1 => (e.1, e.2) = (ratio, k),
                    Some(_) => {}
                    None => sk.push((case.to_string(), ratio, k)),
                }
            }
            if case != "uniform" && gs > 1.5 * uniform {
                failed.borrow_mut().push(format!(
                    "msm 2^{k} {case}: {gs:.4}s is more than 1.5 x uniform {uniform:.4}s"
                ));
            }
        }
    }
    drop(h);

    // the quotient: random constraint systems whose extended domain spans
    // 2^14 ..= 2^max_k, the device job against the stock quotient (check mode)
    if !hooks::install(GpuHooks {
        msm_g1: Some(gpu::msm_g1),
        fft: Some(gpu::fft),
        ifft: Some(gpu::ifft),
        quotient: Some(gpu::quotient),
    }) {
        failed.borrow_mut().push("hooks were installed already".into());
    }
    let mut seen = std::collections::BTreeSet::new();
    for k in 8..=max_k {
        let c = RandomCircuit::new(1000 + k as u64, true, k);
        let Some(shape) = c.shape() else { continue };
        if shape.ext_k < 14 || shape.ext_k > max_k || !seen.insert(shape.ext_k) {
            if shape.ext_k > max_k {
                break;
            }
            continue;
        }
        let (cpu, cs) = time(|| test_switches::without_hooks(|| c.prove()), 1);
        QUOTIENT_CHECK.store(true, Ordering::Relaxed);
        let (checks, bad) = (hooks::quotient_checks(), hooks::quotient_check_diffs());
        let _ = c.prove();
        QUOTIENT_CHECK.store(false, Ordering::Relaxed);
        let checked = hooks::quotient_checks() > checks;
        let pass = checked && hooks::quotient_check_diffs() == bad;
        let (dev, gs) = time(|| c.prove(), 1);
        row(
            "quotient",
            shape.ext_k,
            "proof",
            gs,
            cs,
            pass && dev == cpu && dev.1,
            None,
        );
        gpu::end_request();
    }
    drop(tsv);
    eprintln!("wrote {out}");
    eprintln!("MSM skew ratios (case time / uniform time, fastest of 7; limit 1.5):");
    for (case, r, k) in skew.into_inner() {
        eprintln!("  {case}: max {r:.3} at 2^{k}");
    }
    let failed = failed.into_inner();
    if !failed.is_empty() {
        for f in &failed {
            eprintln!("FAILED: {f}");
        }
        std::process::exit(1);
    }
}
