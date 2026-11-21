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

//! The G1 MSM on the device against blst and the stock CPU MSM
//! (`msm_pippenger`). The window widths 15 and 16 and the sizes with several
//! chunks run in a release build only.

#![cfg(target_os = "macos")]

mod common;

use std::sync::{MutexGuard, OnceLock};

use blst::{
    BLST_ERROR, blst_fp, blst_fp_mul, blst_p1_affine, blst_p1_affine_in_g1, blst_p1_uncompress,
};
use common::random_scalars;
use ff::Field;
use group::{Curve, Group, prime::PrimeCurveAffine};
use midnight_curves::{Bls12, Fq, G1Affine, G1Projective, msm::msm_pippenger};
use midnight_metal::{
    self as metal, G1AffineLimbs, MsmStages, Scalar,
    ctx::{self, Arg},
};
use midnight_proofs::{
    gpu::{adapter, test_switches::without_hooks},
    poly::{
        Coeff, EvaluationDomain, Polynomial, PolynomialLabel,
        commitment::PolynomialCommitmentScheme,
        kzg::{KZGCommitmentScheme, params::ParamsKZG},
    },
};
use rand_chacha::ChaCha8Rng;
use rand_core::SeedableRng;
use rayon::prelude::*;

const UNREGISTERED: (&str, &str, u64) = ("msm", "unregistered-bases", 1);

/// `min_k`: an explicit threshold, or `None` for the defaults.
fn setup(min_k: Option<u32>, cpu_share: bool) -> MutexGuard<'static, ()> {
    let g = common::serial();
    match min_k {
        Some(k) => assert!(metal::set_min_k(k)),
        None => metal::reset_min_k(),
    }
    set_cpu_share(cpu_share);
    g
}

/// Whether `MIDNIGHT_METAL_MIN_K` overrides the defaults.
fn defaults_overridden() -> bool {
    let explicit = metal::thresholds().explicit;
    if explicit {
        eprintln!("MIDNIGHT_METAL_MIN_K is set: the defaults are not in force; skipped");
    }
    explicit
}

fn set_cpu_share(on: bool) {
    // SAFETY: called under the lock of `setup`; no other thread of this
    // binary reads the environment meanwhile.
    unsafe {
        if on {
            std::env::remove_var("MIDNIGHT_METAL_MSM_CPU_SHARE");
        } else {
            std::env::set_var("MIDNIGHT_METAL_MSM_CPU_SHARE", "off");
        }
    }
}

/// `n` distinct points: chunks of `P + i Q` from random `P`, `Q`.
fn random_points(n: usize, seed: u64) -> Vec<G1Affine> {
    let mut out = vec![G1Affine::identity(); n];
    out.par_chunks_mut(1 << 12).enumerate().for_each(|(c, chunk)| {
        let mut rng = ChaCha8Rng::seed_from_u64(seed ^ ((c as u64) << 20));
        let step = G1Projective::random(&mut rng);
        let mut p = G1Projective::random(&mut rng);
        let proj: Vec<G1Projective> = (0..chunk.len())
            .map(|_| {
                p += step;
                p
            })
            .collect();
        G1Projective::batch_normalize(&proj, chunk);
    });
    out
}

fn points_cache() -> &'static [G1Affine] {
    static P: OnceLock<Vec<G1Affine>> = OnceLock::new();
    P.get_or_init(|| random_points(1 << 20, 1))
}

fn msm(s: &[Fq], b: &[G1Affine]) -> Option<G1Projective> {
    metal::msm_g1(adapter::scalars(s), adapter::affine(b)).map(adapter::from_jacobian)
}

/// The device MSM is served and equals `msm_pippenger`.
fn check(name: &str, s: &[Fq], b: &[G1Affine]) {
    let before = metal::stats().msm.served;
    let got = msm(s, b).unwrap_or_else(|| panic!("{name}: declined {:?}", metal::declines()));
    assert!(got == msm_pippenger(s, b), "{name}: MSM of {}", s.len());
    assert_eq!(metal::stats().msm.served, before + 1, "{name}");
}

/// The path and plan of one MSM, its value checked.
fn stages(s: &[Fq], b: &[G1Affine]) -> MsmStages {
    let (r, st) = metal::msm_g1_stages(adapter::scalars(s), adapter::affine(b))
        .unwrap_or_else(|| panic!("an MSM of {} declined", s.len()));
    assert!(
        adapter::from_jacobian(r) == msm_pippenger(s, b),
        "MSM of {}",
        s.len()
    );
    st
}

/// The device value, or the stock CPU MSM when it declines.
fn hook_or_stock(s: &[Fq], b: &[G1Affine]) -> G1Projective {
    msm(s, b).unwrap_or_else(|| msm_pippenger(s, b))
}

fn sized(b: &[G1Affine]) -> bool {
    metal::msm_sized(b.len(), adapter::affine(b))
}

/// `msm_g1` declines `unregistered-bases` only, with no device MSM, no table
/// upload and no G1 check of the bases.
fn declines_unregistered(what: &str, s: &[Fq], b: &[G1Affine]) {
    metal::reset_stats();
    let counts = metal::msm_counts();
    let checks = metal::one_shot_g1_checks();
    assert!(msm(s, b).is_none(), "{what}: served");
    assert_eq!(metal::stats().msm.served, 0, "{what}");
    assert_eq!(metal::declines(), vec![UNREGISTERED], "{what}");
    assert_eq!(metal::msm_counts(), counts, "{what}");
    assert_eq!(metal::one_shot_g1_checks(), checks, "{what}");
}

/// The CUDA crate's mask vector (gpu/src/msm.rs `mask_vector`).
fn cuda_mask_vector(n: usize) -> Vec<Scalar> {
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = || {
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    (0..n).map(|_| [next(), next(), next(), next() >> 3]).collect()
}

fn mask_fq(n: usize) -> Vec<Fq> {
    cuda_mask_vector(n).into_iter().map(adapter::from_scalar).collect()
}

type Xyzz = [u64; 24];

// Operation codes of `msm_test_g1` (msm_test.metal).
const OP_MADD: u32 = 0;
const OP_ADD: u32 = 1;
const OP_FROM_AFFINE: u32 = 2;

fn fp(l: &[u64]) -> blst_fp {
    blst_fp {
        l: l.try_into().unwrap(),
    }
}

fn fmul(a: &blst_fp, b: &blst_fp) -> blst_fp {
    let mut r = blst_fp::default();
    // SAFETY: valid field elements.
    unsafe { blst_fp_mul(&mut r, a, b) };
    r
}

fn fsqr(a: &blst_fp) -> blst_fp {
    fmul(a, a)
}

/// `(x z^2, y z^3, z^3, z^2)`; infinity is all zero.
fn xyzz_of(a: &G1Affine, z: &blst_fp) -> Xyzz {
    let a = adapter::affine(std::slice::from_ref(a))[0];
    let mut r = [0u64; 24];
    if a.iter().all(|&w| w == 0) {
        return r;
    }
    let zz = fsqr(z);
    let zzz = fmul(&zz, z);
    r[..6].copy_from_slice(&fmul(&fp(&a[..6]), &zz).l);
    r[6..12].copy_from_slice(&fmul(&fp(&a[6..]), &zzz).l);
    r[12..18].copy_from_slice(&zzz.l);
    r[18..].copy_from_slice(&zz.l);
    r
}

/// An XYZZ record as a point, checking `ZZ^3 = ZZZ^2`.
fn point_of(r: &Xyzz) -> G1Projective {
    let (x, y, zzz, zz) = (fp(&r[..6]), fp(&r[6..12]), fp(&r[12..18]), fp(&r[18..]));
    let zero = |f: &blst_fp| f.l.iter().all(|&w| w == 0);
    assert_eq!(zero(&zz), zero(&zzz), "ZZ and ZZZ disagree on infinity");
    assert_eq!(fmul(&fsqr(&zz), &zz).l, fsqr(&zzz).l, "ZZ^3 != ZZZ^2");
    let mut j = [0u64; 18];
    j[..6].copy_from_slice(&fmul(&x, &zz).l);
    j[6..12].copy_from_slice(&fmul(&y, &zzz).l);
    j[12..].copy_from_slice(&zz.l);
    adapter::from_jacobian(j)
}

fn g1_kernel(op: u32, a: &[Xyzz], b: &[Xyzz], b_aff: &[G1AffineLimbs], flags: &[u32]) -> Vec<Xyzz> {
    let n = a.len() as u32;
    let s = ctx::lock().unwrap();
    let c = s.ctx();
    let bufs = [
        c.upload(a).unwrap(),
        c.upload(b).unwrap(),
        c.upload(b_aff).unwrap(),
        c.upload(flags).unwrap(),
        c.alloc(size_of_val(a)).unwrap(),
    ];
    c.run(|cmd| {
        let mut args: Vec<Arg> = bufs.iter().map(Arg::Buffer).collect();
        args.extend([Arg::value(&op), Arg::value(&n)]);
        cmd.dispatch("msm_test_g1", n as usize, &args)
    })
    .unwrap();
    bufs[4].as_slice::<Xyzz>().to_vec()
}

#[test]
fn g1_kernels_match_blst() {
    let _g = setup(Some(14), true);
    let mut rng = ChaCha8Rng::seed_from_u64(7);
    let pts: Vec<G1Affine> = (0..64).map(|_| G1Projective::random(&mut rng).to_affine()).collect();
    let inf = G1Affine::identity();
    let mut pairs: Vec<(G1Affine, G1Affine)> = (0..32).map(|i| (pts[i], pts[i + 32])).collect();
    for p in &pts[..4] {
        pairs.extend([(*p, inf), (inf, *p), (*p, *p), (*p, -*p)]);
    }
    pairs.push((inf, inf));
    let z = |i: usize| fp(&adapter::affine(&pts)[(i + 17) % pts.len()][..6]);
    let a: Vec<Xyzz> = pairs.iter().enumerate().map(|(i, p)| xyzz_of(&p.0, &z(i))).collect();
    // b in XYZZ with a different scale, so P + P is not a bitwise copy
    let b: Vec<Xyzz> = pairs.iter().enumerate().map(|(i, p)| xyzz_of(&p.1, &z(i + 5))).collect();
    let b_aff: Vec<G1Affine> = pairs.iter().map(|p| p.1).collect();
    for (op, neg) in [
        (OP_MADD, false),
        (OP_MADD, true),
        (OP_FROM_AFFINE, false),
        (OP_FROM_AFFINE, true),
        (OP_ADD, false),
    ] {
        let flags = vec![neg as u32; pairs.len()];
        let got = g1_kernel(op, &a, &b, adapter::affine(&b_aff), &flags);
        for (i, (p, q)) in pairs.iter().enumerate() {
            let q = if neg { -q.to_curve() } else { q.to_curve() };
            let want = if op == OP_FROM_AFFINE {
                q
            } else {
                p.to_curve() + q
            };
            assert!(
                point_of(&got[i]) == want,
                "op {op}, negated {neg}, pair {i}"
            );
            if op == OP_ADD && *p != inf && q == -p.to_curve() {
                assert_eq!(got[i], [0u64; 24], "P + (-P) at {i}");
            }
        }
    }
}

#[test]
fn mask_is_the_cuda_vector() {
    let _g = setup(Some(14), true);
    let (i0, n) = (100u32, 5000u32);
    let want = cuda_mask_vector((i0 + n) as usize);
    let s = ctx::lock().unwrap();
    let c = s.ctx();
    let out = c.alloc(n as usize * 32).unwrap();
    c.run(|cmd| {
        let args = [Arg::Buffer(&out), Arg::value(&i0), Arg::value(&n)];
        cmd.dispatch("msm_test_mask", n as usize, &args)
    })
    .unwrap();
    assert_eq!(out.as_slice::<Scalar>(), &want[i0 as usize..]);
    assert!(want.iter().all(metal::field::is_reduced));
}

/// Special inputs are spread over all indices so both shares of a split
/// hold them, and `odd[i] = odd[i / 2]` repeats points across the shares.
fn differential(split: bool) {
    let _g = setup(Some(0), split);
    metal::reset_stats();
    // `(log2 n, wbits)`: one size per window width class of the one-shot path
    let sizes: &[(u32, u32)] = if split || cfg!(debug_assertions) {
        &[(14, 11), (16, 13)]
    } else {
        &[(14, 11), (16, 13), (20, 15)]
    };
    for &(k, wbits) in sizes {
        let n = 1usize << k;
        let bases = &points_cache()[..n];
        let path = |st: MsmStages| (st.device_points < n as u64, st.wbits);
        let few = [
            Fq::from(3),
            -Fq::from(5),
            Fq::random(ChaCha8Rng::seed_from_u64(k as u64)),
            Fq::ONE,
        ];
        let repeated: Vec<Fq> = (0..n).map(|i| few[(i * 7 + i / 13) % few.len()]).collect();
        let c = Fq::random(ChaCha8Rng::seed_from_u64(99 + k as u64));
        let random = random_scalars(n, k as u64);
        assert_eq!(path(stages(&random, bases)), (split, wbits), "2^{k}");
        for (name, s) in [
            ("random", random),
            ("all equal", vec![c; n]),
            ("all zero", vec![Fq::ZERO; n]),
            ("all one", vec![Fq::ONE; n]),
            ("all r-1", vec![-Fq::ONE; n]),
            ("repeated", repeated.clone()),
        ] {
            check(name, &s, bases);
        }

        let mut odd = bases.to_vec();
        for i in (0..n).step_by(7) {
            odd[i] = G1Affine::identity();
        }
        for i in (3..n).step_by(11) {
            odd[i] = odd[i / 2];
        }
        for i in (5..n).step_by(17) {
            odd[i] = -odd[i - 1];
        }
        let odd_random = random_scalars(n, 1000 + k as u64);
        assert_eq!(path(stages(&odd_random, &odd)), (split, wbits), "2^{k}");
        for (name, s) in [
            ("odd bases, random", odd_random),
            ("odd bases, repeated", repeated),
            ("odd bases, all one", vec![Fq::ONE; n]),
        ] {
            check(name, &s, &odd);
        }
    }
    assert!(metal::declines().is_empty(), "{:?}", metal::declines());
}

#[test]
fn msm_matches_cpu() {
    differential(true);
    differential(false);
}

/// Every worker of a small pool waits on the device lock while the holder's
/// CPU share runs on the same pool.
#[test]
fn msm_from_rayon_pool() {
    let _g = setup(Some(14), true);
    let n = 1usize << 14;
    let bases = &points_cache()[..n];
    let inputs: Vec<Vec<Fq>> = (0..6).map(|i| random_scalars(n, 300 + i)).collect();
    let want: Vec<Option<G1Projective>> =
        inputs.iter().map(|s| Some(msm_pippenger(s, bases))).collect();
    assert!(stages(&inputs[0], bases).device_points < n as u64);
    let run = || inputs.par_iter().map(|s| msm(s, bases)).collect::<Vec<_>>();
    assert!(run() == want);
    let pool = rayon::ThreadPoolBuilder::new().num_threads(3).build().unwrap();
    assert!(pool.install(run) == want);
}

/// Around the chunk stride of 32, below the plan table, and a split one.
#[test]
fn msm_odd_lengths() {
    let _g = setup(Some(0), true);
    for n in [1usize, 2, 31, 33, 193, 1000, (1 << 14) + 5] {
        let (s, b) = (random_scalars(n, n as u64), &points_cache()[..n]);
        check("odd length", &s, b);
        assert_eq!(stages(&s, b).device_points < n as u64, n >= 1 << 14, "{n}");
    }
}

/// Scalars at the boundary of the `abs` step of `msm_digits`, raw and as
/// `B - mask_i` so the masked value on the device is `B`.
#[test]
fn abs_boundary_scalars_match_cpu() {
    let _g = setup(Some(0), true);
    let half = Fq::from(2).invert().unwrap();
    let p2 = |e: u64| Fq::from(2).pow_vartime([e]);
    let top = Fq::from(0x39f6_d3a9u64);
    let boundary = [
        -half,                               // (r - 1) / 2
        half,                                // (r + 1) / 2
        -Fq::ONE,                            // r - 1
        p2(254) - Fq::ONE,                   // 2^254 - 1 reduced
        (top + Fq::ONE) * p2(224) - Fq::ONE, // top limb of s and r - s equal
        top * p2(224),                       // top limbs next to each other
    ];
    let n = 1usize << 14;
    let bases = &points_cache()[..n];
    let mask = mask_fq(n);
    for split in [false, true] {
        set_cpu_share(split);
        for masked in [false, true] {
            let b = |i: usize, j: usize| {
                boundary[j % boundary.len()] - mask[i] * Fq::from(masked as u64)
            };
            let mut mixed = random_scalars(n, 81);
            for i in (0..n).step_by(3) {
                mixed[i] = b(i, i / 3);
            }
            let only: Vec<Fq> = (0..n).map(|i| b(i, i)).collect();
            for (name, s) in [("mixed", mixed), ("only", only)] {
                check(
                    &format!("{name}, masked {masked}, split {split}"),
                    &s,
                    bases,
                );
            }
        }
    }
}

#[test]
fn wide_windows_and_chunks_match_cpu() {
    let _g = setup(Some(14), true);
    if cfg!(debug_assertions) {
        eprintln!("skipped in a debug build");
        return;
    }
    let n = 1usize << 22;
    let bases = random_points(n, 2222);
    let scal = random_scalars(n, 2223);
    let h = metal::register_srs(adapter::affine(&bases));
    for (k, wbits, batches) in [(20u32, 15u32, 1u32), (22, 16, 2)] {
        let m = 1usize << k;
        let (s, b) = (&scal[..m], &bases[..m]);
        let st = stages(s, b);
        assert!(st.table && st.device_points < m as u64, "2^{k}: {st:?}");
        assert_eq!((st.wbits, st.batches), (wbits, batches), "2^{k}: {st:?}");
        check(&format!("table 2^{k}"), s, b);
    }
    drop(h);

    set_cpu_share(false);
    let m = (1usize << 21) + 4096;
    let st = stages(&scal[..m], &bases[..m]);
    assert!(!st.table && st.device_points == m as u64, "{st:?}");
    assert_eq!((st.wbits, st.batches), (16, 2), "{st:?}");
}

/// `s_i = c - mask_i` puts every point of a window in one bucket: exact up
/// to `HOT_BUCKET_LIMIT` points, a `device-error` decline above it.
#[test]
fn hot_bucket_is_exact_or_declined() {
    let _g = setup(Some(14), true);
    let c = Fq::random(ChaCha8Rng::seed_from_u64(4242));
    for (k, served) in [(16u32, true), (17, false)] {
        let n = 1usize << k;
        let bases = &points_cache()[..n];
        let s: Vec<Fq> = mask_fq(n).iter().map(|m| c - m).collect();
        let want = msm_pippenger(&s, bases);
        for registered in [false, true] {
            let h = registered.then(|| metal::register_srs(adapter::affine(bases)));
            metal::reset_stats();
            let got = msm(&s, bases);
            let what = format!("2^{k}, registered {registered}");
            if served {
                assert!(got == Some(want), "{what}");
            } else {
                assert!(got.is_none(), "{what}");
                assert_eq!(
                    metal::declines(),
                    vec![("msm", "device-error", 1)],
                    "{what}"
                );
                assert!(hook_or_stock(&s, bases) == want, "{what}");
            }
            drop(h);
        }
    }
}

/// `n` scalars, zero except `nz` of them at spread positions.
fn sparse_scalars(n: usize, nz: usize, seed: u64) -> Vec<Fq> {
    let mut s = vec![Fq::ZERO; n];
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let step = n / nz.max(1);
    for i in 0..nz {
        s[i * step + (i * 7919) % step.max(1)] = Fq::random(&mut rng);
    }
    s
}

/// The device MSM, or `None` on a `below-min-k` decline with no device work.
fn try_device_msm(s: &[Fq], b: &[G1Affine]) -> Option<G1Projective> {
    metal::reset_stats();
    let counts = metal::msm_counts();
    let r = msm(s, b);
    if r.is_some() {
        assert_eq!(metal::stats().msm.served, 1);
    } else {
        assert_eq!(metal::declines(), vec![("msm", "below-min-k", 1)]);
        assert_eq!(metal::msm_counts(), counts);
        assert_eq!(metal::stats().msm.served, 0);
    }
    r
}

/// With the defaults a table needs `2^12 + n/5` non-zero scalars; an
/// explicit threshold needs `2^k` on both paths.
#[test]
fn sparse_msm_declines_below_min_k() {
    let _g = setup(None, true);
    let t = metal::thresholds();
    assert!(!t.explicit, "MIDNIGHT_METAL_MIN_K is set: {t:?}");
    assert_eq!(t.msm_one_shot, None);
    let n = 1usize << 16;
    let bases = &points_cache()[..n];
    let need = (1usize << 12) + n / 5;
    let declined = |s: &[Fq], b: &[G1Affine]| try_device_msm(s, b).is_none();
    let served = |s: &[Fq], b: &[G1Affine]| {
        assert!(
            try_device_msm(s, b) == Some(msm_pippenger(s, b)),
            "{}",
            s.len()
        );
    };

    for nz in [0, 2, 11, n / 3, n] {
        declines_unregistered(&format!("{nz}"), &sparse_scalars(n, nz, nz as u64), bases);
    }

    let h = metal::register_srs(adapter::affine(bases));
    for nz in [2, 1 << t.msm_table, need - 1] {
        assert!(declined(&sparse_scalars(n, nz, 5), bases), "table {nz}");
    }
    served(&sparse_scalars(n, need, 6), bases);

    // a column with zero rows before its blinding rows; the multi-open's
    // length m - 1
    let m = 1usize << t.msm_table;
    for len in [m, m - 1] {
        let mut s = random_scalars(len, 13);
        s[len - 20..len - 4].fill(Fq::ZERO);
        served(&s, &bases[..len]);
    }
    assert!(declined(&sparse_scalars(m, m / 2, 14), &bases[..m]));

    assert!(metal::set_min_k(14));
    served(&sparse_scalars(n, 1 << 14, 7), bases);
    assert!(declined(&sparse_scalars(n, (1 << 14) - 1, 8), bases));
    drop(h);
    served(&sparse_scalars(n, 1 << 14, 9), bases);
    assert!(declined(&sparse_scalars(n, (1 << 14) - 1, 10), bases));
}

fn sized_call(s: &[Fq], b: &[G1Affine]) -> (bool, Option<G1Projective>) {
    metal::reset_stats();
    let (sized, r) = metal::msm_g1_sized(adapter::scalars(s), adapter::affine(b));
    (sized, r.map(adapter::from_jacobian))
}

/// `msm_sized`, `msm_g1` and `msm_g1_sized` agree on unregistered,
/// registered, dropped and malformed calls.
#[test]
fn unregistered_bases_decline_by_default() {
    let _g = setup(None, true);
    if defaults_overridden() {
        return;
    }
    assert_eq!(metal::thresholds().msm_one_shot, None);
    let n = 1usize << 15;
    let bases = &points_cache()[..n];
    let s = random_scalars(n, 516);
    let want = msm_pippenger(&s, bases);

    assert!(!sized(bases));
    declines_unregistered("unregistered", &s, bases);
    assert!(hook_or_stock(&s, bases) == want);
    assert_eq!(sized_call(&s, bases), (false, None));
    assert_eq!(metal::declines(), vec![UNREGISTERED]);

    let h = metal::register_srs(adapter::affine(bases));
    assert!(sized(bases));
    let checks = metal::one_shot_g1_checks();
    let (c0, o0, _) = metal::msm_counts();
    check("registered", &s, bases);
    let (c1, o1, _) = metal::msm_counts();
    assert_eq!((c1 - c0, o1 - o0), (1, 0), "from the table");
    assert_eq!(metal::one_shot_g1_checks(), checks);
    assert_eq!(sized_call(&s, bases), (true, Some(want)));
    assert_eq!(metal::stats().msm.served, 1);
    drop(h);

    assert!(!sized(bases));
    declines_unregistered("dropped", &s, bases);
    assert_eq!(sized_call(&s[..n - 1], bases), (false, None));
    assert_eq!(metal::declines(), vec![("msm", "shape", 1)]);
}

#[test]
fn infinity_bases_and_malformed_calls() {
    let _g = setup(Some(14), true);
    let n = 1usize << 14;
    let mut bases = points_cache()[..n].to_vec();
    for i in (0..n).step_by(5) {
        bases[i] = G1Affine::identity();
    }
    let s: Vec<Fq> = random_scalars(n, 91)
        .into_iter()
        .map(|x| if x == Fq::ZERO { Fq::ONE } else { x })
        .collect();
    let (_, o0, _) = metal::msm_counts();
    check("infinity bases, one-shot", &s, &bases);
    assert_eq!(metal::msm_counts().1, o0 + 1);
    let h = metal::register_srs(adapter::affine(&bases));
    let (c0, _, _) = metal::msm_counts();
    check("infinity bases, table", &s, &bases);
    assert_eq!(metal::msm_counts().0, c0 + 1);

    let mut unreduced = adapter::scalars(&s).to_vec();
    unreduced[7] = metal::field::FR_MODULUS;
    for (reason, sc, bl) in [
        ("shape", &adapter::scalars(&s)[..n - 1], n),
        ("shape", adapter::scalars(&s), n - 1),
        ("unreduced", &unreduced[..], n),
    ] {
        metal::reset_stats();
        assert!(metal::msm_g1(sc, adapter::affine(&bases[..bl])).is_none());
        assert_eq!(metal::declines(), vec![("msm", reason, 1)]);
    }
    drop(h);
}

/// The first MSM uploads the table, the second has `MSM(r)` cached (one
/// pass), and longer prefixes split with the CPU.
#[test]
fn registered_table_prefixes() {
    let _g = setup(Some(14), true);
    let n = (1usize << 17) + 5;
    let bases = &points_cache()[..n];
    let handle = metal::register_srs(adapter::affine(bases));
    assert_eq!(handle.len(), n);
    assert_eq!(handle.device_bytes(), 0, "a registration is host memory");
    assert!(handle.verify(adapter::affine(bases)));
    let (c0, o0, u0) = metal::msm_counts();

    let m = 1usize << 14;
    let st = stages(&random_scalars(m, 5), &bases[..m]);
    assert!(st.table && st.passes == 2, "{st:?}");
    assert_eq!(metal::msm_counts(), (c0 + 1, o0, u0 + 1));
    assert_eq!(handle.device_bytes(), (n * 96) as u64);
    let st = stages(&random_scalars(m, 6), &bases[..m]);
    assert!(st.table && st.passes == 1, "{st:?}");

    for len in [1usize << 17, n] {
        let s = random_scalars(len, len as u64);
        let st = stages(&s, &bases[..len]);
        assert!(st.table && st.device_points < len as u64, "{len}: {st:?}");
        check("table prefix, split", &s, &bases[..len]);
    }
    assert_eq!(metal::msm_counts(), (c0 + 6, o0, u0 + 1));
}

/// A table changed at one point a sampled check would not read is dropped:
/// with the defaults the call declines, with an explicit threshold the
/// one-shot path serves it.
#[test]
fn stale_table_declines_by_default_and_one_shot_when_explicit() {
    let _g = setup(None, true);
    if defaults_overridden() {
        return;
    }
    let n = 1usize << 15;
    let fresh = random_points(4, 4711);
    let s = random_scalars(n, 4712);
    let (i, j) = (3 * n / 7 + 5, 2 * (1 << 14) / 7 + 3);
    let registered = || {
        let bases = points_cache()[..n].to_vec();
        let h = metal::register_srs(adapter::affine(&bases));
        (bases, h)
    };

    let (mut bases, h) = registered();
    check("table", &s, &bases);
    bases[i] = fresh[0];
    let stale = metal::srs_stale();
    assert!(!sized(&bases));
    assert_eq!(metal::srs_stale(), stale + 1);
    declines_unregistered("stale, msm_sized first", &s, &bases);
    assert!(hook_or_stock(&s, &bases) == msm_pippenger(&s, &bases));
    assert_eq!(metal::srs_stale(), stale + 1);
    drop(h);

    let (mut bases, h) = registered();
    bases[i] = fresh[1];
    let stale = metal::srs_stale();
    declines_unregistered("stale", &s, &bases);
    assert_eq!(metal::srs_stale(), stale + 1);
    assert!(!sized(&bases));
    drop(h);

    let (mut bases, h) = registered();
    bases[i] = fresh[3];
    let stale = metal::srs_stale();
    assert_eq!(sized_call(&s, &bases), (false, None));
    assert_eq!(metal::srs_stale(), stale + 1);
    assert_eq!(metal::declines(), vec![UNREGISTERED]);
    assert!(!sized(&bases));
    drop(h);

    assert!(metal::set_min_k(14));
    let (mut bases, h) = registered();
    bases[i] = fresh[0];
    assert!(!h.verify(adapter::affine(&bases)));
    let stale = metal::srs_stale();
    assert!(sized(&bases));
    assert_eq!(metal::srs_stale(), stale + 1);
    let checks = metal::one_shot_g1_checks();
    let (c0, o0, u0) = metal::msm_counts();
    check("stale, explicit threshold", &s, &bases);
    assert_eq!(metal::msm_counts(), (c0, o0 + 1, u0));
    assert_eq!(metal::one_shot_g1_checks(), checks + 1);
    drop(h);

    let (mut bases, h) = registered();
    let s = random_scalars(1 << 14, 62);
    let m = s.len();
    check("prefix", &s, &bases[..m]);
    bases[j] = fresh[2];
    let stale = metal::srs_stale();
    let (c0, o0, u0) = metal::msm_counts();
    check("prefix, one point changed", &s, &bases[..m]);
    assert_eq!(metal::srs_stale(), stale + 1);
    assert_eq!(metal::msm_counts(), (c0, o0 + 1, u0));
    drop(h);
}

/// A point on the curve outside the prime-order subgroup.
fn non_subgroup_point() -> G1Affine {
    for x in 1u8.. {
        let mut compressed = [0u8; 48];
        compressed[0] = 0x80;
        compressed[47] = x;
        let mut p = blst_p1_affine::default();
        // SAFETY: 48 readable bytes; `p` is a valid affine point after a
        // successful decoding, which checks the curve but not the subgroup.
        let found = unsafe {
            blst_p1_uncompress(&mut p, compressed.as_ptr()) == BLST_ERROR::BLST_SUCCESS
                && !blst_p1_affine_in_g1(&p)
        };
        if found {
            // SAFETY: `G1Affine` is a transparent `blst_p1_affine`.
            return unsafe { std::mem::transmute::<blst_p1_affine, G1Affine>(p) };
        }
    }
    unreachable!()
}

#[test]
fn bases_outside_g1_decline() {
    let _g = setup(Some(14), true);
    let n = 1usize << 14;
    let k = n / 3;
    let mut off = adapter::affine(&points_cache()[..1])[0];
    off[6] ^= 1;
    // SAFETY: `G1Affine` is a transparent `blst_p1_affine` (`[u64; 12]`).
    let off = unsafe { std::mem::transmute::<G1AffineLimbs, G1Affine>(off) };
    for (what, p) in [
        ("not in the subgroup", non_subgroup_point()),
        ("off the curve", off),
    ] {
        let mut bases = points_cache()[..n].to_vec();
        bases[k] = p;
        for sc in [-Fq::ONE, -Fq::from(12345)] {
            let mut s = random_scalars(n, 71);
            s[k] = sc;
            for registered in [false, true] {
                let h = registered.then(|| metal::register_srs(adapter::affine(&bases)));
                metal::reset_stats();
                let counts = metal::msm_counts();
                let case = format!("{what}, {sc:?}, registered {registered}");
                assert!(msm(&s, &bases).is_none(), "{case}");
                let want = vec![("msm", "bases-not-in-subgroup", 1)];
                assert_eq!(metal::declines(), want, "{case}");
                assert_eq!(metal::stats().msm.served, 0, "{case}");
                assert_eq!(metal::msm_counts(), counts, "{case}");
                drop(h);
            }
            // the fallback runs on this input (a debug build of
            // midnight-curves asserts every point is in the subgroup)
            if what == "not in the subgroup" && !cfg!(debug_assertions) {
                let _ = msm_pippenger(&s, &bases);
            }
        }
        assert!(metal::set_min_k(0));
        let h = metal::register_srs(adapter::affine(&bases));
        check(
            "prefix before the bad point",
            &random_scalars(k, 73),
            &bases[..k],
        );
        drop(h);
        assert!(metal::set_min_k(14));
    }
}

/// KZG commitments through the hook equal the stock ones, served or not.
#[test]
fn hook_commitment_matches_stock() {
    let _g = setup(None, true);
    if defaults_overridden() {
        return;
    }
    const K: u32 = 14;
    let mut rng = ChaCha8Rng::seed_from_u64(12);
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, &mut rng);
    let h = metal::register_srs(adapter::affine(params.bases::<Coeff>()));
    let domain = EvaluationDomain::<Fq>::new(1, K);
    common::install_hooks(metal::quotient);
    let commit = |poly: &Polynomial<Fq, Coeff>| {
        KZGCommitmentScheme::<Bls12>::commit(&params, poly, PolynomialLabel::Custom("p".into()))
    };
    for (nz, device) in [(5usize, false), (1usize << K, true)] {
        let mut poly = domain.empty_coeff();
        let step = poly.len() / nz;
        for i in 0..nz {
            poly[i * step] = Fq::random(&mut rng);
        }
        metal::reset_stats();
        let got = commit(&poly);
        let served = metal::stats().msm.served;
        let declines = metal::declines();
        if device {
            assert_eq!(served, 1, "{declines:?}");
        } else {
            assert_eq!(served, 0);
            assert_eq!(declines, vec![("msm", "below-min-k", 1)]);
        }
        let want = without_hooks(|| commit(&poly));
        assert_eq!(metal::stats().msm.served, served, "a suspended hook served");
        assert!(got == want, "{nz} non-zero");
    }
    drop(h);
}
