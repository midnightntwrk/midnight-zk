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

//! The device transforms and MSM against the CPU, at edge inputs and sizes
//! `2^1 ..= 2^20`. The ordinary tests skip when there is no device. The bounded
//! sanitizer tests require a device.

use ff::{Field, PrimeField};
use group::{Curve, Group, prime::PrimeCurveAffine};
use midnight_curves::{Fq, G1Affine, G1Projective, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::gpu::adapter;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

fn device() -> bool {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return false;
    }
    gpu::set_min_k(1);
    true
}

/// Random values with edge values mixed in: 0, 1, -1, and repeats.
fn values(n: usize, seed: u64) -> Vec<Fq> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    (0..n)
        .map(|i| match i % 7 {
            0 => Fq::ZERO,
            1 => Fq::ONE,
            2 => -Fq::ONE,
            3 => Fq::from(5),
            _ => Fq::random(&mut rng),
        })
        .collect()
}

fn root(k: u32) -> Fq {
    let mut w = Fq::ROOT_OF_UNITY;
    for _ in k..Fq::S {
        w = w.square();
    }
    w
}

#[test]
fn ntt_matches_cpu() {
    if !device() {
        return;
    }
    check_ntt(1..=20);
}

fn check_ntt(sizes: impl IntoIterator<Item = u32>) {
    for k in sizes {
        let n = 1usize << k;
        let w = root(k);
        let a = values(n, k as u64);
        let mut cpu = a.clone();
        best_fft(&mut cpu, w, k);
        let mut dev = a.clone();
        assert!(
            gpu::fft(adapter::scalars_mut(&mut dev), adapter::scalar(w), k),
            "fft k={k}"
        );
        assert_eq!(dev, cpu, "fft k={k}");

        // the inverse with the domain's divisor, and with another divisor
        let wi = w.invert().unwrap();
        for d in [Fq::from(n as u64).invert().unwrap(), Fq::from(3)] {
            let mut cpu = a.clone();
            best_fft(&mut cpu, wi, k);
            cpu.iter_mut().for_each(|x| *x *= d);
            let mut dev = a.clone();
            assert!(gpu::ifft(
                adapter::scalars_mut(&mut dev),
                adapter::scalar(wi),
                k,
                adapter::scalar(d)
            ));
            assert_eq!(dev, cpu, "ifft k={k}");
        }
    }
    // a root that is not the standard one, a wrong length, an unreduced
    // value: declined, input unchanged
    let mut a = values(8, 1);
    let keep = a.clone();
    assert!(!gpu::fft(
        adapter::scalars_mut(&mut a),
        adapter::scalar(Fq::from(2)),
        3
    ));
    assert!(!gpu::fft(
        adapter::scalars_mut(&mut a[..7]),
        adapter::scalar(root(3)),
        3
    ));
    let mut bad = adapter::scalars(&a).to_vec();
    bad[3] = gpu::field::MODULUS;
    assert!(!gpu::fft(&mut bad, adapter::scalar(root(3)), 3));
    assert_eq!(a, keep);
}

fn points(n: usize, seed: u64) -> Vec<G1Affine> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let g = G1Projective::random(&mut rng);
    let mut acc = g;
    (0..n)
        .map(|i| {
            acc += g;
            if i % 11 == 5 {
                G1Affine::identity()
            } else {
                acc.to_affine()
            }
        })
        .collect()
}

#[test]
fn msm_matches_cpu() {
    if !device() {
        return;
    }
    check_msm(1..=20, 1 << 12);
}

fn check_msm(sizes: impl IntoIterator<Item = u32>, edge_len: usize) {
    for k in sizes {
        let n = 1usize << k;
        let p = points(n, k as u64);
        let s = values(n, 7 + k as u64);
        let cpu = G1Affine::multi_exp_affine(&p, &s);
        let dev = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&p)).expect("msm");
        assert_eq!(adapter::from_jacobian(dev), cpu, "msm k={k}");
    }
    // all scalars equal (a hot bucket without the mask), all zero
    let p = points(edge_len, 3);
    for s in [vec![Fq::from(9); edge_len], vec![Fq::ZERO; edge_len]] {
        let cpu = G1Affine::multi_exp_affine(&p, &s);
        let dev = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&p)).unwrap();
        assert_eq!(adapter::from_jacobian(dev), cpu);
    }
}

#[test]
fn registered_tables_and_prefix() {
    if !device() {
        assert_ne!(
            std::env::var("MIDNIGHT_GPU_REQUIRE_CUDA").as_deref(),
            Ok("1"),
            "registered-table check requires a CUDA device"
        );
        return;
    }
    check_registered_tables(1 << 12);
}

fn check_registered_tables(n: usize) {
    let mut p = points(n, 77);
    let s = values(n, 78);
    let (cached0, _, _) = gpu::msm::msm_counts();
    let h = gpu::register_srs(adapter::affine(&p));
    assert!(h.verify(adapter::affine(&p)));
    let dev = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&p)).unwrap();
    assert_eq!(
        adapter::from_jacobian(dev),
        G1Affine::multi_exp_affine(&p, &s)
    );
    // a prefix is served from the same table
    let m = n - 1;
    let dev = gpu::msm_g1(adapter::scalars(&s[..m]), adapter::affine(&p[..m])).unwrap();
    assert_eq!(
        adapter::from_jacobian(dev),
        G1Affine::multi_exp_affine(&p[..m], &s[..m])
    );
    assert!(gpu::msm::msm_counts().0 >= cached0 + 2);
    // the slice changes under its handle: the table is dropped, the result
    // is still the MSM of the current points
    // Index 1 is outside the eight sampled registration points at this length.
    // Its scalar is one, so the stale table produces a different group element.
    p[1] = (p[1] + G1Projective::generator()).to_affine();
    let stale = gpu::msm::srs_stale();
    let dev = gpu::msm_g1(adapter::scalars(&s), adapter::affine(&p)).unwrap();
    assert_eq!(
        adapter::from_jacobian(dev),
        G1Affine::multi_exp_affine(&p, &s)
    );
    assert_eq!(gpu::msm::srs_stale(), stale + 1);
    assert!(!h.verify(adapter::affine(&p)));
    drop(h);
    assert!(gpu::end_request());
}

mod sanitizer_device {
    use super::*;

    #[test]
    #[ignore = "requires a CUDA device under compute-sanitizer"]
    fn ntt() {
        assert!(device());
        check_ntt([1, 6, 9]);
        assert!(gpu::end_request());
    }

    #[test]
    #[ignore = "requires a CUDA device under compute-sanitizer"]
    fn msm() {
        assert!(device());
        check_msm([1, 6], 64);
        assert!(gpu::end_request());
    }

    #[test]
    #[ignore = "requires a CUDA device under compute-sanitizer"]
    fn registered() {
        assert!(device());
        check_registered_tables(64);
    }
}
