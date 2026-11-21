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

//! The device NTT against the stock CPU transforms, bit for bit.

#![cfg(target_os = "macos")]

mod common;

use common::{declines, random_scalars as random};
use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use midnight_curves::{
    Fq,
    fft::{best_fft_with_twiddles, compute_twiddles},
};
use midnight_metal::{Scalar, field::FR_MODULUS, ntt_test_support as dev};
use midnight_proofs::{
    gpu::{
        adapter::{from_scalar, scalar, scalars, scalars_mut},
        test_switches::without_hooks,
    },
    poly::{EvaluationDomain, FftDomain},
};

fn setup() {
    assert!(midnight_metal::device(), "no Metal device");
    midnight_metal::set_min_k(1);
}

fn root(log_n: u32) -> Fq {
    (log_n..Fq::S).fold(Fq::ROOT_OF_UNITY, |w, _| w.square())
}

/// The stock transform at `omega` as `EvaluationDomain` runs it, then times
/// `divisor`.
fn stock(input: &[Fq], omega: Fq, log_n: u32, divisor: Option<Fq>) -> Vec<Fq> {
    let mut a = input.to_vec();
    best_fft_with_twiddles(&mut a, &compute_twiddles(&omega, log_n), log_n);
    if let Some(d) = divisor {
        a.iter_mut().for_each(|x| *x *= d);
    }
    a
}

/// The hook: `fft` without a divisor, `ifft` with one.
fn hook(a: &mut [Fq], omega: Fq, log_n: u32, divisor: Option<Fq>) -> bool {
    match divisor {
        None => midnight_metal::fft(scalars_mut(a), scalar(omega), log_n),
        Some(d) => midnight_metal::ifft(scalars_mut(a), scalar(omega), log_n, scalar(d)),
    }
}

#[test]
fn roots_match_curves() {
    setup();
    for log_n in 0..=28 {
        let w = root(log_n);
        assert_eq!(dev::root(log_n, false), Some(scalar(w)), "2^{log_n}");
        assert_eq!(dev::root(log_n, true), Some(scalar(w.invert().unwrap())));
    }
    assert_eq!(dev::root(29, false), None);
}

/// One pass: fewer than four and exactly four elements per thread, a
/// partial and a full threadgroup. Two passes: unequal and equal radices,
/// the high twiddle table only (16), both tables (17), the largest (20).
/// Three passes: equal and unequal radices.
#[test]
fn fft_matches_stock() {
    setup();
    for log_n in [1, 2, 6, 10, 11, 12, 16, 17, 20, 21, 22] {
        let n = 1usize << log_n;
        let seed = 100 + u64::from(log_n);
        let (w, wi) = (root(log_n), root(log_n).invert().unwrap());
        let n_inv = Fq::from(n as u64).invert().unwrap();
        let d = random(1, seed ^ 0xd1)[0];
        let mut single = vec![Fq::ZERO; n];
        single[(seed as usize * 7919) % n] = Fq::ONE;
        let mut first = vec![Fq::ZERO; n];
        first[0] = Fq::ONE;
        let inputs = [
            random(n, seed),
            vec![Fq::ZERO; n],
            first,
            single,
            vec![-Fq::ONE; n],
        ];
        for (i, input) in inputs.iter().enumerate() {
            for (r, div) in [
                (w, None),
                (wi, None),
                (wi, Some(n_inv)),
                (wi, Some(d)),
                (w, Some(n_inv)),
                (w, Some(d)),
            ] {
                let mut got = input.clone();
                assert!(hook(&mut got, r, log_n, div), "declined");
                let ok = got == stock(input, r, log_n, div);
                assert!(ok, "2^{log_n} input {i}, inverse root {}, {div:?}", r == wi);
            }
        }
    }
}

#[test]
fn building_blocks_match_stock_domain() {
    setup();
    // (j, k): k == extended_k, one, two (one and both twiddle tables) and
    // three passes
    for (j, k) in [(2u32, 3u32), (4, 8), (4, 10), (8, 14), (4, 19)] {
        let domain = EvaluationDomain::<Fq>::new(j, k);
        let fft_domain = FftDomain::new(&domain);
        let ext_k = domain.extended_k();
        let zeta = [Fq::ZETA, Fq::ZETA.square()].map(scalar);
        let zeta_out = [zeta[1], zeta[0]];
        let divisor = scalar(Fq::from(1u64 << ext_k).invert().unwrap());
        let to_fq = |v: Vec<Scalar>| -> Vec<Fq> { v.into_iter().map(from_scalar).collect() };

        let coeffs = random(1 << k, u64::from(j * 100 + k));
        let ext = dev::coeff_to_extended(scalars(&coeffs), k, ext_k, zeta).unwrap();
        let want = fft_domain.coeff_to_extended(domain.coeff_from_vec(coeffs.clone()));
        assert!(
            to_fq(ext.clone()) == want.to_vec(),
            "coeff_to_extended k {k}"
        );

        for values in [
            to_fq(ext.clone()),
            random(1 << ext_k, u64::from(j * 1000 + k)),
        ] {
            let got = dev::extended_to_coeff(scalars(&values), ext_k, divisor, zeta_out).unwrap();
            let mut e = domain.empty_extended();
            e.copy_from_slice(&values);
            assert!(
                to_fq(got) == fft_domain.extended_to_coeff(e),
                "extended_to_coeff k {k}"
            );
        }
        let back = dev::extended_to_coeff(&ext, ext_k, divisor, zeta_out).unwrap();
        assert_eq!(&back[..1 << k], scalars(&coeffs));
        assert!(back[1 << k..].iter().all(|x| *x == [0; 4]));
    }
}

/// The kernels silently mis-compute on an unreduced by-value scalar.
#[test]
fn building_blocks_refuse_unreduced_scalars() {
    setup();
    let (bad, worse) = (FR_MODULUS, [u64::MAX; 4]);
    let (one, z) = (scalar(Fq::ONE), scalar(Fq::ZETA));
    let values = random(16, 604);
    let v = scalars(&values);
    let table = random(2, 611);
    let mut errors = vec![];
    for inverse in [false, true] {
        for s in [bad, worse] {
            errors.push(dev::ntt(v, 4, inverse, Some(s)).unwrap_err());
        }
    }
    for zeta in [[bad, z], [z, bad], [worse, worse]] {
        errors.push(dev::coeff_to_extended(v, 4, 5, zeta).unwrap_err());
    }
    errors.push(dev::extended_to_coeff(v, 4, bad, [z, z]).unwrap_err());
    errors.push(dev::extended_to_coeff(v, 4, one, [z, bad]).unwrap_err());
    errors.push(dev::elementwise(v, [z, bad], one, scalars(&table)).unwrap_err());
    errors.push(dev::elementwise(v, [z, z], bad, scalars(&table)).unwrap_err());
    for e in errors {
        assert!(e.contains("unreduced"), "{e}");
    }
    let got = dev::ntt(v, 4, false, Some(one)).unwrap();
    assert_eq!(&got[..], scalars(&stock(&values, root(4), 4, None)));
}

#[test]
fn declines_leave_the_buffer_unchanged() {
    setup();
    let log_n = 12;
    let n = 1usize << log_n;
    let input = random(n, 4242);
    let w = root(log_n);
    let div = Fq::from(n as u64).invert().unwrap();
    let declines_shape = |a: &mut Vec<Fq>, r: Fq, lg: u32| {
        let copy = a.clone();
        for (class, divisor) in [("fft", None), ("ifft", Some(div))] {
            let before = declines(class, "shape");
            assert!(!hook(a, r, lg, divisor));
            assert_eq!(*a, copy);
            assert!(declines(class, "shape") > before);
        }
    };
    // another primitive root, the roots of other sizes, a non-root
    for bad in [w * w * w, root(log_n + 1), root(log_n - 1), Fq::from(5u64)] {
        declines_shape(&mut input.clone(), bad, log_n);
    }
    for (len, lg) in [
        (n - 1, log_n),
        (n, log_n + 1),
        (n, log_n - 1),
        (2 * n, log_n),
    ] {
        declines_shape(&mut random(len, 99), root(lg), lg);
    }

    let mut raw: Vec<Scalar> = scalars(&input).to_vec();
    raw[17] = [u64::MAX; 4];
    let copy = raw.clone();
    let before = declines("fft", "unreduced");
    assert!(!midnight_metal::fft(&mut raw, scalar(w), log_n));
    assert_eq!(raw, copy);
    assert_eq!(declines("fft", "unreduced") - before, 1);
    let mut a = input.clone();
    let before = declines("ifft", "unreduced");
    let wi = scalar(w.invert().unwrap());
    assert!(!midnight_metal::ifft(
        scalars_mut(&mut a),
        wi,
        log_n,
        FR_MODULUS
    ));
    assert_eq!(a, input);
    assert_eq!(declines("ifft", "unreduced") - before, 1);
    assert!(hook(&mut a, w, log_n, None));
}

#[test]
fn hooks_serve_the_domain_transforms() {
    setup();
    common::install_hooks(midnight_metal::quotient);
    let domain = EvaluationDomain::<Fq>::new(4, 14);
    let fft_domain = FftDomain::new(&domain);
    let values = random(1 << 14, 31337);
    let transforms = || {
        (
            fft_domain.lagrange_to_coeff(domain.lagrange_from_vec(values.clone())),
            fft_domain.coeff_to_lagrange(domain.coeff_from_vec(values.clone())),
        )
    };
    let before = midnight_metal::stats();
    let (coeffs, evals) = transforms();
    let after = midnight_metal::stats();
    assert!(after.ifft.served > before.ifft.served, "ifft not served");
    assert!(after.fft.served > before.fft.served, "fft not served");
    let (want_coeffs, want_evals) = without_hooks(transforms);
    assert!(coeffs.to_vec() == want_coeffs.to_vec());
    assert!(evals.to_vec() == want_evals.to_vec());
}

/// Ignored: it needs about 10 GiB of memory.
#[test]
#[ignore]
fn large_transform_round_trip() {
    setup();
    let log_n = 26;
    let input = random(1 << log_n, 2026);
    let fwd = dev::ntt(scalars(&input), log_n, false, None).unwrap();
    let n_inv = Fq::from(1u64 << log_n).invert().unwrap();
    let back = dev::ntt(&fwd, log_n, true, Some(scalar(n_inv))).unwrap();
    assert_eq!(&back[..], scalars(&input));
}

#[test]
fn parallel_ifft_callers_match_stock() {
    setup();
    let log_n = 16;
    let w_inv = root(log_n).invert().unwrap();
    let div = Some(Fq::from(1u64 << log_n).invert().unwrap());
    std::thread::scope(|s| {
        for t in 0..6u64 {
            s.spawn(move || {
                for rep in 0..3u64 {
                    let input = random(1 << log_n, 100 + 10 * t + rep);
                    let mut got = input.clone();
                    assert!(hook(&mut got, w_inv, log_n, div));
                    assert!(
                        got == stock(&input, w_inv, log_n, div),
                        "caller {t}, rep {rep}"
                    );
                }
            });
        }
    });
    assert!(midnight_metal::end_request());
}
