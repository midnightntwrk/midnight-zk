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

//! Admission rulings: which reason a declined call gets, and that the
//! decision comes before any device work. In its own test binary (it sets
//! the minimum size).

use midnight_gpu::{self as gpu, Scalar, abi::QuotientJobAbi, field};

fn count(class: &str, reason: &str) -> u64 {
    gpu::declines()
        .iter()
        .filter(|d| d.0 == class && d.1 == reason)
        .map(|d| d.2)
        .sum()
}

/// A quotient job header: `2^k` rows, `2^ext_k` extended, coset shift
/// `[z, z^2]` in and `[z^2, z]` out. The rest is zero (it fails the full
/// check before any pointer is read).
fn job(k: u32, ext_k: u32, z: Scalar) -> QuotientJobAbi {
    // SAFETY: a plain repr(C) struct of integers and pointers; zero is valid.
    let mut j: QuotientJobAbi = unsafe { std::mem::zeroed() };
    j.abi = gpu::abi::QUOTIENT_ABI;
    (j.k, j.ext_k) = (k, ext_k);
    let z2 = field::square(&z);
    j.zeta = [z, z2];
    j.zeta_out = [z2, z];
    j
}

/// Runs the quotient on `j` (or a null job) and returns the reason it
/// declined; the output stays untouched.
fn quotient_reason(j: Option<&QuotientJobAbi>) -> &'static str {
    const REASONS: [&str; 6] = [
        "shape",
        "below-min-k",
        "no-device",
        "unreduced",
        "memory",
        "device-error",
    ];
    let before: Vec<u64> = REASONS.iter().map(|r| count("quotient", r)).collect();
    let mut out = vec![[7u64; 4]; 8];
    let p = j.map_or(std::ptr::null(), |j| {
        j as *const _ as *const std::ffi::c_void
    });
    // SAFETY: a null job, or a header whose counts are zero and whose
    // checks fail before any pointer is read.
    assert!(!unsafe { gpu::quotient::quotient(p, &mut out) });
    assert!(
        out.iter().all(|v| *v == [7u64; 4]),
        "the output is untouched"
    );
    let fired: Vec<&str> = REASONS
        .iter()
        .zip(&before)
        .filter(|(r, b)| count("quotient", r) != **b)
        .map(|(r, _)| *r)
        .collect();
    assert_eq!(fired.len(), 1, "one counted reason: {fired:?}");
    fired[0]
}

#[test]
fn rulings() {
    // ORACLE-28: the MSM ceiling, on lengths alone
    gpu::set_min_k(14);
    for n in [(1usize << 28) + 1, 1 << 29] {
        assert_eq!(gpu::msm_admission(n, n, 28), Err("shape"), "{n}");
    }
    assert_eq!(gpu::msm_admission(1 << 28, 1 << 28, 28), Ok(()));
    assert_eq!(gpu::msm_admission(5, 6, 28), Err("shape"));
    // a one-point MSM is a value case, not a shape
    assert_eq!(gpu::msm_admission(1, 1, 28), Err("below-min-k"));
    gpu::set_min_k(0);
    assert_eq!(gpu::msm_admission(1, 1, 28), Ok(()));

    // ORACLE-27 / ORACLE-31: a one-element NTT or inverse NTT is `shape`,
    // before the minimum size and before the device check (the same in the
    // stub and with the CUDA core)
    for min_k in [0, 14] {
        assert!(gpu::set_min_k(min_k));
        let errors = gpu::stats().device_errors;
        let (shape, small, none) = (
            count("ntt", "shape"),
            count("ntt", "below-min-k"),
            count("ntt", "no-device"),
        );
        let mut a: Vec<Scalar> = vec![field::from_u64(9)];
        assert!(!gpu::fft(&mut a, field::one(), 0));
        assert!(!gpu::ifft(&mut a, field::one(), 0, field::one()));
        assert_eq!(a, vec![field::from_u64(9)], "the input is untouched");
        assert_eq!(
            count("ntt", "shape"),
            shape + 2,
            "min_k {min_k}: fft and ifft"
        );
        assert_eq!(count("ntt", "below-min-k"), small, "min_k {min_k}");
        assert_eq!(count("ntt", "no-device"), none, "min_k {min_k}");
        assert_eq!(gpu::stats().device_errors, errors, "no device call");
    }

    // audit r2 (b): a minimum above MAX_EXT_K is refused, the old value stays
    assert!(gpu::set_min_k(5));
    assert!(!gpu::set_min_k(gpu::MAX_EXT_K + 1));
    assert!(!gpu::set_min_k(u32::MAX));
    assert_eq!(gpu::min_k(), 5, "the refused value is not stored");
    let small = count("ntt", "below-min-k");
    let mut a: Vec<Scalar> = vec![field::from_u64(3); 1 << 3];
    assert!(!gpu::fft(&mut a, field::one(), 3));
    assert_eq!(count("ntt", "below-min-k"), small + 1, "2^3 is below 2^5");
    // 2^6 is admitted by size: with the refused minimum it would decline
    // as below-min-k
    let mut a: Vec<Scalar> = vec![field::from_u64(3); 1 << 6];
    let _ = gpu::fft(&mut a, field::one(), 6);
    assert_eq!(
        count("ntt", "below-min-k"),
        small + 1,
        "2^6 passes the size gate"
    );
    assert!(gpu::set_min_k(gpu::MAX_EXT_K), "the top value is accepted");

    // ORACLE-06: the shift takes precedence over the size gate, at every
    // minimum; ORACLE-32: the header reasons come before the device check,
    // so the stub gives the device path's reasons
    let z = field::primitive_cube_root();
    let two = field::from_u64(2);
    for min_k in [1, 14] {
        assert!(gpu::set_min_k(min_k));
        assert_eq!(
            quotient_reason(Some(&job(3, 5, two))),
            "shape",
            "min_k {min_k}"
        );
    }
    assert!(gpu::set_min_k(14));
    assert_eq!(quotient_reason(None), "shape", "a null job");
    let mut bad = job(3, 5, z);
    bad.abi = gpu::abi::QUOTIENT_ABI + 1;
    assert_eq!(quotient_reason(Some(&bad)), "shape", "another ABI version");
    assert_eq!(
        quotient_reason(Some(&job(6, 5, z))),
        "shape",
        "k above ext_k"
    );
    assert_eq!(quotient_reason(Some(&job(3, 5, z))), "below-min-k");
    // oracle audit r4: k = 0 is one counted `shape` decline at every minimum
    // (before the size gate and the device), never a device error or a
    // fallback, and the output is left for the stock code
    for min_k in [1, 14] {
        assert!(gpu::set_min_k(min_k));
        let errors = gpu::stats().device_errors;
        let shape = count("quotient", "shape");
        assert_eq!(
            quotient_reason(Some(&job(0, 1, z))),
            "shape",
            "k = 0, min_k {min_k}"
        );
        assert_eq!(count("quotient", "shape"), shape + 1, "one decline");
        assert_eq!(gpu::stats().device_errors, errors, "no fallback");
    }
    assert!(gpu::set_min_k(14));
    // a header that passes: the stub has no device; the CUDA core goes on to
    // the full check, which this zeroed job fails (`shape`)
    let want = if gpu::device() { "shape" } else { "no-device" };
    assert_eq!(quotient_reason(Some(&job(15, 16, z))), want);
}
