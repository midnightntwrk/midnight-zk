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

//! The BLS12-381 scalar field on [`Scalar`] limbs (through `blst`).
//!
//! A [`Scalar`] is a `blst_fr`: four little-endian `u64` limbs of the
//! Montgomery form `a * 2^256 mod r`, reduced (less than [`MODULUS`]). This
//! is the in-memory form of `midnight_curves::Fq`, so slices of it are passed
//! without conversion. Every entry point of this crate that receives scalars
//! checks that they are reduced ([`all_reduced`]) and declines otherwise.

use blst::{
    blst_fr, blst_fr_add, blst_fr_from_uint64, blst_fr_inverse, blst_fr_mul, blst_fr_sqr,
    blst_fr_sub,
};

use crate::Scalar;

/// The modulus `r`, little-endian limbs.
pub const MODULUS: Scalar = [
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];

/// `2^S` is the largest power of two dividing `r - 1`.
pub const S: u32 = 32;

/// The `2^S`-th root of unity of `midnight_curves::Fq` (`ROOT_OF_UNITY`),
/// Montgomery limbs. Its square `S - k` times is the root of the `2^k`
/// domain.
pub const ROOT_OF_UNITY: Scalar = [
    0xb9b5_8d8c_5f0e_466a,
    0x5b1b_4c80_1819_d7ec,
    0x0af5_3ae3_52a3_1e64,
    0x5bf3_adda_19e9_b27b,
];

/// Zero.
pub const ZERO: Scalar = [0; 4];

#[inline]
fn fr(a: &Scalar) -> blst_fr {
    blst_fr { l: *a }
}

/// Whether `a < r`.
#[inline]
pub fn is_reduced(a: &Scalar) -> bool {
    for i in (0..4).rev() {
        if a[i] != MODULUS[i] {
            return a[i] < MODULUS[i];
        }
    }
    false
}

/// Whether every element is reduced (in parallel for long slices).
pub fn all_reduced(a: &[Scalar]) -> bool {
    const PART: usize = 1 << 16;
    if a.len() <= PART {
        return a.iter().all(is_reduced);
    }
    let threads = std::thread::available_parallelism().map_or(4, |t| t.get()).min(16);
    let per = a.len().div_ceil(threads).max(PART);
    std::thread::scope(|s| {
        let hs: Vec<_> = a.chunks(per).map(|c| s.spawn(move || c.iter().all(is_reduced))).collect();
        hs.into_iter().all(|h| h.join().unwrap_or(false))
    })
}

/// `a + b`.
#[inline]
pub fn add(a: &Scalar, b: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: valid pointers to blst_fr values.
    unsafe { blst_fr_add(&mut r, &fr(a), &fr(b)) };
    r.l
}

/// `a - b`.
#[inline]
pub fn sub(a: &Scalar, b: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: as `add`.
    unsafe { blst_fr_sub(&mut r, &fr(a), &fr(b)) };
    r.l
}

/// `a * b`.
#[inline]
pub fn mul(a: &Scalar, b: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: as `add`.
    unsafe { blst_fr_mul(&mut r, &fr(a), &fr(b)) };
    r.l
}

/// `a^2`.
#[inline]
pub fn square(a: &Scalar) -> Scalar {
    let mut r = blst_fr::default();
    // SAFETY: as `add`.
    unsafe { blst_fr_sqr(&mut r, &fr(a)) };
    r.l
}

/// `1 / a` (`None` for zero).
pub fn invert(a: &Scalar) -> Option<Scalar> {
    if *a == ZERO {
        return None;
    }
    let mut r = blst_fr::default();
    // SAFETY: as `add`.
    unsafe { blst_fr_inverse(&mut r, &fr(a)) };
    Some(r.l)
}

/// The element of the integer `v`.
pub fn from_u64(v: u64) -> Scalar {
    let mut r = blst_fr::default();
    let limbs = [v, 0, 0, 0];
    // SAFETY: four readable limbs.
    unsafe { blst_fr_from_uint64(&mut r, limbs.as_ptr()) };
    r.l
}

/// One.
pub fn one() -> Scalar {
    from_u64(1)
}

/// The root of unity of the `2^log_n` domain, as `EvaluationDomain` derives
/// it, and its inverse. `None` for `log_n > S`.
pub fn std_root(log_n: u32) -> Option<(Scalar, Scalar)> {
    if log_n > S {
        return None;
    }
    let mut w = ROOT_OF_UNITY;
    for _ in log_n..S {
        w = square(&w);
    }
    Some((w, invert(&w)?))
}

/// A primitive cube root of unity `z` (`z != 1`, `z^3 = 1`):
/// `g^((r - 1) / 3)` for the first small `g` that does not give one. The
/// quotient takes the shift `[z, z^2]` of a job built from either cube root.
pub fn primitive_cube_root() -> Scalar {
    // (r - 1) / 3 as little-endian limbs (3 divides r - 1)
    let mut e = [0u64; 4];
    let mut m = MODULUS;
    m[0] -= 1;
    let mut rem: u128 = 0;
    for i in (0..4).rev() {
        let cur = (rem << 64) | m[i] as u128;
        e[i] = (cur / 3) as u64;
        rem = cur % 3;
    }
    let pow = |b: &Scalar| {
        let mut acc = one();
        for i in (0..256).rev() {
            acc = square(&acc);
            if (e[i / 64] >> (i % 64)) & 1 == 1 {
                acc = mul(&acc, b);
            }
        }
        acc
    };
    (2..64u64)
        .map(|g| pow(&from_u64(g)))
        .find(|z| *z != one())
        .expect("a small non-cube exists")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roots_and_reduction() {
        assert!(is_reduced(&ZERO));
        assert!(!is_reduced(&MODULUS));
        let mut below = MODULUS;
        below[0] -= 1;
        assert!(is_reduced(&below));
        let (w, wi) = std_root(1).unwrap();
        assert_eq!(mul(&w, &wi), one());
        // the 2-element root is -1
        assert_eq!(add(&w, &one()), ZERO);
        let (w, _) = std_root(S).unwrap();
        assert_eq!(w, ROOT_OF_UNITY);
        let (w, _) = std_root(0).unwrap();
        assert_eq!(w, one());
    }
}
