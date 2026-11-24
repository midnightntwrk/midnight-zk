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

//! Zero-copy views between the BLS12-381 types of `midnight-curves` and the
//! plain limb arrays of the hook API.
//!
//! - [`Scalar`]: a scalar-field element as `blst_fr` holds it: four
//!   little-endian `u64` limbs in Montgomery form (`R = 2^256`), reduced modulo
//!   `r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`.
//! - [`G1AffineLimbs`]: `blst_p1_affine`, the coordinates `x`, `y` as six `u64`
//!   limbs each, Montgomery form (`R = 2^384`); the point at infinity is all
//!   zero.
//! - [`G1JacobianLimbs`]: `blst_p1`, Jacobian `X`, `Y`, `Z`, six limbs each.
//!
//! The `midnight-curves` types are `#[repr(transparent)]` wrappers of these
//! `blst` types, so a slice of them is a slice of limb arrays. The size and
//! alignment checks below fail the build if that ever changes. This module
//! depends only on `midnight-curves`.
#![allow(unsafe_code)]

use midnight_curves::{Fq, G1Affine, G1Projective};

/// A scalar: `blst_fr` limbs, Montgomery form.
pub type Scalar = [u64; 4];
/// An affine G1 point: `blst_p1_affine` limbs.
pub type G1AffineLimbs = [u64; 12];
/// A Jacobian G1 point: `blst_p1` limbs.
pub type G1JacobianLimbs = [u64; 18];

const _: () = {
    assert!(std::mem::size_of::<Fq>() == std::mem::size_of::<Scalar>());
    assert!(std::mem::align_of::<Fq>() == std::mem::align_of::<Scalar>());
    assert!(std::mem::size_of::<G1Affine>() == std::mem::size_of::<G1AffineLimbs>());
    assert!(std::mem::align_of::<G1Affine>() == std::mem::align_of::<G1AffineLimbs>());
    assert!(std::mem::size_of::<G1Projective>() == std::mem::size_of::<G1JacobianLimbs>());
    assert!(std::mem::align_of::<G1Projective>() == std::mem::align_of::<G1JacobianLimbs>());
};

/// The limbs of scalars.
pub fn scalars(a: &[Fq]) -> &[Scalar] {
    // SAFETY: `Fq` is a transparent `blst_fr`, a `repr(C)` `[u64; 4]`; size
    // and alignment are checked above.
    unsafe { &*(a as *const [Fq] as *const [Scalar]) }
}

/// The limbs of scalars, mutable. A write must leave reduced Montgomery
/// limbs.
pub fn scalars_mut(a: &mut [Fq]) -> &mut [Scalar] {
    // SAFETY: as `scalars`.
    unsafe { &mut *(a as *mut [Fq] as *mut [Scalar]) }
}

/// The limbs of one scalar.
pub fn scalar(a: Fq) -> Scalar {
    scalars(std::slice::from_ref(&a))[0]
}

/// The scalar of reduced Montgomery limbs.
pub fn from_scalar(a: Scalar) -> Fq {
    let mut r = Fq::default();
    scalars_mut(std::slice::from_mut(&mut r))[0] = a;
    r
}

/// The limbs of affine points.
pub fn affine(a: &[G1Affine]) -> &[G1AffineLimbs] {
    // SAFETY: `G1Affine` is a transparent `blst_p1_affine`, `repr(C)` of two
    // `[u64; 6]`; size and alignment are checked above.
    unsafe { &*(a as *const [G1Affine] as *const [G1AffineLimbs]) }
}

/// The point of Jacobian limbs (`blst_p1` layout, a point on the curve).
pub fn from_jacobian(a: G1JacobianLimbs) -> G1Projective {
    // SAFETY: `G1Projective` is a transparent `blst_p1`, `repr(C)` of three
    // `[u64; 6]`; size and alignment are checked above.
    unsafe { std::mem::transmute::<G1JacobianLimbs, G1Projective>(a) }
}

/// The limbs of a Jacobian point.
pub fn jacobian(a: &G1Projective) -> G1JacobianLimbs {
    // SAFETY: as `from_jacobian`.
    unsafe { std::mem::transmute::<G1Projective, G1JacobianLimbs>(*a) }
}

#[cfg(test)]
mod tests {
    use ff::{Field, PrimeField};
    use group::{Curve, Group, prime::PrimeCurveAffine};

    use super::*;

    #[test]
    fn limbs_round_trip() {
        let a = Fq::from(5u64) * Fq::ROOT_OF_UNITY;
        assert_eq!(from_scalar(scalar(a)), a);
        assert_eq!(scalar(Fq::ZERO), [0; 4]);
        // Montgomery form: 1 is R mod r, not 1
        assert_ne!(scalar(Fq::ONE), [1, 0, 0, 0]);
        let g = G1Projective::generator() * Fq::from(7u64);
        assert_eq!(from_jacobian(jacobian(&g)), g);
        let ga = [g.to_affine(), G1Affine::identity()];
        let l = affine(&ga);
        assert_eq!(l[1], [0; 12]);
        assert_eq!(l.as_ptr() as usize, ga.as_ptr() as usize);
    }
}
