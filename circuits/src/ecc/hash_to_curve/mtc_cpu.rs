// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

//! Map to curve off-circuit implementations.

use ff::{Field, PrimeField};
use group::cofactor::CofactorGroup;
use halo2curves::ff_ext::Legendre;
use midnight_curves::{JubjubExtended as Jubjub, JubjubSubgroup};
use subtle::{ConditionallySelectable, ConstantTimeEq};

// use crate::instructions::ecc::EdwardsCurve;
use super::mtc_params::{MapToEdwardsParams, MapToWeierstrassParams};
use crate::ecc::curves::CircuitCurve;

/// The set of off-circuit instructions for map-to-curve.
pub trait MapToCurveCPU<C: CircuitCurve> {
    /// Map an element of the base field (a coordinate) to a pair of coordinates
    /// that satisfy the underlying curve equation.
    fn map_to_curve(u: &C::Base) -> C::CryptographicGroup;
}

impl MapToCurveCPU<Jubjub> for Jubjub {
    fn map_to_curve(u: &<Jubjub as CircuitCurve>::Base) -> JubjubSubgroup {
        let (x, y) = svdw_map_to_curve::<Jubjub>(u);
        let (x, y) = weierstrass_to_montgomery::<Jubjub>(&x, &y);
        let (x, y) = montgomery_to_edwards::<Jubjub>(&x, &y);
        let extended_point = Jubjub::from_xy(x, y).unwrap();
        <Jubjub as CofactorGroup>::clear_cofactor(&extended_point)
    }
}

/// Map to Curve function.
/// Adapted from halo2curves:
/// <https://github.com/privacy-scaling-explorations/halo2curves/blob/9fff22c5f72cc54fac1ef3a844e1072b08cfecdf/src/hash_to_curve.rs#L197>
fn svdw_map_to_curve<C>(u: &C::Base) -> (C::Base, C::Base)
where
    C: CircuitCurve + MapToWeierstrassParams<C::Base>,
    C::Base: Legendre,
{
    // 1. tv1 = u^2
    let tv1 = u.square();
    // 2. tv1 = tv1 * c1
    let tv1 = tv1 * C::c1();
    // 3. tv2 = 1 + tv1
    let tv2 = C::Base::ONE + tv1;
    // 4. tv1 = 1 - tv1
    let tv1 = C::Base::ONE - tv1;
    // 5. tv3 = tv1 * tv2
    let tv3 = tv1 * tv2;
    // 6. tv3 = inv0(tv3)
    let tv3 = tv3.invert().unwrap_or(C::Base::ZERO);
    // 7. tv4 = u * tv1
    let tv4 = *u * tv1;
    // 8. tv4 = tv4 * tv3
    let tv4 = tv4 * tv3;
    // 9. tv4 = tv4 * c3
    let tv4 = tv4 * C::c3();
    // 10. x1 = c2 - tv4
    let x1 = C::c2() - tv4;
    // 11. gx1 = x1^2
    let gx1 = x1.square();
    // 12. gx1 = gx1 + A
    let gx1 = gx1 + C::A;
    // 13. gx1 = gx1 * x1
    let gx1 = gx1 * x1;
    // 14. gx1 = gx1 + B
    let gx1 = gx1 + C::B;
    // 15. e1 = is_square(gx1)
    let e1 = !gx1.ct_quadratic_non_residue();
    // 16. x2 = c2 + tv4
    let x2 = C::c2() + tv4;
    // 17. gx2 = x2^2
    let gx2 = x2.square();
    // 18. gx2 = gx2 + A
    let gx2 = gx2 + C::A;
    // 19. gx2 = gx2 * x2
    let gx2 = gx2 * x2;
    // 20. gx2 = gx2 + B
    let gx2 = gx2 + C::B;
    // 21. e2 = is_square(gx2) AND NOT e1    # Avoid short-circuit logic ops
    let e2 = !gx2.ct_quadratic_non_residue() & (!e1);
    // 22. x3 = tv2^2
    let x3 = tv2.square();
    // 23. x3 = x3 * tv3
    let x3 = x3 * tv3;
    // 24. x3 = x3^2
    let x3 = x3.square();
    // 25. x3 = x3 * c4
    let x3 = x3 * C::c4();
    // 26. x3 = x3 + Z
    let x3 = x3 + C::SVDW_Z;
    // 27. x = CMOV(x3, x1, e1)    # x = x1 if gx1 is square, else x = x3
    let x = C::Base::conditional_select(&x3, &x1, e1);
    // 28. x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
    let x = C::Base::conditional_select(&x, &x2, e2);
    // 29. gx = x^2
    let gx = x.square();
    // 30. gx = gx + A
    let gx = gx + C::A;
    // 31. gx = gx * x
    let gx = gx * x;
    // 32. gx = gx + B
    let gx = gx + C::B;
    // 33. y = sqrt(gx)
    let y = gx.sqrt().unwrap();
    // 34. e3 = sgn0(u) == sgn0(y)
    let e3 = u.is_odd().ct_eq(&y.is_odd());
    // 35. y = CMOV(-y, y, e3)    # Select correct sign of y
    let y = C::Base::conditional_select(&-y, &y, e3);
    // 36. return (x, y)
    (x, y)
}

/// Maps a pair of Weierstrass coordinates into Montgomery form.
fn weierstrass_to_montgomery<C>(x: &C::Base, y: &C::Base) -> (C::Base, C::Base)
where
    C: CircuitCurve + MapToEdwardsParams<C::Base>,
{
    let x_prime = *x * C::MONT_K;
    let x_prime = x_prime - C::MONT_J * C::Base::from(3).invert().unwrap();
    let y_prime = *y * C::MONT_K;

    (x_prime, y_prime)
}

/// Maps a pair of coordinates in Montgomery form into Edwards coordinates.
fn montgomery_to_edwards<C>(x: &C::Base, y: &C::Base) -> (C::Base, C::Base)
where
    C: CircuitCurve + MapToEdwardsParams<C::Base>,
{
    // 1. tv1 = s + 1
    let mut tv1 = *x + C::Base::ONE;
    // 2. tv2 = tv1 * t
    let mut tv2 = tv1 * *y;
    // 3. tv2 = inv0(tv2)
    tv2 = tv2.invert().unwrap_or(C::Base::ZERO);
    // 4. v = tv2 * tv1
    let mut x_prime = tv2 * tv1;
    // 5. v = v * s
    x_prime *= *x;
    // 6. w = tv2 * t
    let mut y_prime = tv2 * *y;
    // 7. tv1 = s - 1
    tv1 = *x - C::Base::ONE;
    // 8. w = w * tv1
    y_prime *= tv1;
    // 9. e = t2 == 0
    let e = tv2 == C::Base::ZERO;
    // 10. w = CMOV(w, 1, e)
    y_prime = C::Base::conditional_select(&y_prime, &C::Base::ONE, (e as u8).into());
    // 11. return (v, w)
    (x_prime, y_prime)
}
