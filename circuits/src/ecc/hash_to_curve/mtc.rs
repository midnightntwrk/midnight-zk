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

//! Map to curve in-circuit implementations.

use ff::{Field, PrimeField};
use midnight_proofs::{circuit::Layouter, plonk::Error};

use super::{
    mtc_cpu::MapToCurveCPU,
    mtc_params::{MapToEdwardsParams, MapToWeierstrassParams},
};
use crate::{
    ecc::{
        curves::{CircuitCurve, EdwardsCurve},
        native::{AssignedNativePoint, EccChip},
    },
    instructions::{
        BinaryInstructions, DecompositionInstructions, EccInstructions, EqualityInstructions,
        FieldInstructions,
    },
    types::{AssignedBit, InnerConstants, InnerValue, Instantiable},
};

/// The set of in-circuit instructions for map-to-curve.
pub trait MapToCurveInstructions<F, C>: EccInstructions<F, C>
where
    F: PrimeField,
    C: CircuitCurve + MapToCurveCPU<C>,
{
    /// Map an element of the base field (a coordinate) to a pair of coordinates
    /// that satisfy the underlying curve equation.
    fn map_to_curve(
        &self,
        layouter: &mut impl Layouter<F>,
        u: &Self::Coordinate,
    ) -> Result<Self::Point, Error>;
}

impl<C> MapToCurveInstructions<C::Base, C> for EccChip<C>
where
    C: EdwardsCurve + MapToCurveCPU<C> + MapToEdwardsParams<C::Base>,
{
    fn map_to_curve(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        u: &Self::Coordinate,
    ) -> Result<AssignedNativePoint<C>, Error> {
        let (weierstrass_x, weierstrass_y) = svdw_map_to_weierstrass::<C::Base, C, Self::Coordinate>(
            layouter,
            self.base_field(),
            self.native_gadget(),
            u,
        )?;

        let (montgomery_x, montgomery_y) = weierstrass_to_montgomery::<C::Base, C, Self::Coordinate>(
            layouter,
            self.base_field(),
            &weierstrass_x,
            &weierstrass_y,
        )?;

        let (edwards_x, edwards_y) = montgomery_to_edwards::<C::Base, C, Self::Coordinate>(
            layouter,
            self.base_field(),
            &montgomery_x,
            &montgomery_y,
        )?;

        let point = self.point_from_coordinates(layouter, &edwards_x, &edwards_y)?;
        self.mul_by_constant(layouter, C::Scalar::from_u128(C::COFACTOR), &point)
    }
}

/// Map an element of the base field (a coordinate) to a pair of coordinates
/// that satisfy the underlying Weierstrass equation.
fn svdw_map_to_weierstrass<F, C, T>(
    layouter: &mut impl Layouter<F>,
    base_field: &impl DecompositionInstructions<F, T>,
    bool_chip: &(impl BinaryInstructions<F> + EqualityInstructions<F, AssignedBit<F>>),
    u: &T,
) -> Result<(T, T), Error>
where
    F: PrimeField,
    C: CircuitCurve + MapToWeierstrassParams<C::Base>,
    T: InnerValue<Element = C::Base> + Instantiable<F> + InnerConstants + Clone,
{
    // SVDW Method for map to curve.

    // 1. tv1 = u^2
    let tv1 = base_field.mul(layouter, u, u, None)?;
    // 2. tv1 = tv1 * c1
    let tv1 = base_field.mul_by_constant(layouter, &tv1, C::c1())?;
    // 3. tv2 = 1 + tv1
    let tv2 = base_field.add_constant(layouter, &tv1, C::Base::ONE)?;
    // 4. tv1 = 1 - tv1
    let tv1 = base_field.linear_combination(layouter, &[(-C::Base::ONE, tv1)], C::Base::ONE)?;
    // 5. tv3 = tv1 * tv2
    let tv3 = base_field.mul(layouter, &tv1, &tv2, None)?;
    // 6. tv3 = inv0(tv3)
    let tv3 = base_field.inv0(layouter, &tv3)?;
    // 7. tv4 = u * tv1
    let tv4 = base_field.mul(layouter, u, &tv1, None)?;
    // 8. tv4 = tv4 * tv3
    let tv4 = base_field.mul(layouter, &tv4, &tv3, None)?;
    // 9. tv4 = tv4 * c3
    let tv4 = base_field.mul_by_constant(layouter, &tv4, C::c3())?;
    // 10. x1 = c2 - tv4
    let x1 = base_field.linear_combination(layouter, &[(-C::Base::ONE, tv4.clone())], C::c2())?;
    // 11. gx1 = x1^2
    let gx1 = base_field.mul(layouter, &x1, &x1, None)?;
    // 12. gx1 = gx1 + A
    let gx1 = base_field.add_constant(layouter, &gx1, C::A)?;
    // 13. gx1 = gx1 * x1
    let gx1 = base_field.mul(layouter, &gx1, &x1, None)?;
    // 14. gx1 = gx1 + B
    let gx1 = base_field.add_constant(layouter, &gx1, C::B)?;
    // 15. e1 = is_square(gx1)
    let e1 = base_field.is_square(layouter, &gx1)?;

    // 16. x2 = c2 + tv4
    let x2 = base_field.add_constant(layouter, &tv4, C::c2())?;
    // 17. gx2 = x2^2
    let gx2 = base_field.mul(layouter, &x2, &x2, None)?;
    // 18. gx2 = gx2 + A
    let gx2 = base_field.add_constant(layouter, &gx2, C::A)?;
    // 19. gx2 = gx2 * x2
    let gx2 = base_field.mul(layouter, &gx2, &x2, None)?;
    // 20. gx2 = gx2 + B
    let gx2 = base_field.add_constant(layouter, &gx2, C::B)?;
    // 21. e2 = is_square(gx2) AND NOT e1     # Avoid short-circuit logic ops
    let e2 = {
        let e2 = base_field.is_square(layouter, &gx2)?;
        let not_e1 = bool_chip.not(layouter, &e1)?;
        bool_chip.and(layouter, &[e2, not_e1])?
    };

    // 22. x3 = tv2^2
    let x3 = base_field.mul(layouter, &tv2, &tv2, None)?;
    // 23. x3 = x3 * tv3
    let x3 = base_field.mul(layouter, &x3, &tv3, None)?;
    // 24. x3 = x3^2
    let x3 = base_field.mul(layouter, &x3, &x3, None)?;
    // 25. x3 = x3 * c4
    let x3 = base_field.mul_by_constant(layouter, &x3, C::c4())?;
    // 26. x3 = x3 + Z
    let x3 = base_field.add_constant(layouter, &x3, C::SVDW_Z)?;

    // 27. x = CMOV(x3, x1, e1)      # x = x1 if gx1 is square, else x = x3
    let x = base_field.select(layouter, &e1, &x1, &x3)?;
    // 28. x = CMOV(x, x2, e2)       # x = x2 if gx2 is square and gx1 is not
    let x = base_field.select(layouter, &e2, &x2, &x)?;

    // 29. gx = x^2
    let gx = base_field.mul(layouter, &x, &x, None)?;
    // 30. gx = gx + A
    let gx = base_field.add_constant(layouter, &gx, C::A)?;
    // 31. gx = gx * x
    let gx = base_field.mul(layouter, &gx, &x, None)?;
    // 32. gx = gx + B
    let gx = base_field.add_constant(layouter, &gx, C::B)?;
    // 33. y = sqrt(gx)
    let y = {
        let y_val = gx.value().map(|gx| {
            gx.sqrt()
                .expect("gx should be a quadratic residue but is not.")
        });
        let y = base_field.assign(layouter, y_val)?;
        let y_square = base_field.mul(layouter, &y, &y, None)?;
        base_field.assert_equal(layouter, &y_square, &gx)?;
        y
    };
    // 34. e3 = sgn0(u) == sgn0(y)
    let e3 = {
        let sgn0_u = base_field.sgn0(layouter, u)?;
        let sgn0_y = base_field.sgn0(layouter, &y)?;
        bool_chip.is_equal(layouter, &sgn0_u, &sgn0_y)?
    };
    // 35. y = CMOV(-y, y, e3)       # Select correct sign of y
    let y = {
        let minus_y = base_field.neg(layouter, &y)?;
        base_field.select(layouter, &e3, &y, &minus_y)?
    };

    Ok((x, y))
}

/// Maps a pair of Weierstrass coordinates into Montgomery form.
fn weierstrass_to_montgomery<F, C, T>(
    layouter: &mut impl Layouter<F>,
    base_field: &impl FieldInstructions<F, T>,
    x: &T,
    y: &T,
) -> Result<(T, T), Error>
where
    F: PrimeField,
    C: CircuitCurve + MapToEdwardsParams<C::Base>,
    T: InnerValue<Element = C::Base> + Instantiable<F> + InnerConstants + Clone,
{
    // x' = MONT_K * x - MONT_J / 3
    let tv1 = base_field.mul_by_constant(layouter, x, C::MONT_K)?;
    let x_prime = base_field.add_constant(
        layouter,
        &tv1,
        -C::MONT_J * C::Base::from(3).invert().unwrap(),
    )?;

    // y' = MONT_K * y
    let y_prime = base_field.mul_by_constant(layouter, y, C::MONT_K)?;

    Ok((x_prime, y_prime))
}

/// Maps a pair of coordinates in Montgomery form into Edwards coordinates.
fn montgomery_to_edwards<F, C, T>(
    layouter: &mut impl Layouter<F>,
    base_field: &impl FieldInstructions<F, T>,
    x: &T,
    y: &T,
) -> Result<(T, T), Error>
where
    F: PrimeField,
    C: CircuitCurve + MapToEdwardsParams<C::Base>,
    T: InnerValue<Element = C::Base> + Instantiable<F> + InnerConstants + Clone,
{
    // 1. tv1 = s + 1
    let mut tv1 = base_field.add_constant(layouter, x, C::Base::ONE)?;
    // 2. tv2 = tv1 * t
    let mut tv2 = base_field.mul(layouter, &tv1, y, None)?;
    // 3. tv2 = inv0(tv2)
    tv2 = base_field.inv0(layouter, &tv2)?;
    // 4. v = tv2 * tv1
    let mut x_prime = base_field.mul(layouter, &tv2, &tv1, None)?;
    // 5. v = v * s
    x_prime = base_field.mul(layouter, &x_prime, x, None)?;
    // 6. w = tv2 * t
    let mut y_prime = base_field.mul(layouter, &tv2, y, None)?;
    // 7. tv1 = s - 1
    tv1 = base_field.add_constant(layouter, x, -C::Base::ONE)?;
    // 8. w = w * tv1
    y_prime = base_field.mul(layouter, &y_prime, &tv1, None)?;
    // 9. e = tv2 == 0
    let e = base_field.is_zero(layouter, &tv2)?;
    // 10. w = CMOV(w, 1, e)
    let assigned_one = base_field.assign_fixed(layouter, C::Base::ONE)?;
    y_prime = base_field.select(layouter, &e, &assigned_one, &y_prime)?;
    // 11. return (v, w)
    Ok((x_prime, y_prime))
}
