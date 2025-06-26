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

//! Map to curve parameter traits and implementations.

use blstrs::{Fq as JubjubBase, JubjubExtended as Jubjub};
use ff::PrimeField;

/// Constants for the Shallue-van de Woestijne (SVDW) map to Weierstrass curve.
pub trait MapToWeierstrassParams<BaseField: PrimeField> {
    /// Z constant of the SVDW method.
    const SVDW_Z: BaseField;

    /// Parameter `a` in the curve equation `y^2 = x^3 + a*x + b`.
    const A: BaseField;

    /// Parameter `b` in the curve equation `y^2 = x^3 + a*x + b`.
    const B: BaseField;

    /// Right-hand side evaluation of the curve equation.
    fn g(x: BaseField) -> BaseField {
        x * x * x + Self::A * x + Self::B
    }

    /// g(Z).
    fn c1() -> BaseField {
        Self::g(Self::SVDW_Z)
    }

    /// -Z / 2.
    fn c2() -> BaseField {
        -Self::SVDW_Z * BaseField::TWO_INV
    }

    /// sqrt(-g(Z) * (3 * Z^2 + 4 * A)) with zero sgn0.
    fn c3() -> BaseField {
        let den =
            BaseField::from(3u64) * Self::SVDW_Z * Self::SVDW_Z + BaseField::from(4u64) * Self::A;
        let a = -Self::c1() * den;
        let sqrt = a
            .sqrt()
            .expect("This value should be a quadratic residue. Check SVDW_Z parameter.");
        if bool::from(sqrt.is_even()) {
            sqrt
        } else {
            -sqrt
        }
    }

    /// -4 * g(Z) / (3 * Z^2 + 4 * A).
    fn c4() -> BaseField {
        let four = BaseField::from(4u64);
        let det = BaseField::from(3u64) * Self::SVDW_Z * Self::SVDW_Z + four * Self::A;
        -four * Self::c1() * (det.invert().unwrap())
    }
}

/// Constants for the Shallue-van de Woestijne (SVDW) map to twisted Edwards
/// curve, through Montgomery form.
pub trait MapToEdwardsParams<BaseField: PrimeField>: MapToWeierstrassParams<BaseField> {
    /// `J` constant of Montgomery curve: `K * y^2 = x^3 + J * x^2 + x`.
    const MONT_J: BaseField;

    /// `K` constant of Montgomery curve: `K * y^2 = x^3 + J * x^2 + x`.
    const MONT_K: BaseField;
}

// The script about deriving these constants can be found:
// `scripts/hash_to_jubjub_params.sage`
impl MapToWeierstrassParams<JubjubBase> for Jubjub {
    const SVDW_Z: JubjubBase = JubjubBase::from_raw([
        0xfffffffeffffffff,
        0x53bda402fffe5bfe,
        0x3339d80809a1d805,
        0x73eda753299d7d48,
    ]);

    const A: JubjubBase = JubjubBase::from_raw([
        0xc50d34dcd4c20942,
        0x20535e745e639334,
        0x976220a0378a2328,
        0x739e8acf6e7266e8,
    ]);

    const B: JubjubBase = JubjubBase::from_raw([
        0x7120c33b4c6628e1,
        0xbbf51483ff8366ac,
        0xf4c60001b55614b0,
        0x6ae5ca3c3f667667,
    ]);
}

impl MapToEdwardsParams<JubjubBase> for Jubjub {
    const MONT_J: JubjubBase = JubjubBase::from_raw([
        0x000000000000a002,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
    ]);

    const MONT_K: JubjubBase = JubjubBase::from_raw([
        0xfffffffeffff5ffd,
        0x53bda402fffe5bfe,
        0x3339d80809a1d805,
        0x73eda753299d7d48,
    ]);
}

#[cfg(test)]
mod test {
    use ff::Field;

    use super::*;
    use crate::ecc::curves::CircuitCurve;

    fn test_params<C>()
    where
        C: CircuitCurve + MapToWeierstrassParams<C::Base>,
    {
        // g(Z) != 0.
        assert_ne!(C::c1(), C::Base::ZERO);

        // -(3 * Z^2 + 4 * A) / (4 * g(Z)) != 0.
        assert_ne!(C::c4(), C::Base::ZERO);

        // -(3 * Z^2 + 4 * A) / (4 * g(Z)) is square.
        assert!(bool::from(C::c4().sqrt().is_some()));

        // At least one of g(Z) and g(-Z / 2) is square.
        assert!(bool::from(C::c1().sqrt().is_some()) | bool::from(C::g(C::c2()).sqrt().is_some()));

        // C3 is the "positive" solution of the square root.
        assert!(bool::from(C::c3().is_even()));
    }

    #[test]
    fn test_jubjub_params() {
        test_params::<Jubjub>()
    }
}
