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

//! Foreign-field arithmetic parameters for different emulation scenarios.
//!
//! All the emulation parameters from this file were generated using
//! [scripts/foreign_params_gen.py].

use std::{fmt::Debug, ops::Rem};

use ff::PrimeField;
use halo2curves::{bls12381, bn256, secp256k1};
use num_bigint::{BigInt, BigInt as BI, ToBigInt};
use num_traits::{One, Signed};
use pasta_curves::{pallas, vesta};

use crate::{ecc::curves::CircuitCurve, utils::util::modulus};

/// Trait for configuring a (foreign) FieldChip. These parameters need to be
/// manually optimized for each emulation of field K over native field F.
/// These parameters were generated with our script:
/// `scripts/foreign_params_gen.py`.
pub trait FieldEmulationParams<F: PrimeField, K: PrimeField>:
    Default + Clone + Debug + PartialEq + Eq
{
    /// The logarithm in base 2 (bit length) of the base in which we represent
    /// integers modulo the emulated modulus.
    /// The actual base is 2 powered to this constant.
    const LOG2_BASE: u32;

    /// The number of limbs used to represent a emulated field element.
    /// It must hold base^NB_LIMBS >= emulated_modulus.
    const NB_LIMBS: u32;

    /// Vector of powers of the base, used for the foreign-field identities.
    /// The i-th element must be congruent to base^i modulo the emulated
    /// modulus.
    fn base_powers() -> Vec<BI> {
        let two = BI::from(2);
        let m = &modulus::<K>().to_bigint().unwrap();
        (0..Self::NB_LIMBS)
            .map(|i| two.pow(Self::LOG2_BASE * i).rem(m))
            .collect::<Vec<_>>()
    }

    /// Vector of powers of the base, used for the foreign-field identities.
    /// The (i * nb_limbs + j)-th element must be congruent to base^(i+j) modulo
    /// the emulated modulus.
    fn double_base_powers() -> Vec<BI> {
        let two = BI::from(2);
        let m = &modulus::<K>().to_bigint().unwrap();
        (0..Self::NB_LIMBS)
            .flat_map(|i| {
                (0..Self::NB_LIMBS)
                    .map(|j| two.pow(Self::LOG2_BASE * (i + j)).rem(m))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }

    /// Auxiliary moduli used in the identities. They should be as large as
    /// possible, to maximize their contribution to the lcm bound.
    /// On the other hand, they cannot be excessively large, in order to
    /// guarantee no wrap-around (modulo the native modulus) in the equations.
    fn moduli() -> Vec<BI>;

    /// A bound on the maximum size of the absolute value of limb bounds for
    /// non-well-formed emulated field elements. If such bound is exceeded, the
    /// normalization function can no longer be applied.
    /// We set this value to be base^2 by default. This value is guaranteed to
    /// be supported with the same moduli as those used for the multiplication
    /// gate. Another good choice for this value would be the largest possible
    /// value that allows us to implement the normalization gate with only
    /// one extra auxiliary modulus.
    fn max_limb_bound() -> BI {
        BI::from(2).pow(2 * Self::LOG2_BASE)
    }

    /// Log2 of the limb size of range-checks. This value is different and
    /// independent of base, the size of ModArith limbs.
    const RC_LIMB_SIZE: u32;
}

/// Sanity checks on the parameters for the FieldChip to be sound.
pub(crate) fn check_params<F, K, P>()
where
    F: PrimeField,
    K: PrimeField,
    P: FieldEmulationParams<F, K>,
{
    let m = &modulus::<K>().to_bigint().unwrap();
    let base = BI::from(2).pow(P::LOG2_BASE);
    let nb_limbs = P::NB_LIMBS;

    // The integer represented by limbs [x0, ..., x_{n-1}] is 1 + sum_i base^i xi

    assert!(*m > BI::one());
    assert!(base > BI::one());

    // Assert that we can encode any integer in [Z_m] with [nb_limbs] limbs of size
    // [base].
    assert!(BI::pow(&base, nb_limbs) >= *m);

    let base_powers = P::base_powers();
    let double_base_powers = P::double_base_powers();

    assert_eq!(base_powers.len(), nb_limbs as usize);
    assert_eq!(double_base_powers.len(), (nb_limbs * nb_limbs) as usize);

    let expected_powers = (0..nb_limbs).map(|i| BI::pow(&base, i).rem(m));
    let expected_double_powers = (0..nb_limbs).flat_map(|i| {
        (0..nb_limbs)
            .map(|j| BI::pow(&base, i + j).rem(m))
            .collect::<Vec<_>>()
    });

    // Check that the powers in ModAP are congruent to the expected powers modulo m.
    base_powers
        .iter()
        .chain(double_base_powers.iter())
        .zip(expected_powers.chain(expected_double_powers))
        .for_each(|(b, e)| {
            // The assertion on the base powers being negative can be removed if we
            // generalize the way upper-bounds are computed. ATM they are simply computed by
            // considering the integer represented with all limbs set to (base-1).
            assert!(!BI::is_negative(b));
            assert_eq!(b.rem(m), e.rem(m))
        });
}

/// MultiEmualtionParams.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct MultiEmulationParams {}

/// Implement FieldEmulationParams for any curve that can emulate itself through
/// MultiEmulationParams.
impl<C: CircuitCurve + Default> FieldEmulationParams<C::Scalar, C::Base> for C
where
    MultiEmulationParams: FieldEmulationParams<C::Scalar, C::Base>,
{
    const LOG2_BASE: u32 = MultiEmulationParams::LOG2_BASE;

    const NB_LIMBS: u32 = MultiEmulationParams::NB_LIMBS;

    fn moduli() -> Vec<BigInt> {
        MultiEmulationParams::moduli()
    }

    const RC_LIMB_SIZE: u32 = MultiEmulationParams::RC_LIMB_SIZE;
}

/*
====================================================
Emulated: Vesta's Scalar field (Pallas' Base field)

Native fields supported:
 - Vesta's Base field
 - Vesta's Scalar field (dummy emulation)
====================================================
*/

/// Vesta's Base field over Vesta's Scalar field.
impl FieldEmulationParams<vesta::Scalar, vesta::Base> for MultiEmulationParams {
    const LOG2_BASE: u32 = 51;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(124)]
    }
    const RC_LIMB_SIZE: u32 = 14;
}

/// Vesta's Scalar field over Vesta's Scalar field.
impl FieldEmulationParams<vesta::Scalar, vesta::Scalar> for MultiEmulationParams {
    const LOG2_BASE: u32 = 51;

    const NB_LIMBS: u32 = 5;

    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(124)]
    }

    const RC_LIMB_SIZE: u32 = 14;
}

/*
====================================================
Emulated: Secp256k1's Base field

Native fields supported:
 - Vesta's Scalar field
 - Pallas' Scalar field
 - BN254's Scalar field
 - BLS12-381's Scalar field (halo2curves & blstrs)
====================================================
*/

/// Secp256k1's Base field over Vesta's Scalar field.
impl FieldEmulationParams<vesta::Scalar, secp256k1::Fp> for MultiEmulationParams {
    const LOG2_BASE: u32 = 86;
    const NB_LIMBS: u32 = 3;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(86),
            BigInt::from(2).pow(86) - BigInt::from(1),
        ]
    }
    const RC_LIMB_SIZE: u32 = 16;
}

/// Secp256k1's Base field over Pallas' Scalar field.
impl FieldEmulationParams<pallas::Scalar, secp256k1::Fp> for MultiEmulationParams {
    const LOG2_BASE: u32 = 86;
    const NB_LIMBS: u32 = 3;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(86),
            BigInt::from(2).pow(86) - BigInt::from(1),
        ]
    }
    const RC_LIMB_SIZE: u32 = 16;
}

/// Secp256k1's Base field over BN254's Scalar field.
impl FieldEmulationParams<bn256::Fr, secp256k1::Fp> for MultiEmulationParams {
    const LOG2_BASE: u32 = 64;
    const NB_LIMBS: u32 = 4;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(128)]
    }
    const RC_LIMB_SIZE: u32 = 16;
}

/// Secp256k1's Base field over BLS12-381's Scalar field.
impl FieldEmulationParams<bls12381::Fr, secp256k1::Fp> for MultiEmulationParams {
    const LOG2_BASE: u32 = 52;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(156)]
    }
    const RC_LIMB_SIZE: u32 = 16;
}

/// Secp256k1's Base field over BLS12-381's Scalar field.
impl FieldEmulationParams<midnight_curves::Fq, secp256k1::Fp> for MultiEmulationParams {
    const LOG2_BASE: u32 = 64;
    const NB_LIMBS: u32 = 4;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(128)]
    }
    const RC_LIMB_SIZE: u32 = 16;
}

/*
====================================================
Emulated: Secp256k1's Scalar field

Native fields supported:
 - Vesta's Scalar field
 - Pallas' Scalar field
 - BN254's Scalar field
 - BLS12-381's Scalar field (halo2curves & blstrs)
====================================================
*/

/// Secp256k1's Scalar field over Vesta's Scalar field.
impl FieldEmulationParams<vesta::Scalar, secp256k1::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 86;
    const NB_LIMBS: u32 = 3;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(82),
            BigInt::from(2).pow(82) - BigInt::from(52),
        ]
    }
    const RC_LIMB_SIZE: u32 = 15;
}

/// Secp256k1's Scalar field over Pallas' Scalar field.
impl FieldEmulationParams<pallas::Scalar, secp256k1::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 86;
    const NB_LIMBS: u32 = 3;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(82),
            BigInt::from(2).pow(82) - BigInt::from(52),
        ]
    }
    const RC_LIMB_SIZE: u32 = 15;
}

/// Secp256k1's Scalar field over BN254's Scalar field.
impl FieldEmulationParams<bn256::Fr, secp256k1::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 52;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(141)]
    }
    const RC_LIMB_SIZE: u32 = 14;
}

/// Secp256k1's Scalar field over BLS12-381's Scalar field.
impl FieldEmulationParams<bls12381::Fr, secp256k1::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 52;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(142)]
    }
    const RC_LIMB_SIZE: u32 = 14;
}

/// Secp256k1's Scalar field over BLS12-381's Scalar field.
impl FieldEmulationParams<midnight_curves::Fq, secp256k1::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 64;
    const NB_LIMBS: u32 = 4;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(118),
            BigInt::from(2).pow(118) - BigInt::one(),
        ]
    }
    const RC_LIMB_SIZE: u32 = 17;
}

/*
====================================================
Emulated: BLS12-381's Base field

Native fields supported:
 - BLS12-381's Scalar field (halo2curves & blstrs)
====================================================
*/

/// BLS12-381's Base field over BLS12-381's Scalar field.
impl FieldEmulationParams<bls12381::Fr, bls12381::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 56;
    const NB_LIMBS: u32 = 7;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(136),
            BigInt::from(2).pow(136) - BigInt::from(2),
        ]
    }
    const RC_LIMB_SIZE: u32 = 17;
}

/// BLS12-381's Base field over BLS12-381's Scalar field.
impl FieldEmulationParams<midnight_curves::Fq, midnight_curves::Fp> for MultiEmulationParams {
    const LOG2_BASE: u32 = 56;
    const NB_LIMBS: u32 = 7;
    fn moduli() -> Vec<BigInt> {
        vec![
            BigInt::from(2).pow(134),
            BigInt::from(2).pow(134) - BigInt::from(1),
        ]
    }
    const RC_LIMB_SIZE: u32 = 15;
}

/*
====================================================
Emulated: BN254's Base field

Native fields supported:
 - BLS12-381's Scalar field (halo2curves & blstrs)
 - BN254's Scalar field
====================================================
*/

/// BN254's Base field over BLS12-381's Scalar field.
impl FieldEmulationParams<bls12381::Fq, bn256::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 52;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(142)]
    }
    const RC_LIMB_SIZE: u32 = 14;
}

/// BN254's Base field over BLS12-381's Scalar field.
impl FieldEmulationParams<midnight_curves::Fq, bn256::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 52;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(142)]
    }
    const RC_LIMB_SIZE: u32 = 14;
}

/// BN254's Base field over BN254's Scalar field.
impl FieldEmulationParams<bn256::Fr, bn256::Fq> for MultiEmulationParams {
    const LOG2_BASE: u32 = 52;
    const NB_LIMBS: u32 = 5;
    fn moduli() -> Vec<BigInt> {
        vec![BigInt::from(2).pow(141)]
    }
    const RC_LIMB_SIZE: u32 = 14;
}
