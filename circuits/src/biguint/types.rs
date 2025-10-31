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

use std::cmp::max;

use ff::PrimeField;
use midnight_proofs::circuit::Value;
use num_bigint::BigUint;
use num_traits::{One, Zero};

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::Sampleable;
use crate::{
    field::foreign::util::{big_from_limbs, big_to_limbs},
    types::{AssignedNative, InnerConstants, InnerValue},
    utils::util::{big_to_fe, fe_to_big},
};

/// The logarithm of the base of representation `BASE := 2^LOG2_BASE`.
// This number should be lower than `F::NUM_BITS / 2` over native field `F`.
// Indeed, it must be lower than that amount with some extra room for
// "computing". For example, with a 256-bits field, this number is not
// recommended to exceed 120.
//
// In general, a good choice for the value of LOG2_BASE is a multiple of
// `MAX_BIT_LEN * ZkStdLibArch::nr_pow2range_cols` where the former is the
// table size of the native_gadget range-checks and the latter the number of
// columns dedicated to such lookup. Here, we pick a multiple of 8 * 4 = 32.
pub(crate) const LOG2_BASE: u32 = 96;

/// Type for assigned big unsigned integers, emulated over native field `F`.
///  - `limbs` is a little-endian vector of assigned native values representing
///    the big unsigned integer in base `BASE`.
///
///    We allow the limbs to be non-normalized, i.e., they do not necessarily
///    need to be in the range `[0, BASE)`. However, we keep track of an
///    upper-bound on their size.
///
///  - `limb_size_bounds` is a vector (of the same length as `limbs`) containing
///    an upper-bound on the size the respective limb. That is, `limbs[i]` is
///    guaranteed to be in `[0, 1 << limb_size_bounds[i])`, for every `i`.
///
/// NOTE: Do not implement `AssignmentInstructions` for this type.
/// `AssignedBigUint`s should be constructed with a known bound on their size.
/// We provided dedicated methods `assign_biguint` and `assign_fixed_biguint`
/// for this.
///
/// Similarly, do not implement `PublicInputInstructions` for this type.
/// Use `constrain_as_public_input` instead.
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedBigUint<F: PrimeField> {
    pub(crate) limbs: Vec<AssignedNative<F>>,
    pub(crate) limb_size_bounds: Vec<u32>,
}

impl<F: PrimeField> InnerValue for AssignedBigUint<F> {
    type Element = BigUint;

    fn value(&self) -> Value<BigUint> {
        let base = BigUint::one() << LOG2_BASE;
        let limbs_as_big = self.limbs.iter().map(|l| l.value().copied().map(fe_to_big));
        let value: Value<Vec<BigUint>> = Value::from_iter(limbs_as_big);
        value.map(|limbs| big_from_limbs(&base, &limbs))
    }
}

impl<F: PrimeField> InnerConstants for AssignedBigUint<F> {
    fn inner_zero() -> BigUint {
        BigUint::zero()
    }

    fn inner_one() -> Self::Element {
        BigUint::one()
    }
}

impl<F: PrimeField> AssignedBigUint<F> {
    /// This function is the off-circuit analog of
    /// [crate::biguint::biguint_gadget::BigUintGadget::constrain_as_public_input].
    pub fn as_public_input(element: &BigUint, nb_bits: u32) -> Vec<F> {
        biguint_to_limbs(element, Some(nb_bits.div_ceil(LOG2_BASE)))
    }
}

#[cfg(any(test, feature = "testing"))]
pub(crate) const TEST_NB_BITS: u32 = 1024;

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> Sampleable for AssignedBigUint<F> {
    fn sample_inner(mut rng: impl rand::RngCore) -> BigUint {
        num_bigint::RandBigInt::gen_biguint(&mut rng, TEST_NB_BITS as u64)
    }
}

impl<F: PrimeField> AssignedBigUint<F> {
    /// Returns an upper-bound on the number of bits necessary to represent the
    /// given big unsigned integer. Such bound is computed based on the
    /// `AssignedBigUint` limb size bounds.
    ///
    /// This function does not simply return `nb_limbs * LOG2_BASE` because it
    /// can also deal with big unsigned integers that are not normalized i.e.
    /// whose bounds are allowed to exceed LOG2_BASE.
    pub fn nb_bits(&self) -> u32 {
        self.limb_size_bounds
            .iter()
            .rev()
            .fold(BigUint::zero(), |acc, bound| {
                (acc << LOG2_BASE) + (BigUint::one() << bound) - BigUint::one()
            })
            .bits() as u32
    }

    /// Returns `true` iff all the limb bounds of this `AssignedBigUint` are
    /// lower than or equal to LOG2_BASE.
    pub fn is_normalized(&self) -> bool {
        self.limb_size_bounds.iter().all(|bound| *bound <= LOG2_BASE)
    }
}

/// Given bounds which limit the size of two integers, returns a bound on the
/// size of their sum. Concretely, it returns the smallest integer `bound` such
/// that the sum of an integer in the range `[0, 2^bound1)` with an integer in
/// the range `[0, 2^bound2)` is guaranteed to be in the range `[0, 2^bound)`.
pub(crate) fn bound_of_addition(bound1: u32, bound2: u32) -> u32 {
    if bound1 == 0 {
        return bound2;
    }

    if bound2 == 0 {
        return bound1;
    }

    1 + max(bound1, bound2)
}

/// Breaks the given BigUint into `nb_limbs` limbs (over the underlying prime
/// field) representing the value in base 2^LOG2_BASE (in little-endian).
///
/// If not provided, `nb_limbs` will default to the minimum number of limbs
/// necessary to represent the given integer.
///
/// If `nb_limbs` is provided, this function will panic if the conversion is not
/// possible.
pub(crate) fn biguint_to_limbs<F: PrimeField>(value: &BigUint, nb_limbs: Option<u32>) -> Vec<F> {
    let nb_limbs = nb_limbs.unwrap_or(value.bits().div_ceil(LOG2_BASE as u64) as u32);
    big_to_limbs(nb_limbs, &(BigUint::from(1u8) << LOG2_BASE), value)
        .into_iter()
        .map(big_to_fe::<F>)
        .collect()
}

#[cfg(feature = "extraction")]
pub mod extraction {
    //! Extraction specific logic related to the biguint gadget.
    use std::{borrow::Borrow, ops::Rem as _};

    use extractor_support::{
        cell_to_expr,
        cells::{
            ctx::{ICtx, OCtx},
            load::LoadFromCells,
            store::StoreIntoCells,
            CellReprSize,
        },
        circuit::injected::InjectedIR,
        error::Error,
        ir::{stmt::IRStmt, CmpOp},
    };
    use ff::PrimeField;
    use midnight_proofs::{circuit::Layouter, plonk::Expression};

    use super::{AssignedBigUint, LOG2_BASE};
    use crate::types::AssignedNative;

    const fn num_limbs(bits: usize) -> usize {
        let c: usize = bits / LOG2_BASE as usize;
        if bits % LOG2_BASE as usize != 0 {
            c + 1
        } else {
            c
        }
    }

    /// Represents a big unsigned integer of up to `BITS` bits loaded from
    /// cells.
    #[derive(Debug)]
    pub struct LoadedBigUint<F: PrimeField, const BITS: usize>(AssignedBigUint<F>);

    impl<F, const BITS: usize> CellReprSize for LoadedBigUint<F, BITS>
    where
        F: PrimeField,
    {
        const SIZE: usize = num_limbs(BITS) * AssignedNative::<F>::SIZE;
    }

    impl<F: PrimeField, const BITS: usize> Borrow<AssignedBigUint<F>> for LoadedBigUint<F, BITS> {
        fn borrow(&self) -> &AssignedBigUint<F> {
            &self.0
        }
    }

    impl<F: PrimeField, const BITS: usize> From<LoadedBigUint<F, BITS>> for AssignedBigUint<F> {
        fn from(value: LoadedBigUint<F, BITS>) -> Self {
            value.0
        }
    }

    impl<F: PrimeField, const BITS: usize> TryFrom<AssignedBigUint<F>> for LoadedBigUint<F, BITS> {
        type Error = Error;

        fn try_from(value: AssignedBigUint<F>) -> Result<Self, Self::Error> {
            let n_limbs = value.limbs.len();
            if n_limbs > num_limbs(BITS) {
                return Err(Error::UnexpectedElements {
                    header: "While wrapping big uint into a loaded bit uint",
                    expected: n_limbs,
                    actual: num_limbs(BITS),
                });
            }
            Ok(Self(value))
        }
    }

    fn emit_limb_bound_constraints<F: PrimeField>(
        biguint: &AssignedBigUint<F>,
        injected_ir: &mut InjectedIR<F>,
    ) -> Result<(), Error> {
        let n_limbs = biguint.limb_size_bounds.len();
        assert_eq!(n_limbs, biguint.limbs.len());
        let lhs = biguint.limbs[..n_limbs - 1].iter().map(|c| (c.cell(), cell_to_expr(c)));
        let rhs = biguint.limb_size_bounds[..n_limbs - 1]
            .iter()
            .copied()
            .map(|b| F::from(b as u64))
            .map(Expression::Constant);
        std::iter::zip(lhs, rhs)
            .map(|((cell, lhs), rhs)| {
                lhs.map(|lhs| {
                    (
                        cell.region_index,
                        IRStmt::constraint(
                            CmpOp::Lt,
                            (cell.row_offset, lhs),
                            (cell.row_offset, rhs),
                        ),
                    )
                })
            })
            .chain(
                std::iter::zip(biguint.limbs.last(), biguint.limb_size_bounds.last()).map(
                    |(limb, bound)| {
                        let cell = limb.cell();
                        let lhs = cell_to_expr(limb)?;
                        let op = if *bound < LOG2_BASE {
                            CmpOp::Le
                        } else {
                            CmpOp::Lt
                        };
                        let rhs = Expression::Constant(F::from(*bound as u64));
                        Ok((
                            cell.region_index,
                            IRStmt::constraint(op, (cell.row_offset, lhs), (cell.row_offset, rhs)),
                        ))
                    },
                ),
            )
            .try_for_each(|stmt| {
                let (index, stmt) = stmt?;
                injected_ir.entry(index).or_default().push(stmt);
                Ok(())
            })
    }

    impl<F: PrimeField, C, const BITS: usize> LoadFromCells<F, C> for LoadedBigUint<F, BITS> {
        fn load(
            ctx: &mut ICtx,
            chip: &C,
            layouter: &mut impl Layouter<F>,
            injected_ir: &mut InjectedIR<F>,
        ) -> Result<Self, Error> {
            assert_eq!(
                AssignedNative::<F>::SIZE,
                1,
                "AssignedNative needs to occupy only one cell"
            );
            let n_limbs = num_limbs(BITS);
            let limbs =
                std::iter::repeat_with(|| AssignedNative::load(ctx, chip, layouter, injected_ir))
                    .take(n_limbs)
                    .collect::<Result<Vec<_>, _>>()?;
            let mut limb_size_bounds = vec![LOG2_BASE; n_limbs];
            let n_bits = std::cmp::max(BITS, 1) as u32;
            *limb_size_bounds.last_mut().unwrap() = (n_bits - 1).rem(LOG2_BASE) + 1; // msl bound
            let be = AssignedBigUint {
                limbs,
                limb_size_bounds,
            };
            emit_limb_bound_constraints(&be, injected_ir)?;

            Ok(LoadedBigUint(be))
        }
    }

    impl<F: PrimeField, C, const BITS: usize> StoreIntoCells<F, C> for LoadedBigUint<F, BITS> {
        fn store(
            self,
            ctx: &mut OCtx,
            chip: &C,
            layouter: &mut impl Layouter<F>,
            injected_ir: &mut InjectedIR<F>,
        ) -> Result<(), Error> {
            let n_limbs = self.0.limbs.len();
            assert_eq!(
                n_limbs,
                self.0.limb_size_bounds.len(),
                "Inconsistent lengths between bounds and lengths"
            );

            if n_limbs > num_limbs(BITS) {
                return Err(Error::UnexpectedElements {
                    header: "While storing big uint",
                    expected: n_limbs,
                    actual: num_limbs(BITS),
                });
            }

            emit_limb_bound_constraints(&self.0, injected_ir)?;

            self.0
                .limbs
                .into_iter()
                .try_for_each(|limb| limb.store(ctx, chip, layouter, injected_ir))
        }
    }
}
