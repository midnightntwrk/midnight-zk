use std::{cmp::max, ops::Rem};

use ff::PrimeField;
use halo2_proofs::circuit::Value;
use num_bigint::BigUint;
use num_traits::{One, Zero};
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::Sampleable, num_bigint::RandBigInt, rand::RngCore};

use crate::{
    field::foreign::util::{big_from_limbs, big_to_limbs},
    types::{AssignedNative, InnerConstants, InnerValue, Instantiable},
    utils::util::{big_to_fe, fe_to_big},
};

/// The logarithm of the base of representation `BASE := 2^LOG2_BASE`.
// This number should be lower than `F::NUM_BITS / 2` over native field `F`.
// Indeed, it must be lower than that amount with some extra room for
// "computing". For example, with a 256-bits field, this number is not
// recommended to exceed 120.
//
// In general, a good choice for the value of LOG2_BASE is a multiple of
// `MAX_BIT_LEN * NB_POW2RANGE_COLS` where the former is the table size of the
// native_gadget range-checks and the latter the number of columns dedicated to
// such lookup. Here, we pick a multiple of 8 * 4 = 32.
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
/// `AssignedBigUint`s should be constructed by first assigning an
/// `AssignedBoundedBigUint` and then performing a translation into
/// `AssignedBigUint`.
///
/// Similarly, do not implement `PublicInputInstructions` for this type. Pass
/// through `AssignedBoundedBigUint` instead.
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedBigUint<F: PrimeField> {
    pub(crate) limbs: Vec<AssignedNative<F>>,
    pub(crate) limb_size_bounds: Vec<u32>,
}

/// Type for assigned big unsigned integers, emulated over native field `F`,
/// that are guaranteed to be in the range `[0, 2^NB_BITS)`.
///  - `limbs` is a little-endian vector of assigned native values representing
///    the big unsigned integer in base `BASE`. All limbs are guaranteed to be
///    well-formed, i.e. to contain a value in the range `[0, BASE)`, except for
///    the most significant limb, which we may be restricted further (in case
///    LOG2_BASE does not divide NB_BITS).
#[derive(Clone, Debug)]
#[must_use]
pub struct AssignedBoundedBigUint<F: PrimeField, const NB_BITS: u32> {
    pub(crate) limbs: Vec<AssignedNative<F>>,
}

impl<F: PrimeField, const NB_BITS: u32> From<AssignedBoundedBigUint<F, NB_BITS>>
    for AssignedBigUint<F>
{
    fn from(bounded: AssignedBoundedBigUint<F, NB_BITS>) -> Self {
        let mut size_bounds = vec![LOG2_BASE; bounded.limbs.len() - 1];
        size_bounds.push((NB_BITS - 1).rem(LOG2_BASE) + 1);
        AssignedBigUint {
            limbs: bounded.limbs.to_vec(),
            limb_size_bounds: size_bounds,
        }
    }
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

#[cfg(any(test, feature = "testing"))]
pub(crate) const TEST_NB_BITS: u32 = 1024;

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> Sampleable for AssignedBigUint<F> {
    fn sample_inner(mut rng: impl RngCore) -> BigUint {
        rng.gen_biguint(TEST_NB_BITS as u64)
    }
}

impl<F: PrimeField, const NB_BITS: u32> InnerValue for AssignedBoundedBigUint<F, NB_BITS> {
    type Element = BigUint;

    fn value(&self) -> Value<BigUint> {
        Into::<AssignedBigUint<F>>::into(self.clone()).value()
    }
}

impl<F: PrimeField, const NB_BITS: u32> Instantiable<F> for AssignedBoundedBigUint<F, NB_BITS> {
    fn as_public_input(element: &BigUint) -> Vec<F> {
        // TODO: Aggregate the limbs into a batch while they fit in a single `F`.
        biguint_to_limbs(element, Some(NB_BITS.div_ceil(LOG2_BASE)))
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
            .enumerate()
            .fold(0, |acc_bound, (i, bound)| {
                let shifted_acc_bound = max(acc_bound, LOG2_BASE) - LOG2_BASE;
                let bound_i = *bound + (i as u32) * LOG2_BASE;
                bound_of_addition(shifted_acc_bound, bound_i)
            })
    }

    /// Returns `true` iff all the limb bounds of this `AssignedBigUint` are
    /// lower than or equal to LOG2_BASE.
    pub fn is_normalized(&self) -> bool {
        self.limb_size_bounds
            .iter()
            .all(|bound| *bound <= LOG2_BASE)
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
