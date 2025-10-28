//! A gadget for emulating arithmetic over big unsigned integers.

use std::{
    cmp::{max, min},
    marker::PhantomData,
    ops::Rem,
};

use ff::PrimeField;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    halo2_proofs::plonk::{Column, ConstraintSystem, Instance},
};

use super::{bound_of_addition, AssignedBigUint, AssignedBoundedBigUint};
#[cfg(test)]
use crate::biguint::types::TEST_NB_BITS;
use crate::{
    biguint::{biguint_to_limbs, LOG2_BASE},
    field::{foreign::util::big_to_limbs, AssignedBounded},
    instructions::{
        AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        EqualityInstructions, NativeInstructions, PublicInputInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedNative, Bit},
    utils::{
        types::InnerValue,
        util::{big_to_fe, fe_to_big},
    },
};

#[derive(Clone, Debug)]
/// A gadget for emulating arithmetic over the integers.
///  - F: the native field,
///  - N: a set of in-circuit native instructions.
pub struct BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    native_gadget: N,
    _marker: PhantomData<F>,
}

impl<F, N> BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    /// Create a new gadget for big unsinged integers.
    pub fn new(native_gadget: &N) -> Self {
        Self {
            native_gadget: native_gadget.clone(),
            _marker: PhantomData,
        }
    }
}

// We implement `AssignmentInstructions` and `PublicInputInstructions` for
// `AssignedBoundedBigUint`.
//
// All other functions/traits will be directly implemented for
// `AssignedBigUint`.

impl<F, N, const NB_BITS: u32> AssignmentInstructions<F, AssignedBoundedBigUint<F, NB_BITS>>
    for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<BigUint>,
    ) -> Result<AssignedBoundedBigUint<F, NB_BITS>, Error> {
        let x = self.assign_bounded(layouter, value, NB_BITS)?;
        Ok(AssignedBoundedBigUint::<F, NB_BITS> { limbs: x.limbs })
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        c: BigUint,
    ) -> Result<AssignedBoundedBigUint<F, NB_BITS>, Error> {
        assert!(c.bits() <= NB_BITS as u64);
        let nb_limbs = NB_BITS.div_ceil(LOG2_BASE) as usize;
        let base = BigUint::one() << LOG2_BASE;
        let limbs = big_to_limbs(nb_limbs as u32, &base, &c)
            .into_iter()
            .map(|l| self.native_gadget.assign_fixed(layouter, big_to_fe::<F>(l)))
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(AssignedBoundedBigUint::<F, NB_BITS> { limbs })
    }
}

impl<F, N, const NB_BITS: u32> PublicInputInstructions<F, AssignedBoundedBigUint<F, NB_BITS>>
    for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        assigned: &AssignedBoundedBigUint<F, NB_BITS>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(assigned.limbs.to_vec())
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &AssignedBoundedBigUint<F, NB_BITS>,
    ) -> Result<(), Error> {
        assigned
            .limbs
            .iter()
            .try_for_each(|l| self.native_gadget.constrain_as_public_input(layouter, l))
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<BigUint>,
    ) -> Result<AssignedBoundedBigUint<F, NB_BITS>, Error> {
        // We can skip the bounds check in this case.
        let nb_limbs = NB_BITS.div_ceil(LOG2_BASE) as usize;
        let limbs = value
            .map(|x| big_to_limbs(nb_limbs as u32, &(BigUint::one() << LOG2_BASE), &x))
            .transpose_vec(nb_limbs)
            .into_iter()
            .map(|limb_value| {
                self.native_gadget
                    .assign_as_public_input(layouter, limb_value.map(big_to_fe::<F>))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(AssignedBoundedBigUint::<F, NB_BITS> { limbs })
    }
}

impl<F, N> AssertionInstructions<F, AssignedBigUint<F>> for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<(), Error> {
        assert!(x.is_normalized());
        assert!(y.is_normalized());

        let n = max(x.limbs.len(), y.limbs.len());
        let mut x = x.clone();
        let mut y = y.clone();
        self.resize(layouter, n, &mut x)?;
        self.resize(layouter, n, &mut y)?;

        for i in 0..n {
            self.native_gadget
                .assert_equal(layouter, &x.limbs[i], &y.limbs[i])?;
        }
        Ok(())
    }

    fn assert_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<(), Error> {
        let x_eq_y = self.is_equal(layouter, x, y)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &x_eq_y, Bit(false))
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        constant: BigUint,
    ) -> Result<(), Error> {
        assert!(x.is_normalized());

        let mut constant_limbs = biguint_to_limbs::<F>(&constant, None);
        if x.limbs.len() < constant_limbs.len() {
            panic!(
                "An AssignedBigUint with {} limbs in base 2^{} cannot be equal to {}",
                x.limbs.len(),
                LOG2_BASE,
                constant
            )
        }

        constant_limbs.resize(x.limbs.len(), F::ZERO);

        for (i, ci) in constant_limbs.iter().enumerate() {
            self.native_gadget
                .assert_equal_to_fixed(layouter, &x.limbs[i], *ci)?;
        }

        Ok(())
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        constant: BigUint,
    ) -> Result<(), Error> {
        let x_eq_constant = self.is_equal_to_fixed(layouter, x, constant)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &x_eq_constant, Bit(false))
    }
}

impl<F, N> EqualityInstructions<F, AssignedBigUint<F>> for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBit<F>, Error> {
        assert!(x.is_normalized());
        assert!(y.is_normalized());

        let n = max(x.limbs.len(), y.limbs.len());
        let mut x = x.clone();
        let mut y = y.clone();
        self.resize(layouter, n, &mut x)?;
        self.resize(layouter, n, &mut y)?;

        let xi_eq_yi_bits = (x.limbs.iter())
            .zip(y.limbs.iter())
            .map(|(xi, yi)| self.native_gadget.is_equal(layouter, xi, yi))
            .collect::<Result<Vec<_>, Error>>()?;

        self.native_gadget.and(layouter, &xi_eq_yi_bits)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        constant: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        assert!(x.is_normalized());

        let mut constant_limbs = biguint_to_limbs::<F>(&constant, None);
        if x.limbs.len() < constant_limbs.len() {
            // We could also provide a WARNING in this case, since the output
            // can be deduced from the limb length of x and the constant.
            return self.native_gadget.assign_fixed(layouter, Bit(false));
        }

        constant_limbs.resize(x.limbs.len(), F::ZERO);

        let xi_eq_yi_bits = (x.limbs.iter())
            .zip(constant_limbs.iter())
            .map(|(xi, ci)| self.native_gadget.is_equal_to_fixed(layouter, xi, *ci))
            .collect::<Result<Vec<_>, Error>>()?;

        self.native_gadget.and(layouter, &xi_eq_yi_bits)
    }
}

impl<F, N> ZeroInstructions<F, AssignedBigUint<F>> for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
}

impl<F, N> ControlFlowInstructions<F, AssignedBigUint<F>> for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        let n = max(x.limbs.len(), y.limbs.len());
        let mut x = x.clone();
        let mut y = y.clone();
        self.resize(layouter, n, &mut x)?;
        self.resize(layouter, n, &mut y)?;

        let limbs = (x.limbs.iter())
            .zip(y.limbs.iter())
            .map(|(xi, yi)| self.native_gadget.select(layouter, cond, xi, yi))
            .collect::<Result<Vec<_>, _>>()?;

        let limb_size_bounds = (x.limb_size_bounds.iter())
            .zip(y.limb_size_bounds.iter())
            .map(|(xi_bound, yi_bound)| max(xi_bound, yi_bound))
            .copied()
            .collect::<Vec<_>>();

        Ok(AssignedBigUint {
            limbs,
            limb_size_bounds,
        })
    }
}

impl<F, N> BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    /// Adds the given assigned big unsinged integers.
    pub fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        let mut limbs = Vec::with_capacity(max(x.limbs.len(), y.limbs.len()));
        let mut limb_size_bounds = vec![];

        let n = min(x.limbs.len(), y.limbs.len());
        for i in 0..n {
            limbs.push(self.native_gadget.add(layouter, &x.limbs[i], &y.limbs[i])?);
            limb_size_bounds.push(bound_of_addition(
                x.limb_size_bounds[i],
                y.limb_size_bounds[i],
            ));
        }

        if x.limbs.len() > y.limbs.len() {
            limbs.extend(x.limbs[n..].to_vec());
            limb_size_bounds.extend(x.limb_size_bounds[n..].to_vec());
        }

        if y.limbs.len() > x.limbs.len() {
            limbs.extend(y.limbs[n..].to_vec());
            limb_size_bounds.extend(y.limb_size_bounds[n..].to_vec());
        }

        let z = AssignedBigUint {
            limbs,
            limb_size_bounds,
        };

        self.normalize(layouter, &z)
    }

    /// Subtracts the given assigned big unsinged integers, returning `x - y`.
    ///
    /// # Panics
    ///
    /// The circuit will become unsatisfiable if `x < y`.
    pub fn sub(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        let res_value = (x.value())
            .zip(y.value())
            // We avoid a run-time error here by setting res_value = 0 in case x < y. This is not a
            // soundness problem since, in that case, the resulting circuit would be unsatisfiable,
            // given that we require x = res + y below.
            .map(|(x, y)| if x >= y { x - y } else { BigUint::ZERO });
        let res = self.assign_bounded(layouter, res_value, x.nb_bits())?;
        let z = self.add(layouter, &res, y)?;
        self.assert_equal(layouter, x, &z)?;
        Ok(res)
    }

    /// Multiplies the given assigned big unsinged integers.
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        let x = self.normalize(layouter, x)?;
        let y = self.normalize(layouter, y)?;

        let native_gadget = &self.native_gadget;
        let zero = native_gadget.assign_fixed(layouter, F::ZERO)?;
        let nb_prod_limbs = x.limbs.len() + y.limbs.len() - 1;
        let mut limbs = vec![zero; nb_prod_limbs];
        let mut limb_size_bounds = vec![0; nb_prod_limbs];

        for i in 0..x.limbs.len() {
            for j in 0..y.limbs.len() {
                let p = native_gadget.mul(layouter, &x.limbs[i], &y.limbs[j], None)?;
                let p_bound = x.limb_size_bounds[i] + y.limb_size_bounds[j];
                limbs[i + j] = native_gadget.add(layouter, &limbs[i + j], &p)?;
                limb_size_bounds[i + j] = bound_of_addition(limb_size_bounds[i + j], p_bound);
            }
        }

        let z = AssignedBigUint {
            limbs,
            limb_size_bounds,
        };

        self.normalize(layouter, &z)
    }

    /// Integer division with remainder. Returns (big unsigned) integers
    /// `(q, r)` satisfying:
    ///  - `r in [0, y)`
    ///  - `x = q * y + r`.
    pub fn div_rem(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<(AssignedBigUint<F>, AssignedBigUint<F>), Error> {
        let (q_value, r_value) = x.value().zip(y.value()).map(|(x, y)| x.div_rem(&y)).unzip();

        let q = self.assign_bounded(layouter, q_value, x.nb_bits())?;
        let r = self.assign_bounded(layouter, r_value, y.nb_bits())?;

        let q_times_y = self.mul(layouter, &q, y)?;
        let q_times_y_plus_r = self.add(layouter, &q_times_y, &r)?;
        self.assert_equal(layouter, x, &q_times_y_plus_r)?;

        self.assert_lower_than(layouter, &r, y)?;

        Ok((q, r))
    }

    /// Modular exponentiation (by a constant). Returns `x^n % m`.
    pub fn mod_exp(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        n: u64,
        m: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        if n == 0 {
            let one: AssignedBoundedBigUint<F, 1> = self.assign_fixed(layouter, BigUint::one())?;
            return Ok(one.into());
        }

        let mut n = n;
        let mut tmp = x.clone();
        let mut res = None;

        // This is a simple square-and-multiply.
        while n > 0 {
            if n & 1 != 0 {
                res = match res {
                    None => Some(tmp.clone()),
                    Some(acc) => Some(self.mod_mul(layouter, &acc, &tmp, m)?),
                };
            }

            n >>= 1;

            if n > 0 {
                tmp = self.mod_mul(layouter, &tmp, &tmp, m)?;
            }
        }

        Ok(res.unwrap())
    }

    /// Returns a vector of assigned bits representing the given assigned big
    /// unsigned integer little-endian.
    pub fn to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        assert!(x.is_normalized());

        let bits = x
            .limbs
            .iter()
            .map(|limb| {
                self.native_gadget.assigned_to_le_bits(
                    layouter,
                    limb,
                    Some(LOG2_BASE as usize),
                    true,
                )
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect();

        Ok(bits)
    }

    /// Returns the assigned big unsigned integer represented by the given
    /// vector of assigned bits, by interpreting it in little-endian.
    pub fn from_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBigUint<F>, Error> {
        let limbs = bits
            .chunks(LOG2_BASE as usize)
            .map(|chunk_bits| {
                self.native_gadget
                    .assigned_from_le_bits(layouter, chunk_bits)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let limb_size_bounds = bits
            .chunks(LOG2_BASE as usize)
            .map(|chunk_bits| chunk_bits.len() as u32)
            .collect();

        Ok(AssignedBigUint {
            limbs,
            limb_size_bounds,
        })
    }

    /// Returns `1` iff `x < y`.
    pub fn lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBit<F>, Error> {
        let geq = self.geq(layouter, x, y)?;
        self.native_gadget.not(layouter, &geq)
    }
}

// A block of auxiliary non-exposed functions.
impl<F, N> BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    /// Assigns a big unsigned integer, and guarantees it fits in the range
    /// `[0, 2^nb_bits)`.
    fn assign_bounded(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<BigUint>,
        nb_bits: u32,
    ) -> Result<AssignedBigUint<F>, Error> {
        let nb_limbs = nb_bits.div_ceil(LOG2_BASE) as usize;
        // All limbs will be bounded by 2^LOG2_BASE except possibly the most significant
        // one, which will be restricted further if LOG2_BASE does not divide NB_BITS.
        let mut limb_size_bounds = vec![LOG2_BASE; nb_limbs - 1];
        limb_size_bounds.push((nb_bits - 1).rem(LOG2_BASE) + 1); // msl bound

        let limbs = value
            .map(|x| big_to_limbs(nb_limbs as u32, &(BigUint::one() << LOG2_BASE), &x))
            .transpose_vec(nb_limbs)
            .into_iter()
            .zip(limb_size_bounds.iter())
            .map(|(limb_value, size_bound)| {
                self.native_gadget.assign_lower_than_fixed(
                    layouter,
                    limb_value.map(big_to_fe::<F>),
                    &(BigUint::one() << *size_bound),
                )
            })
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(AssignedBigUint::<F> {
            limbs,
            limb_size_bounds,
        })
    }

    /// Normalize the given `AssignedBigUint`, producing an equivalent one where
    /// all the limbs are guaranteed to be in the range `[0, BASE)`.
    fn normalize(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        if x.is_normalized() {
            return Ok(x.clone());
        }

        let native_gadget = &self.native_gadget;
        let nb_limbs_output = x.nb_bits().div_ceil(LOG2_BASE) as usize;

        // Extend x with trailing zeros to fit the output length.
        let mut x = x.clone();
        self.resize(layouter, nb_limbs_output, &mut x)?;

        let mut carry: AssignedNative<F> = native_gadget.assign_fixed(layouter, F::ZERO)?;
        let mut carry_size_bound = 0;
        let mut limbs = Vec::with_capacity(nb_limbs_output);

        for i in 0..nb_limbs_output {
            let payload = native_gadget.add(layouter, &carry, &x.limbs[i])?;
            let payload_bound = bound_of_addition(carry_size_bound, x.limb_size_bounds[i]);

            // Make sure we never overflow over the native modulus.
            if payload_bound >= F::NUM_BITS {
                panic!("normalize: overflow over native modulus; decrease LOG2_BASE to avoid this")
            }

            let (q, limb) = self.div_rem_native_by_base(layouter, &payload, payload_bound)?;

            // Prepare the carry and its bound for the next iteration.
            carry_size_bound = max(payload_bound, LOG2_BASE) - LOG2_BASE;
            carry = q;

            limbs.push(limb);
        }

        // Assert that the final carry is zero, ensuring proper normalization.
        native_gadget.assert_equal_to_fixed(layouter, &carry, F::ZERO)?;

        Ok(AssignedBigUint {
            limbs,
            limb_size_bounds: vec![LOG2_BASE; nb_limbs_output],
        })
    }

    /// Resizes, if necessary, the limbs of the given `AssignedBigUint` by
    /// adding trailing zeros, until reaching the desired length.
    ///
    /// # Panics
    ///
    /// If the number of limbs of the `x` exceeds the desired size `n`.
    fn resize(
        &self,
        layouter: &mut impl Layouter<F>,
        n: usize,
        x: &mut AssignedBigUint<F>,
    ) -> Result<(), Error> {
        if x.limbs.len() > n {
            panic!("resize: the number of limbs is greater than the desired size");
        }
        let zero: AssignedNative<F> = self.native_gadget.assign_fixed(layouter, F::ZERO)?;
        x.limbs.resize(n, zero);
        x.limb_size_bounds.resize(n, 0);

        Ok(())
    }

    /// Modular multiplication. Returns `(x * y) % m`.
    fn mod_mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
        m: &AssignedBigUint<F>,
    ) -> Result<AssignedBigUint<F>, Error> {
        let p = self.mul(layouter, x, y)?;
        let (_, r) = self.div_rem(layouter, &p, m)?;
        Ok(r)
    }

    /// Returns `1` iff `x >= y`.
    fn geq(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<AssignedBit<F>, Error> {
        assert!(x.is_normalized());
        assert!(y.is_normalized());

        let n = max(x.limbs.len(), y.limbs.len());
        let mut x = x.clone();
        let mut y = y.clone();
        self.resize(layouter, n, &mut x)?;
        self.resize(layouter, n, &mut y)?;

        let init = self.native_gadget.assign_fixed(layouter, Bit(true))?;
        x.limbs
            .iter()
            .zip(y.limbs.iter())
            .try_fold(init, |acc, (xi, yi)| {
                let xi_eq_yi = self.native_gadget.is_equal(layouter, xi, yi)?;
                let xi = AssignedBounded::<F>::to_assigned_bounded_unsafe(xi, LOG2_BASE);
                let yi = AssignedBounded::<F>::to_assigned_bounded_unsafe(yi, LOG2_BASE);
                let xi_greater_than_yi = self.native_gadget.greater_than(layouter, &xi, &yi)?;

                let acc = self.native_gadget.and(layouter, &[xi_eq_yi, acc])?;

                self.native_gadget.or(layouter, &[xi_greater_than_yi, acc])
            })
    }

    /// Ensures that `x < y`.
    fn assert_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedBigUint<F>,
        y: &AssignedBigUint<F>,
    ) -> Result<(), Error> {
        let b = self.geq(layouter, x, y)?;
        self.native_gadget
            .assert_equal_to_fixed(layouter, &b, Bit(false))
    }

    /// Division with remainder of the given native value by constant
    /// `BASE := 2^LOG2_BASE`. Returns `AssignedNative` values `(q, r)`
    /// satisfying:
    ///  - `r in [0, BASE)`
    ///  - `x = q * BASE + r`.
    ///
    /// This function also takes a bound on the size of `x`, satisfying
    /// `x in [0, 2^x_size_bound).` Such bound cannot exceed the native field
    /// number of bits, to avoid overflows.
    fn div_rem_native_by_base(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        x_size_bound: u32,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error> {
        assert!(x_size_bound < F::NUM_BITS);
        let native_gadget = &self.native_gadget;
        let base = BigUint::one() << LOG2_BASE;
        let (q_value, r_value) = x
            .value()
            .map(|v| {
                let (q, r) = fe_to_big(*v).div_rem(&base);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        let shifted_x_size_bound = max(x_size_bound, LOG2_BASE) - LOG2_BASE;
        let q_bound = BigUint::one() << shifted_x_size_bound;

        let q = native_gadget.assign_lower_than_fixed(layouter, q_value, &q_bound)?;
        let r = native_gadget.assign_lower_than_fixed(layouter, r_value, &base)?;

        let q_times_base_plus_r = native_gadget.linear_combination(
            layouter,
            &[
                (F::from_u128(1 << LOG2_BASE), q.clone()),
                (F::ONE, r.clone()),
            ],
            F::ZERO,
        )?;
        native_gadget.assert_equal(layouter, x, &q_times_base_plus_r)?;

        Ok((q, r))
    }
}

// The following implementation of AssignmentInstructions for `AssignedBigUint`
// is exclusively for tests. DO NOT remove the `cfg(test)` flag here.
// The only entry point for `AssignedBigUint` must be `AssignedBoundedBigUint`.
#[cfg(test)]
impl<F, N> AssignmentInstructions<F, AssignedBigUint<F>> for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<BigUint>,
    ) -> Result<AssignedBigUint<F>, Error> {
        let x: AssignedBoundedBigUint<F, TEST_NB_BITS> = self.assign(layouter, value)?;
        Ok(x.into())
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        c: BigUint,
    ) -> Result<AssignedBigUint<F>, Error> {
        let x: AssignedBoundedBigUint<F, TEST_NB_BITS> = self.assign_fixed(layouter, c)?;
        Ok(x.into())
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, N> FromScratch<F> for BigUintGadget<F, N>
where
    F: PrimeField,
    N: NativeInstructions<F> + FromScratch<F>,
{
    type Config = <N as FromScratch<F>>::Config;

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_gadget = <N as FromScratch<F>>::new_from_scratch(config);
        BigUintGadget::<F, N>::new(&native_gadget)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_column: &Column<Instance>,
    ) -> Self::Config {
        <N as FromScratch<F>>::configure_from_scratch(meta, instance_column)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        <N as FromScratch<F>>::load_from_scratch(layouter, config);
    }
}

#[cfg(test)]
mod tests {

    use blstrs::Scalar as BlsScalar;
    use ff::FromUniformBytes;
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use halo2curves::pasta::{Fp as VestaScalar, Fq as PallasScalar};
    use num_bigint::RandBigInt;
    use num_traits::Zero;

    use super::*;
    use crate::{
        field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
        instructions::{assertions, control_flow, equality, zero},
        testing_utils::FromScratch,
    };

    // Aliases for readability.
    type NG<F> = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
    type BG<F> = BigUintGadget<F, NG<F>>;

    macro_rules! test_field {
        ($mod:ident, $op:ident, $field:ident, $name:expr) => {
            $mod::tests::$op::<$field, AssignedBigUint<$field>, BG<$field>>($name);
        };
    }

    macro_rules! test {
        ($mod:ident, $op:ident) => {
            #[test]
            fn $op() {
                test_field!($mod, $op, BlsScalar, "biguint_gadget");
                test_field!($mod, $op, PallasScalar, "");
                test_field!($mod, $op, VestaScalar, "");
            }
        };
    }

    test!(assertions, test_assertions);

    test!(equality, test_is_equal);

    test!(zero, test_zero_assertions);
    test!(zero, test_is_zero);

    test!(control_flow, test_select);
    test!(control_flow, test_cond_assert_equal);

    #[derive(Clone, Debug)]
    enum Operation {
        Add,
        Sub,
        Mul,
        Div,
        Rem,
        ModExp,
        Bits,
        Lower,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, N> {
        x: Value<BigUint>,
        y: Value<BigUint>,
        expected: BigUint,
        operation: Operation,
        _marker: PhantomData<(F, N)>,
    }

    impl<F, N> Circuit<F> for TestCircuit<F, N>
    where
        F: PrimeField,
        N: NativeInstructions<F> + FromScratch<F>,
    {
        type Config = <N as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_column = meta.instance_column();
            <N as FromScratch<F>>::configure_from_scratch(meta, &instance_column)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = <N as FromScratch<F>>::new_from_scratch(&config);
            let biguint_gadget = BigUintGadget::<F, N>::new(&native_gadget);
            <N as FromScratch<F>>::load_from_scratch(&mut layouter, &config);

            let x: AssignedBoundedBigUint<F, 1024> =
                biguint_gadget.assign(&mut layouter, self.x.clone())?;
            let y: AssignedBoundedBigUint<F, 1024> =
                biguint_gadget.assign(&mut layouter, self.y.clone())?;

            let x: AssignedBigUint<F> = x.into();
            let y: AssignedBigUint<F> = y.into();

            let res = match self.operation {
                Operation::Add => biguint_gadget.add(&mut layouter, &x, &y)?,
                Operation::Sub => biguint_gadget.sub(&mut layouter, &x, &y)?,
                Operation::Mul => biguint_gadget.mul(&mut layouter, &x, &y)?,
                Operation::Div => biguint_gadget.div_rem(&mut layouter, &x, &y)?.0,
                Operation::Rem => biguint_gadget.div_rem(&mut layouter, &x, &y)?.1,
                Operation::ModExp => biguint_gadget.mod_exp(&mut layouter, &x, 3, &y)?,
                Operation::Bits => {
                    let bits = biguint_gadget.to_le_bits(&mut layouter, &x)?;
                    biguint_gadget.from_le_bits(&mut layouter, &bits)?
                }
                Operation::Lower => {
                    let b = biguint_gadget.lower_than(&mut layouter, &x, &y)?;
                    biguint_gadget.from_le_bits(&mut layouter, &[b])?
                }
            };

            let expected: AssignedBoundedBigUint<F, 2048> =
                biguint_gadget.assign_fixed(&mut layouter, self.expected.clone())?;

            biguint_gadget.assert_equal(&mut layouter, &expected.into(), &res)
        }
    }

    fn run<F>(x: &BigUint, y: &BigUint, expected: &BigUint, operation: Operation, must_pass: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
    {
        let circuit = TestCircuit::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>> {
            x: Value::known(x.clone()),
            y: Value::known(y.clone()),
            expected: expected.clone(),
            operation,
            _marker: PhantomData,
        };
        let log2_nb_rows = 12;
        let public_inputs = vec![vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }
    }

    fn random_biguint(nb_bits: u64) -> BigUint {
        rand::thread_rng().gen_biguint(nb_bits)
    }

    #[test]
    fn test_add_biguint() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            let y: BigUint = random_biguint(1024);
            run::<F>(&x, &y, &(&x + &y), Operation::Add, true);
            run::<F>(&x, &zero, &x, Operation::Add, true);
            run::<F>(&x, &y, &zero, Operation::Add, false)
        }
    }

    #[test]
    fn test_sub_biguint() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        let one = BigUint::one();
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            let y: BigUint = random_biguint(1024);
            let (x, y) = if x >= y { (x, y) } else { (y, x) };
            run::<F>(&x, &y, &(&x - &y), Operation::Sub, true);
            run::<F>(&y, &x, &zero, Operation::Sub, false);
            run::<F>(&x, &zero, &x, Operation::Sub, true);
            run::<F>(&x, &x, &zero, Operation::Sub, true);
            run::<F>(&zero, &zero, &zero, Operation::Sub, true);
            run::<F>(&(&x + &one), &x, &one, Operation::Sub, true);
            run::<F>(&x, &y, &zero, Operation::Sub, false)
        }
    }

    #[test]
    fn test_mul_biguint() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        let one = BigUint::one();
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            let y: BigUint = random_biguint(1024);
            run::<F>(&x, &y, &(&x * &y), Operation::Mul, true);
            run::<F>(&x, &zero, &zero, Operation::Mul, true);
            run::<F>(&zero, &x, &zero, Operation::Mul, true);
            run::<F>(&x, &one, &x, Operation::Mul, true);
            run::<F>(&one, &x, &x, Operation::Mul, true);
            run::<F>(&x, &y, &zero, Operation::Add, false)
        }
    }

    #[test]
    fn test_div_rem_biguint() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        let one = BigUint::one();
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            let y: BigUint = random_biguint(1000);
            let (q, r) = x.div_rem(&y);
            let x_plus_one = &x + BigUint::one();
            run::<F>(&x, &y, &q, Operation::Div, true);
            run::<F>(&x, &one, &x, Operation::Div, true);
            run::<F>(&x, &x, &one, Operation::Div, true);
            run::<F>(&x, &x_plus_one, &zero, Operation::Div, true);
            run::<F>(&x, &y, &random_biguint(1024), Operation::Div, false);

            run::<F>(&x, &y, &r, Operation::Rem, true);
            run::<F>(&x, &one, &zero, Operation::Rem, true);
            run::<F>(&x, &x, &zero, Operation::Rem, true);
            run::<F>(&x, &x_plus_one, &x, Operation::Rem, true);
            run::<F>(&x, &y, &random_biguint(1024), Operation::Rem, false)
        }
    }

    #[test]
    fn test_mod_exp_biguint() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        let one = BigUint::one();
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            let m: BigUint = random_biguint(1024);
            let res = (&x * &x * &x).div_rem(&m).1;
            run::<F>(&x, &m, &res, Operation::ModExp, true);
            run::<F>(&zero, &m, &zero, Operation::ModExp, true);
            run::<F>(&one, &m, &one, Operation::ModExp, true);
            run::<F>(&x, &m, &BigUint::ZERO, Operation::ModExp, false)
        }
    }

    #[test]
    fn test_biguint_to_and_from_bits() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        let one = BigUint::one();
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            run::<F>(&x, &BigUint::default(), &x, Operation::Bits, true);
            run::<F>(&x, &BigUint::default(), &zero, Operation::Bits, false);
        }
        run::<F>(&zero, &BigUint::default(), &zero, Operation::Bits, true);
        run::<F>(&one, &BigUint::default(), &one, Operation::Bits, true);
    }

    #[test]
    fn test_lower_than_biguint() {
        type F = blstrs::Scalar;
        let zero = BigUint::ZERO;
        let one = BigUint::one();
        for _ in 0..10 {
            let x: BigUint = random_biguint(1024);
            let y: BigUint = random_biguint(1024);
            let res = if x < y {
                BigUint::one()
            } else {
                BigUint::zero()
            };
            run::<F>(&x, &y, &res, Operation::Lower, true);
            run::<F>(&x, &x, &zero, Operation::Lower, true);
            run::<F>(&x, &x, &one, Operation::Lower, false);
            run::<F>(&x, &(&x + BigUint::one()), &one, Operation::Lower, true);
        }
        run::<F>(&zero, &zero, &zero, Operation::Lower, true);
        run::<F>(&zero, &one, &one, Operation::Lower, true);
        run::<F>(&one, &zero, &zero, Operation::Lower, true);
        run::<F>(&one, &one, &zero, Operation::Lower, true);
    }
}
