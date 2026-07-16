use core::ops::{Add, AddAssign};

use blst::*;
use ff::Field;
use subtle::{Choice, ConditionallySelectable};

use super::{fp12::Fp12, G1Affine, G2Affine, Gt};

/// Execute a complete pairing operation `(p, q)`.
pub fn pairing(p: &G1Affine, q: &G2Affine) -> Gt {
    let mut tmp = blst_fp12::default();
    unsafe { blst_miller_loop(&mut tmp, &q.0, &p.0) };

    let mut out = blst_fp12::default();
    unsafe { blst_final_exp(&mut out, &tmp) };

    Gt(Fp12(out))
}

/// Represents results of a Miller loop, one of the most expensive portions
/// of the pairing function. `MillerLoopResult`s cannot be compared with each
/// other until `.final_exponentiation()` is called, which is also expensive.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct MillerLoopResult(pub(crate) Fp12);

impl ConditionallySelectable for MillerLoopResult {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        MillerLoopResult(Fp12::conditional_select(&a.0, &b.0, choice))
    }
}

impl Default for MillerLoopResult {
    fn default() -> Self {
        MillerLoopResult(Fp12::ONE)
    }
}

impl pairing::MillerLoopResult for MillerLoopResult {
    type Gt = Gt;

    fn final_exponentiation(&self) -> Gt {
        let mut out = blst_fp12::default();
        unsafe { blst_final_exp(&mut out, &(self.0).0) };
        Gt(Fp12(out))
    }
}

impl<'b> Add<&'b MillerLoopResult> for &MillerLoopResult {
    type Output = MillerLoopResult;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: &'b MillerLoopResult) -> MillerLoopResult {
        MillerLoopResult(self.0 * rhs.0)
    }
}

impl_add!(MillerLoopResult);

impl AddAssign<MillerLoopResult> for MillerLoopResult {
    #[inline]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn add_assign(&mut self, rhs: MillerLoopResult) {
        self.0 *= &rhs.0;
    }
}

impl<'b> AddAssign<&'b MillerLoopResult> for MillerLoopResult {
    #[inline]
    #[allow(clippy::op_ref)]
    fn add_assign(&mut self, rhs: &'b MillerLoopResult) {
        *self = &*self + rhs;
    }
}
