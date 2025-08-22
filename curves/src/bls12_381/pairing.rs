use core::ops::{Add, AddAssign};

use blst::*;
use ff::Field;
use subtle::{Choice, ConditionallySelectable};

use crate::{Fq, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Gt};

use group::prime::PrimeCurveAffine;
use pairing_lib::{Engine, MultiMillerLoop};

use super::fp12::{self, Fp12};

/// Execute a complete pairing operation `(p, q)`.
pub fn pairing(p: &G1Affine, q: &G2Affine) -> Gt {
    let mut tmp = blst_fp12::default();
    unsafe { blst_miller_loop(&mut tmp, &q.0, &p.0) };

    let mut out = blst_fp12::default();
    unsafe { blst_final_exp(&mut out, &tmp) };

    Gt(Fp12(out))
}

macro_rules! impl_pairing {
    ($name:ident, $p:ty, $q:ty, $aggregate:ident, $aggregated:ident) => {
        /// Aggregate pairings efficiently.
        #[derive(Debug)]
        pub struct $name {
            v: Box<[u64]>,
        }

        impl $name {
            pub fn new(hash_or_encode: bool, dst: &[u8]) -> Self {
                let v: Vec<u64> = vec![0; unsafe { blst_pairing_sizeof() } / 8];
                let mut obj = Self {
                    v: v.into_boxed_slice(),
                };
                obj.init(hash_or_encode, dst);
                obj
            }

            pub fn init(&mut self, hash_or_encode: bool, dst: &[u8]) {
                unsafe { blst_pairing_init(self.ctx(), hash_or_encode, dst.as_ptr(), dst.len()) }
            }

            fn ctx(&mut self) -> *mut blst_pairing {
                self.v.as_mut_ptr() as *mut blst_pairing
            }

            fn const_ctx(&self) -> *const blst_pairing {
                self.v.as_ptr() as *const blst_pairing
            }

            pub fn aggregate(
                &mut self,
                pk: &$p,
                sig: Option<&$q>,
                msg: &[u8],
                aug: &[u8],
            ) -> Result<(), BLST_ERROR> {
                let res = unsafe {
                    $aggregate(
                        self.ctx(),
                        &pk.0,
                        match sig {
                            Some(sig) => &sig.0,
                            None => std::ptr::null(),
                        },
                        msg.as_ptr(),
                        msg.len(),
                        aug.as_ptr(),
                        aug.len(),
                    )
                };
                if res == BLST_ERROR::BLST_SUCCESS {
                    Ok(())
                } else {
                    Err(res)
                }
            }

            pub fn aggregated(gtsig: &mut Gt, sig: &$q) {
                unsafe { $aggregated(&mut (gtsig.0).0, &sig.0) }
            }

            pub fn commit(&mut self) {
                unsafe { blst_pairing_commit(self.ctx()) }
            }

            pub fn merge(&mut self, ctx1: &Self) -> Result<(), BLST_ERROR> {
                let res = unsafe { blst_pairing_merge(self.ctx(), ctx1.const_ctx()) };
                if res == BLST_ERROR::BLST_SUCCESS {
                    Ok(())
                } else {
                    Err(res)
                }
            }

            pub fn finalverify(&self, gtsig: Option<&Gt>) -> bool {
                unsafe {
                    blst_pairing_finalverify(
                        self.const_ctx(),
                        match gtsig {
                            Some(ref gtsig) => &(gtsig.0).0,
                            None => std::ptr::null(),
                        },
                    )
                }
            }
        }
    };
}

impl_pairing!(
    PairingG1G2,
    G1Affine,
    G2Affine,
    blst_pairing_aggregate_pk_in_g1,
    blst_aggregated_in_g2
);
impl_pairing!(
    PairingG2G1,
    G2Affine,
    G1Affine,
    blst_pairing_aggregate_pk_in_g2,
    blst_aggregated_in_g1
);

/// Returns true if all provided messages are distinctly unique, false
/// otherwise.
pub fn unique_messages(msgs: &[&[u8]]) -> bool {
    let n_elems = msgs.len();

    if n_elems == 1 {
        return true;
    } else if n_elems == 2 {
        return msgs[0] != msgs[1];
    }

    let mut v: Vec<u64> = vec![0; unsafe { blst_uniq_sizeof(n_elems) } / 8];
    let ctx = v.as_mut_ptr() as *mut blst_uniq;

    unsafe { blst_uniq_init(ctx) };

    for msg in msgs.iter() {
        if !unsafe { blst_uniq_test(ctx, msg.as_ptr(), msg.len()) } {
            return false;
        }
    }

    true
}

/// Bls12-381 engine
#[derive(Debug, Copy, Clone)]
pub struct Bls12;

impl Engine for Bls12 {
    type Fr = Fq;
    type G1 = G1Projective;
    type G1Affine = G1Affine;
    type G2 = G2Projective;
    type G2Affine = G2Affine;
    type Gt = Gt;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        pairing(p, q)
    }
}

impl MultiMillerLoop for Bls12 {
    type G2Prepared = G2Prepared;
    type Result = MillerLoopResult;

    /// Computes $$\sum_{i=1}^n \textbf{ML}(a_i, b_i)$$ given a series of terms
    /// $$(a_1, b_1), (a_2, b_2), ..., (a_n, b_n).$$
    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        let mut res = blst::blst_fp12::default();

        for (i, (p, q)) in terms.iter().enumerate() {
            let mut tmp = blst::blst_fp12::default();
            if (p.is_identity() | q.is_identity()).into() {
                // Define pairing with zero as one, matching what `pairing` does.
                tmp = Fp12::ONE.0;
            } else {
                unsafe {
                    blst::blst_miller_loop_lines(&mut tmp, q.lines.as_ptr(), &p.0);
                }
            }
            if i == 0 {
                res = tmp;
            } else {
                unsafe {
                    blst::blst_fp12_mul(&mut res, &res, &tmp);
                }
            }
        }

        MillerLoopResult(fp12::Fp12(res))
    }
}

#[test]
fn bls12_engine_tests() {
    crate::tests::engine::engine_tests::<Bls12>();
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

impl pairing_lib::MillerLoopResult for MillerLoopResult {
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
