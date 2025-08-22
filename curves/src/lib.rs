//! # `blstrs`
//!
//! An implementation of the BLS12-381 pairing-friendly elliptic curve
//! construction.

#![deny(clippy::perf, clippy::correctness)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::wrong_self_convention)]

#[cfg(not(target_endian = "little"))]
compile_error!("blstrs is only supported on little endian architectures");

#[macro_use]
mod arithmetic;

mod bls12_381;
mod pairing;

mod jubjub;

pub use bls12_381::fp::Fp;
pub use bls12_381::fq::Fq;
pub use bls12_381::g1::{G1Affine, G1Projective, A, B};
pub use bls12_381::g2::{G2Affine, G2Prepared, G2Projective};
pub use bls12_381::gt::Gt;
pub use jubjub::*;
pub use pairing::*;

#[cfg(feature = "serde")]
mod serde_impl;

#[cfg(test)]
pub mod tests;

// export for benchmarking only
use ff::Field;
use group::prime::PrimeCurveAffine;
use pairing_lib::{Engine, MultiMillerLoop, PairingCurveAffine};

#[cfg(feature = "__private_bench")]
pub use crate::{bls12_381::fp12::Fp12, bls12_381::fp2::Fp2};

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
                tmp = bls12_381::fp12::Fp12::ONE.0;
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

        MillerLoopResult(bls12_381::fp12::Fp12(res))
    }
}

#[test]
fn bls12_engine_tests() {
    crate::tests::engine::engine_tests::<Bls12>();
}
