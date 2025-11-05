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

mod curve;
pub mod fft;
pub mod ff_ext;
pub mod msm;
pub mod serde_traits;

pub mod bls12_381;
mod jubjub;

pub use bls12_381::{Bls12, Fp, Fq, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Gt, A, B};
pub use bls12_381::{MillerLoopResult, PairingG1G2, PairingG2G1, pairing, unique_messages};
pub use curve::{Coordinates, CurveAffine, CurveExt};
pub use jubjub::*;

#[cfg(feature = "serde")]
mod serde_impl;

#[cfg(test)]
pub mod tests;

#[cfg(feature = "__private_bench")]
pub use bls12_381::{Fp12, Fp2};
