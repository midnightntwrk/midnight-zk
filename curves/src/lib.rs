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

pub mod msm;

mod curve;

mod bls12_381;
mod jubjub;

pub use bls12_381::fp::Fp;
pub use bls12_381::fq::Fq;
pub use bls12_381::g1::{G1Affine, G1Projective, A, B};
pub use bls12_381::g2::{G2Affine, G2Prepared, G2Projective};
pub use bls12_381::gt::Gt;
pub use bls12_381::pairing::*;
pub use jubjub::*;

#[cfg(test)]
mod tests;

#[cfg(feature = "serde")]
mod serde_impl;
