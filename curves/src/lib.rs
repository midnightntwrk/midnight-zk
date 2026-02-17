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

#[macro_use]
mod derive;

mod curve;
pub mod ff_ext;
pub mod fft;
#[cfg(any(test, feature = "dev-curves"))]
pub mod hash_to_curve;
pub mod msm;
pub mod serde;
pub mod serde_traits;

// Production curves (always available)
pub mod bls12_381;
mod jubjub;
pub mod k256;

pub mod curve25519;

// Development/testing curves (feature-gated)
#[cfg(any(test, feature = "dev-curves"))]
pub mod bn256;

// Re-exports for production curves
pub use bls12_381::{
    unique_messages, Bls12, Fp, Fq, G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective, Gt,
    MillerLoopResult, PairingG1G2, PairingG2G1, A, B,
};
pub use curve::{Coordinates, CurveAffine, CurveExt};
pub use jubjub::*;
// // Re-export pairing library for compatibility with halo2 ecosystem
pub use pairing;

#[cfg(feature = "serde")]
mod serde_impl;

#[cfg(test)]
pub mod tests;

#[cfg(feature = "__private_bench")]
pub use bls12_381::{Fp12, Fp2};
