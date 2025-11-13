//! Secp256k1 elliptic curve implementation.
//!
//! This is the secp256k1 curve defined over the base field Fp and scalar field Fq.
//! It's used in Bitcoin, Ethereum, and other cryptocurrency systems.

mod curve;
mod fp;
mod fq;

pub use curve::*;
pub use fp::*;
pub use fq::*;
