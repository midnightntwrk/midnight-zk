//! Curve25519 .
//!
//! Defined over the base field `Fp`, with scalar field `Fq`.

// mod affine;
mod curve;
mod fp;
// mod fq;

// pub use curve::{Curve25519, Curve25519Affine};
pub use curve::Curve25519;
// pub use fq::{Fq, Scalar};
pub use curve25519_dalek::edwards::CompressedEdwardsY;
pub use curve25519_dalek::Scalar;
pub use fp::Fp;
