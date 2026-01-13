//! Curve25519 .
//!
//! Defined over the base field `Fp`, with scalar field `Fq`.

// mod curve;
mod fp;
// mod fq;

// pub use curve::*;
// pub use fp::*;
// pub use fq::*;

// use curve25519_dalek::field::FieldElement as Base;
// use curve25519_dalek::scalar::Scalar;
// use curve25519_dalek::*;
// use group::cofactor::CofactorCurveAffine;

// use curve25519_dalek::edwards::affine

// #[cfg(test)]
// mod tests {
//     use curve25519_dalek::traits::Identity;
//     use ff::Field;

//     use super::*;

//     #[test]
//     fn test_curve_equation() {
//         // Test that the generator is on the curve
//         let g = EdwardsPoint::identity();
//         assert!(bool::from(g.is_on_curve()));
//     }
// }
