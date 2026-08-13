//! Polynomial commitment schemes.
//!
//! [`scheme`] holds the generic `PolynomialCommitmentScheme` trait and its
//! supporting traits.

/// The `PolynomialCommitmentScheme` trait and its supporting traits (`Params`,
/// `Guard`).
pub mod scheme;

pub use scheme::{Guard, Params, PolynomialCommitmentScheme};
