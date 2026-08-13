//! Polynomial commitment schemes.
//!
//! [`scheme`] holds the generic `PolynomialCommitmentScheme` trait and its
//! supporting traits. [`msm`], [`params`] and the `utils` module hold the
//! shared KZG-style / GWC machinery reused across schemes.

/// Multi-scalar-multiplication accumulators ([`MSMKZG`](msm::MSMKZG),
/// [`DualMSM`](msm::DualMSM)).
pub mod msm;
/// Public parameters / SRS (`ParamsKZG`, `ParamsVerifierKZG`).
pub mod params;
/// The `PolynomialCommitmentScheme` trait and its supporting traits (`Params`,
/// `Guard`).
pub mod scheme;

pub(crate) mod utils;

pub use scheme::{Guard, Params, PolynomialCommitmentScheme};
#[cfg(feature = "fewer-point-sets")]
pub use utils::compute_dummy_queries;
