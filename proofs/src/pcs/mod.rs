//! Polynomial commitment schemes.
//!
//! [`scheme`] holds the generic `PolynomialCommitmentScheme` trait and its
//! supporting traits; [`kzg`] and [`fflonk`] hold the concrete schemes.
//! [`msm`], [`params`] and the `utils` module hold the shared KZG-style / GWC
//! machinery reused across schemes.

/// The fflonk polynomial commitment scheme.
pub mod fflonk;
/// The KZG polynomial commitment scheme.
pub mod kzg;
/// Multi-scalar-multiplication accumulators ([`MSMKZG`](msm::MSMKZG),
/// [`DualMSM`](msm::DualMSM)).
pub mod msm;
/// Public parameters / SRS (`ParamsKZG`, `ParamsVerifierKZG`).
pub mod params;
/// The `PolynomialCommitmentScheme` trait and its supporting traits (`Params`,
/// `Guard`).
pub mod scheme;

pub(crate) mod multi_open;
pub(crate) mod utils;

pub use scheme::{Guard, Params, PolynomialCommitmentScheme};
#[cfg(feature = "fewer-point-sets")]
pub use utils::compute_dummy_queries;
