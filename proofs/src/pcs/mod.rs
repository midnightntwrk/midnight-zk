//! Polynomial commitment schemes.
//!
//! [`scheme`] holds the generic `PolynomialCommitmentScheme` trait and its
//! supporting traits; the concrete fflonk scheme (with KZG as its `T = 0`
//! specialization) lives in [`fflonk`]. [`msm`], [`params`] and the `utils`
//! module hold the shared KZG-style / GWC machinery reused across schemes.

/// The fflonk polynomial commitment scheme (KZG is its `T = 0` case).
pub mod fflonk;
/// Multi-scalar-multiplication accumulators ([`MSMKZG`](msm::MSMKZG),
/// [`DualMSM`](msm::DualMSM)).
pub mod msm;
/// Public parameters / SRS (`ParamsKZG`, `ParamsVerifierKZG`).
pub mod params;
/// The `PolynomialCommitmentScheme` trait and its supporting traits (`Params`,
/// `Guard`, `Labelable`).
pub mod scheme;

pub(crate) mod utils;

pub use fflonk::{FflonkCommitment, FflonkScheme, FflonkVerificationGuard, FFLONK_T_MAX_LOG};
pub use params::{ParamsFflonk, ParamsVerifierFflonk};
pub use scheme::{Guard, Labelable, Params, PolynomialCommitmentScheme};
pub use utils::compute_dummy_queries;
