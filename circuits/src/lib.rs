//! Halo2 gadgets implemented for Midnight.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

#[doc = include_str!("../README.md")]
extern crate core;
#[cfg(feature = "regression")]
extern crate serde_derive;

pub mod compact_std_lib;
pub mod instructions;
mod utils;

pub mod biguint;
pub mod ecc;
pub mod field;
pub mod hash;
pub mod json;
pub mod map;
pub mod verifier;

// Re-exporting modules for convenience and usability.
pub use halo2_proofs;
pub use halo2curves;

/// Tools useful for testing
pub mod testing_utils {
    pub use crate::utils::{ecdsa, plonk_api};
    #[cfg(any(test, feature = "testing"))]
    pub use crate::utils::{
        types::{Invertible, Sampleable},
        util::FromScratch,
    };
}

/// Types for assigned circuit values and non-assigned counterparts, and traits
/// for treating with them generically.
pub mod types {
    pub use crate::{
        ecc::{foreign::AssignedForeignPoint, native::AssignedNativePoint},
        field::{
            foreign::AssignedField,
            native::{AssignedBit, AssignedByte},
            AssignedNative,
        },
        utils::{
            types::{InnerConstants, InnerValue, Instantiable},
            vector::{AssignedVector, VectorInstructions, Vectorizable},
            ComposableChip,
        },
    };
}
