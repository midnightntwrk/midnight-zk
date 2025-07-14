// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
pub mod vec;
pub mod verifier;

// Re-exporting modules for convenience and usability.
pub use halo2curves;
pub use midnight_proofs;

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
            ComposableChip,
        },
        vec::{AssignedVector, Vectorizable},
    };
}
