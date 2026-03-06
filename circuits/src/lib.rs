// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

mod circuit_field;
pub mod instructions;
mod utils;

pub use circuit_field::CircuitField;

pub mod biguint;
pub mod ecc;
pub mod field;
pub mod hash;
pub mod map;
pub mod parsing;
pub mod vec;
pub mod verifier;

// Re-exporting modules for convenience and usability.
pub use midnight_proofs;

// Useful for importing external circuits
pub use crate::utils::ComposableChip;

/// Tools useful for testing
pub mod testing_utils {
    pub use crate::utils::ecdsa;
    #[cfg(any(test, feature = "testing"))]
    pub use crate::{
        instructions::hash::tests::test_hash,
        utils::{
            types::{Invertible, Sampleable},
            util::FromScratch,
        },
    };
}

/// Types for assigned circuit values and non-assigned counterparts, and traits
/// for treating with them generically.
pub mod types {
    pub use crate::{
        biguint::AssignedBigUint,
        ecc::{
            foreign::AssignedForeignPoint,
            native::{AssignedNativePoint, AssignedScalarOfNativeCurve},
        },
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
