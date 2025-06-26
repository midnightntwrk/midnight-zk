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

//! Set of instructions interfaces.
pub mod arithmetic;
pub mod assertions;
pub mod assignments;
pub mod base64;
pub mod binary;
pub mod bitwise;
pub mod canonicity;
pub mod comparison;
pub mod control_flow;
pub mod conversions;
pub mod decomposition;
pub mod divmod;
pub mod ecc;
pub mod equality;
pub mod field;
pub mod hash;
pub mod hash_to_curve;
pub mod map;
pub mod native;
pub mod public_input;
pub mod range_check;
pub mod scalar_field;
pub mod sponge;
pub mod zero;

pub use arithmetic::ArithInstructions;
pub use assertions::AssertionInstructions;
pub use assignments::AssignmentInstructions;
pub use base64::Base64Instructions;
pub use binary::BinaryInstructions;
pub use bitwise::BitwiseInstructions;
pub use canonicity::CanonicityInstructions;
pub use comparison::ComparisonInstructions;
pub use control_flow::ControlFlowInstructions;
pub use conversions::{ConversionInstructions, UnsafeConversionInstructions};
pub use decomposition::DecompositionInstructions;
pub use divmod::DivisionInstructions;
pub use ecc::EccInstructions;
pub use equality::EqualityInstructions;
pub use field::FieldInstructions;
pub use hash::HashInstructions;
pub use hash_to_curve::{HashToCurveCPU, HashToCurveInstructions};
pub use native::NativeInstructions;
pub use public_input::PublicInputInstructions;
pub use range_check::RangeCheckInstructions;
pub use scalar_field::ScalarFieldInstructions;
pub use sponge::{SpongeCPU, SpongeInstructions};
pub use zero::ZeroInstructions;
