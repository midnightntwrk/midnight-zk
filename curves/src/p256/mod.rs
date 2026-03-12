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

//! secp256r1 / NIST P-256 implementation using the p256 crate.
//!
//! Unlike the k256 module, no base field wrapper is needed here. The p256 crate
//! uses Montgomery form internally and elements are always in canonical
//! representation, so `p256::FieldElement` already implements all required
//! traits correctly (including `PartialEq` and `ConstantTimeEq`).

mod curve;

pub use curve::{P256Affine, P256};

/// secp256r1 base field - direct alias to p256::FieldElement.
/// No wrapper needed: p256 uses Montgomery form with canonical representation.
pub type Fp = p256::FieldElement;

/// secp256r1 scalar field - direct alias to p256::Scalar.
pub type Fq = p256::Scalar;
