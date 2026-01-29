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

//! secp256k1 implementation using k256 crate.
//!
//! This module re-exports k256's field types directly and provides a wrapper
//! curve points.

mod curve;

pub use curve::{K256Affine, K256};

/// secp256k1 base field - direct alias to k256::FieldElement.
pub type Fp = k256::FieldElement;

/// secp256k1 scalar field - direct alias to k256::Scalar.
pub type Fq = k256::Scalar;
