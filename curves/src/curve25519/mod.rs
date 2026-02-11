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

//! Curve25519.
//!
//! Defined over the base field `Fp`.

mod affine;
mod curve;
mod fp;

pub use affine::Curve25519Affine;
pub use curve::{Curve25519, Curve25519Subgroup, CURVE_A, CURVE_D};
pub use curve25519_dalek::{edwards::CompressedEdwardsY, Scalar};
pub use fp::Fp;
