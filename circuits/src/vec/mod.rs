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

//! Vector module.
//! This modules contains the types and gadgets to handle variable-length
//! vectors. This type allow the length of the vector to be a witness.

/// Module containing basic vector types and utilities.
pub mod vector;
/// Gadget for handling vectors of elements that fit in the native field:
/// Native elements, bytes and bits.
pub mod vector_gadget;
pub use vector::*;
