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

//! Native and non-native arithmetic
pub mod decomposition;
pub mod foreign;
pub mod native;

use midnight_proofs::circuit::AssignedCell;
pub use native::{AssignedBounded, NativeChip, NativeConfig, NativeGadget};

/// AssignedNative
pub type AssignedNative<F> = AssignedCell<F, F>;
