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

//! A chip that implements decomposition of a Field element in arbitrary sized
//! limbs by combining in a non black-box way the NativeChip and the
//! Pow2RangeChip.
//!
//! It implements:
//! (1) limb decomposition of field element of `num_bits` in `limb_size` sized
//! limbs for a fixed limb size where the most significaunt limb might be
//! smaller if num_bits % limb_size != 0 (2) compute an optimal limb
//! decomposition of a number to prove it is smaller than a 2^r fixed bound
pub mod chip;
pub mod cpu_utils;
pub mod instructions;

pub mod pow2range;
#[cfg(test)]
mod tests;
