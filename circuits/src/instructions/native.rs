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

//! Native instructions interface.

use ff::PrimeField;

use super::{DivisionInstructions, RangeCheckInstructions};
use crate::{
    instructions::{
        AssertionInstructions, BinaryInstructions, ComparisonInstructions, ControlFlowInstructions,
        DecompositionInstructions, EqualityInstructions, FieldInstructions,
        UnsafeConversionInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative},
};

/// The set of circuit all native instructions.
pub trait NativeInstructions<F>:
    FieldInstructions<F, AssignedNative<F>>
    + BinaryInstructions<F>
    + AssertionInstructions<F, AssignedBit<F>>
    + AssertionInstructions<F, AssignedByte<F>>
    + EqualityInstructions<F, AssignedBit<F>>
    + ControlFlowInstructions<F, AssignedBit<F>>
    + DecompositionInstructions<F, AssignedNative<F>>
    + ComparisonInstructions<F, AssignedNative<F>>
    + RangeCheckInstructions<F, AssignedNative<F>>
    + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedByte<F>>
    + DivisionInstructions<F>
where
    F: PrimeField,
{
}
