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

use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

pub mod arity;
pub mod operations;

#[derive(Clone, Debug, PartialEq, Encode, Decode, Serialize, Deserialize)]
/// A ZKIR instruction is parametrized by a ZKIR operation
/// and a series of inputs and outputs (in the form of value names).
///
/// Some operations have a specific fixed arity.
/// The number of inputs and outputs must coincide with the input and output
/// arity of the operation. We perform run-time arity checks when reading
/// programs (list of instructions).
pub struct Instruction {
    /// The operation performed by this instruction.
    #[serde(rename = "op")]
    pub operation: operations::Operation,

    /// Names of the inputs of this instruction.
    #[serde(default)]
    pub inputs: Vec<String>,

    /// Names of the outputs of this instruction.
    #[serde(default)]
    pub outputs: Vec<String>,
}
