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

//! Scalar field instructions interface.
//! Used for the scalar field of an elliptic curve, essentially these are
//! [FieldInstructions] + [DecompositionInstructions] + an associated type
//! `Scalar`.

use std::{fmt::Debug, hash::Hash};

use super::FieldInstructions;
use crate::{
    instructions::DecompositionInstructions,
    types::{InnerConstants, InnerValue, Instantiable},
    CircuitField,
};

/// The set of circuit instructions for scalar field operations.
pub trait ScalarFieldInstructions<F>:
    FieldInstructions<F, Self::Scalar> + DecompositionInstructions<F, Self::Scalar>
where
    F: CircuitField,
    <Self::Scalar as InnerValue>::Element: CircuitField,
    Self::Scalar: Instantiable<F>,
{
    /// An assigned field element.
    type Scalar: InnerConstants + Clone + Debug + PartialEq + Eq + Hash;
}
