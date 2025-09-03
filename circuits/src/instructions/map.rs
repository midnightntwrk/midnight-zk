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

//! Map instructions interface.
//!
//! It provides (in-circuit) functions for creating a map from a specified input
//! type into another.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::types::{AssignedNative, InnerValue};

/// The set of off-circuit instructions for mapping operations.
pub trait MapCPU<F, Key, Value> {
    /// Initializes a new map where all keys point to `default`.
    fn new(default: &Value) -> Self;

    /// A (cryptographically unequivocal) succinct representation of the map.
    fn succinct_repr(&self) -> F;

    /// Inserts a new key -> value entry into the map.
    fn insert(&mut self, key: &Key, value: &Value);

    /// Returns the value associated to a given key.
    /// Unlike a standard `HashMap` every single key has a value in this
    /// structure (possibly the default value it was created with).
    fn get(&self, key: &Key) -> Value;
}

/// The set of circuit instructions for mapping operations.
pub trait MapInstructions<F, AssignedKey, AssignedValue>
where
    F: PrimeField,
    AssignedKey: InnerValue,
    AssignedValue: InnerValue,
{
    /// The CPU version of the map.
    type MapCPU: MapCPU<F, AssignedKey::Element, AssignedValue::Element>;

    /// Initializes a new in-circuit map from the given off-circuit map.
    fn init(
        &mut self,
        layouter: &mut impl Layouter<F>,
        map: Value<Self::MapCPU>,
    ) -> Result<(), Error>;

    /// A (cryptographically unequivocal) succinct representation of the map.
    fn succinct_repr(&self) -> AssignedNative<F>;

    /// Inserts a new key -> value entry into the map.
    /// This call introduces in-circuit constraints that guarantee that the
    /// insertion was done correctly.
    fn insert(
        &mut self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedKey,
        value: &AssignedValue,
    ) -> Result<(), Error>;

    /// Returns the value associated to a given key.
    /// Unlike a standard `HashMap` every single key has a value in this
    /// structure (possibly the default value it was created with).
    /// This call introduces in-circuit constraints that guarantee that the
    /// returned value is correct.
    fn get(
        &self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedKey,
    ) -> Result<AssignedValue, Error>;
}
