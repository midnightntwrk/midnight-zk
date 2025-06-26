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

use core::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::circuit::Value;
#[cfg(any(test, feature = "testing"))]
use rand::RngCore;

use crate::types::AssignedNative;

/// Trait for dealing with public inputs. `Instantiable` is implemented on
/// off-circuit types to determine the way these types are transformed into
/// vectors of native values.
/// Analogous functions exists for constraining public inputs in-circuit in
/// the [crate::instructions::PublicInputInstructions] trait.
pub trait Instantiable<F: PrimeField>: InnerValue {
    /// This function is the off-circuit analog of
    /// [crate::instructions::PublicInputInstructions::as_public_input].
    fn as_public_input(element: &<Self as InnerValue>::Element) -> Vec<F>;
}

/// Trait for accessing the value inside assigned circuit elements.
pub trait InnerValue: Clone + Debug {
    /// Represents the unassigned type corresponding to the [InnerValue]
    type Element: Clone + Debug;

    /// Returns the value of the assigned element.
    fn value(&self) -> Value<Self::Element>;
}

impl<T: InnerValue, const L: usize> InnerValue for [T; L] {
    type Element = [T::Element; L];

    fn value(&self) -> Value<Self::Element> {
        let val = Value::from_iter(self.iter().map(|val| val.value()));
        // We know sizes will match due to the type system. The problem is
        // that the type Value is not right enough.
        val.map(|v: Vec<T::Element>| v.try_into().unwrap())
    }
}

/// Trait for accessing constant values of the inner value type of an assigned
/// element.
pub trait InnerConstants: InnerValue {
    /// The zero of Self::Element (additive identity).
    fn inner_zero() -> Self::Element;

    /// The unit of Self::Element (multiplicative identity and/or additive
    /// generator).
    fn inner_one() -> Self::Element;
}

impl<F: PrimeField> Instantiable<F> for AssignedNative<F> {
    fn as_public_input(element: &F) -> Vec<F> {
        vec![*element]
    }
}

impl<F: PrimeField> InnerValue for AssignedNative<F> {
    type Element = F;
    #[must_use]
    fn value(&self) -> Value<F> {
        self.value().cloned()
    }
}

impl<F: PrimeField> InnerConstants for AssignedNative<F> {
    fn inner_zero() -> F {
        F::ZERO
    }

    fn inner_one() -> F {
        F::ONE
    }
}

#[cfg(any(test, feature = "testing"))]
/// A trait for types that can be inverted. This should only
/// be used for testing.
pub trait Invertible {
    /// Returns the multiplicative inverse of the given value.
    ///
    /// # Panics
    ///
    /// If the given value does not have an inverse.
    fn invert(&self) -> Self;
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> Invertible for F {
    fn invert(&self) -> F {
        self.invert().unwrap()
    }
}

#[cfg(any(test, feature = "testing"))]
/// A trait for types that can be sampled at random. This should only
/// be used for testing.
pub trait Sampleable: InnerValue {
    /// Returns a random inner element, given a random number generator.
    fn sample_inner(rng: impl RngCore) -> Self::Element;
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> Sampleable for AssignedNative<F> {
    fn sample_inner(rng: impl RngCore) -> F {
        F::random(rng)
    }
}
