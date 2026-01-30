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

//! Safe wrapper around k256::FieldElement.
//!
//! k256's FieldElement uses lazy reduction, meaning field elements may not be
//! in canonical form after arithmetic operations. This wrapper ensures that
//! comparison and predicate methods normalize before operating, eliminating
//! the risk of incorrect results.
//!
//! See: <https://github.com/RustCrypto/elliptic-curves/issues/531>

use subtle::{Choice, ConstantTimeEq};

/// secp256k1 base field element with safe comparison semantics.
///
/// This wrapper normalizes field elements before comparison and predicate
/// operations to ensure correct results regardless of internal representation.
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct Fp(pub(crate) k256::FieldElement);

impl Fp {
    /// The zero element.
    pub const ZERO: Self = Self(k256::FieldElement::ZERO);

    /// The multiplicative identity.
    pub const ONE: Self = Self(k256::FieldElement::ONE);

    /// Returns the inner k256::FieldElement.
    #[inline]
    pub fn inner(&self) -> &k256::FieldElement {
        &self.0
    }

    /// Consumes the wrapper and returns the inner k256::FieldElement.
    #[inline]
    pub fn into_inner(self) -> k256::FieldElement {
        self.0
    }

    /// Normalizes the field element to canonical form.
    #[inline]
    pub fn normalize(&self) -> Self {
        Self(self.0.normalize())
    }

    /// Normalizes in place.
    #[inline]
    pub fn normalize_mut(&mut self) {
        self.0 = self.0.normalize();
    }
}

// ============================================================================
// Safe predicate methods (normalize before checking)
// ============================================================================

impl Fp {
    /// Returns true if this element is zero.
    /// Normalizes before checking to ensure correct result.
    #[inline]
    pub fn is_zero(&self) -> Choice {
        self.0.normalize().is_zero()
    }

    /// Returns true if this element is odd.
    /// Normalizes before checking to ensure correct result.
    #[inline]
    pub fn is_odd(&self) -> Choice {
        self.0.normalize().is_odd()
    }

    /// Returns true if this element is even.
    /// Normalizes before checking to ensure correct result.
    #[inline]
    pub fn is_even(&self) -> Choice {
        self.0.normalize().is_even()
    }
}

// ============================================================================
// Safe comparison (normalize before comparing)
// ============================================================================

impl PartialEq for Fp {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.normalize().ct_eq(&other.0.normalize()).into()
    }
}

impl Eq for Fp {}

impl ConstantTimeEq for Fp {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.normalize().ct_eq(&other.0.normalize())
    }
}
