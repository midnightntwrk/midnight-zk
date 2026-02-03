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

//! secp256k1 implementation using k256 crate.
//!
//! This module provides wrappers around k256's types with safe comparison
//! semantics and FieldEncoding implementations. The base field wrapper
//! normalizes before comparisons to avoid issues with k256's lazy reduction
//! strategy.

use core::mem::size_of;

mod base_field;
mod curve;

pub use base_field::Fp;
pub use curve::{K256Affine, K256};

/// secp256k1 scalar field - direct alias to k256::Scalar.
pub type Fq = k256::Scalar;

// ============================================================================
// FieldEncoding for k256::Scalar (Fq)
// ============================================================================

impl crate::FieldEncoding for k256::Scalar {
    type Bytes = [u8; 32];

    const REPR_ENDIAN: crate::Endian = crate::Endian::BE;

    fn to_le_bytes(&self) -> Self::Bytes {
        use ff::PrimeField;
        let mut bytes: [u8; 32] = self.to_repr().into();
        bytes.reverse();
        bytes
    }

    fn to_be_bytes(&self) -> Self::Bytes {
        use ff::PrimeField;
        self.to_repr().into()
    }

    fn from_le_bytes(bytes: &[u8]) -> Option<Self> {
        use ff::PrimeField;
        if bytes.len() != size_of::<Self::Repr>() {
            return None;
        }
        let mut be_bytes = [0u8; 32];
        be_bytes.copy_from_slice(bytes);
        be_bytes.reverse();
        Self::from_repr(k256::FieldBytes::from(be_bytes)).into()
    }

    fn from_be_bytes(bytes: &[u8]) -> Option<Self> {
        use core::convert::TryInto;
        use ff::PrimeField;
        if bytes.len() != size_of::<Self::Repr>() {
            return None;
        }
        let be_bytes: [u8; 32] = bytes.try_into().ok()?;
        Self::from_repr(k256::FieldBytes::from(be_bytes)).into()
    }

    fn to_biguint(&self) -> num_bigint::BigUint {
        num_bigint::BigUint::from_bytes_be(&self.to_be_bytes())
    }

    fn from_biguint(n: &num_bigint::BigUint) -> Option<Self> {
        let bytes = n.to_bytes_be();
        if bytes.len() > size_of::<Self::Repr>() {
            return None;
        }
        // Pad with leading zeros for big-endian.
        let mut padded = [0u8; 32];
        padded[32 - bytes.len()..].copy_from_slice(&bytes);
        Self::from_be_bytes(&padded)
    }
}
