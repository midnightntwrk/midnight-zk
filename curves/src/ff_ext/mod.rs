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

//! Field extension traits and utilities.

pub mod cubic;
pub mod inverse;
pub mod jacobi;
pub mod quadratic;

use subtle::{Choice, ConstantTimeEq};

/// Legendre symbol trait for computing quadratic residuosity.
pub trait Legendre {
    /// Compute the Legendre symbol of this field element.
    ///
    /// Returns:
    /// * 1 if this element is a quadratic residue
    /// * -1 if this element is a quadratic non-residue
    /// * 0 if this element is zero
    fn legendre(&self) -> i64;

    /// Returns `Choice(1)` if this element is a quadratic non-residue.
    #[inline(always)]
    fn ct_quadratic_non_residue(&self) -> Choice {
        self.legendre().ct_eq(&-1)
    }

    /// Returns `Choice(1)` if this element is a quadratic residue.
    /// Note: 0 is considered a quadratic residue.
    #[inline(always)]
    fn ct_quadratic_residue(&self) -> Choice {
        // The legendre symbol returns 0 for 0
        // and 1 for quadratic residues,
        // we consider 0 a square hence quadratic residue.
        self.legendre().ct_ne(&-1)
    }
}

/// Extension field trait.
pub trait ExtField: ff::Field {
    /// The non-residue used to construct the extension.
    const NON_RESIDUE: Self;

    /// Multiply this element by the non-residue.
    #[must_use]
    fn mul_by_nonresidue(&self) -> Self {
        Self::NON_RESIDUE * self
    }

    /// Apply the Frobenius endomorphism.
    fn frobenius_map(&mut self, power: usize);
}

#[macro_export]
macro_rules! extend_field_legendre {
    ($field:ident ) => {
        impl $crate::ff_ext::Legendre for $field {
            #[inline(always)]
            fn legendre(&self) -> i64 {
                self.jacobi()
            }
        }
    };
}
