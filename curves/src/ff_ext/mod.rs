//! Field extension traits and utilities.

pub mod inverse;
pub mod jacobi;

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
