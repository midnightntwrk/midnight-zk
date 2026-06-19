//! Generic extension-field building blocks for the bn256 tower.
//!
//! These are the reusable layers the concrete tower is built from:
//! `Fq2 = QuadExtField<Fq>`, `Fq6 = CubicExtField<Fq2>`, `Fq12 = QuadExtField<Fq6>`.

pub mod cubic;
pub mod quadratic;

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
