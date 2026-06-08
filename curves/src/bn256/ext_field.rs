//! Extension field trait used by the bn256 tower.

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
