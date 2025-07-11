use ff::PrimeField;

use crate::field::AssignedNative;

/// Assigned plain value of given number of bits L.
#[derive(Clone, Debug)]
pub(super) struct AssignedPlain<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// Assigned spreaded value of given number of bits L.
#[derive(Clone, Debug)]
pub(super) struct AssignedSpreaded<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// A pair of assigned plain-spreaded values guaranteed to be consistent.
/// The plain value is also guaranteed to be in the range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedPlainSpreaded<F: PrimeField, const L: usize> {
    pub plain: AssignedPlain<F, L>,
    pub spreaded: AssignedSpreaded<F, L>,
}

/// The assigned spreaded values of 10-9-11-2 limbs (in big-endian) for the
/// register A of 32 bits. Input type of Σ₀(A).
#[derive(Clone, Debug)]
pub(super) struct LimbsOfA<F: PrimeField> {
    pub spreaded_limb_10: AssignedSpreaded<F, 10>,
    pub spreaded_limb_9: AssignedSpreaded<F, 9>,
    pub spreaded_limb_11: AssignedSpreaded<F, 11>,
    pub spreaded_limb_2: AssignedSpreaded<F, 2>,
}
