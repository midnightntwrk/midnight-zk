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
    pub spreaded_limb_09: AssignedSpreaded<F, 9>,
    pub spreaded_limb_11: AssignedSpreaded<F, 11>,
    pub spreaded_limb_02: AssignedSpreaded<F, 2>,
}

/// The assigned spreaded values of 7-14-5-6 limbs (in big-endian) for the
/// register E of 32 bits. Input type of Σ₁(E).
#[derive(Clone, Debug)]
pub(super) struct LimbsOfE<F: PrimeField> {
    pub spreaded_limb_07: AssignedSpreaded<F, 7>,
    pub spreaded_limb_14: AssignedSpreaded<F, 14>,
    pub spreaded_limb_05: AssignedSpreaded<F, 5>,
    pub spreaded_limb_06: AssignedSpreaded<F, 6>,
}
