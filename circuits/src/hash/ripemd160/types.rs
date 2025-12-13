use ff::PrimeField;

use crate::field::AssignedNative;

/// An assigned 32-bit word, represented by a field element for 4 bytes in
/// little-endian order.
#[derive(Clone, Debug)]
pub(super) struct AssignedWord<F: PrimeField>(pub AssignedNative<F>);

/// An assigned value in spreaded form, it is guaranteed to be the spreaded form
/// of a value in the range [0, 2^L).
#[derive(Clone, Debug)]
pub(super) struct AssignedSpreaded<F: PrimeField, const L: usize>(pub AssignedNative<F>);

/// The assigned values of the state vector (h0, h1, h2, h3, h4).
/// They are provided and updated for each block.
#[derive(Clone, Debug)]
pub(super) struct State<F: PrimeField> {
    pub(super) h0: AssignedWord<F>,
    pub(super) h1: AssignedWord<F>,
    pub(super) h2: AssignedWord<F>,
    pub(super) h3: AssignedWord<F>,
    pub(super) h4: AssignedWord<F>,
}
