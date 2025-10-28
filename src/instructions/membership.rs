//! Membership instruction interface. This interface assumes that the proof
//! for membership and non-membership have the same type.

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::ErrorFront as Error};

use crate::types::AssignedBit;

/// Instructions for membership and non-membership chip
pub trait MembershipInstructions<F: PrimeField> {
    /// Assigned elements of the sets
    type AssignedElement;
    /// Assigned Proof of membership
    type AssignedMemProof;
    /// Assigned succinct representation of the set
    type AssignedSet;

    /// Given a proof `pi`, an element `val` a set `set`, and bool `in_set`,
    /// this function returns `in_set` if `proof` is valid for `val` in set
    /// `set`. The value `in_set` is witnessed by the prover.
    fn is_in_set(
        &self,
        layouter: &mut impl Layouter<F>,
        val: &Self::AssignedElement,
        proof: &Self::AssignedMemProof,
        set: &Self::AssignedSet,
        in_set: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error>;
}
