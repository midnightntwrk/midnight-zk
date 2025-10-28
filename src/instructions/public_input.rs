//! Public input instructions interface.
//!
//! It provides functions for constraining public inputs.
//!
//! This trait is parametrized by the resulting `Assigned` type (a generic of
//! this trait that must implement [crate::types::InnerValue] and
//! [Instantiable]).

use ff::PrimeField;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};

use crate::types::{AssignedNative, Instantiable};

/// The set of circuit instructions for constraining public inputs.
pub trait PublicInputInstructions<F, Assigned>
where
    F: PrimeField,
    Assigned: Instantiable<F>,
{
    /// Returns the cells associated with the given assigned value with the same
    /// format as a public input. This function is the in-circuit analog of
    /// [Instantiable::as_public_input].
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &Assigned,
    ) -> Result<Vec<AssignedNative<F>>, Error>;

    /// Constrains the given assigned value as a public input to the circuit.
    ///
    /// One can think of this function as the composition of
    /// [PublicInputInstructions::as_public_input] with the halo2 constrain
    /// instance mechanism.
    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &Assigned,
    ) -> Result<(), Error>;

    /// Same as [assign](crate::instructions::AssignmentInstructions::assign),
    /// but it immediately constrains the assigned value as a public input.
    /// This allows the implementer of this function to skip some in-circuit
    /// checks on the structure of the assigned value, which will be
    /// guaranteed to hold through the public input bind.
    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Assigned::Element>,
    ) -> Result<Assigned, Error>;
}
