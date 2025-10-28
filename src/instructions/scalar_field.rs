//! Scalar field instructions interface.
//! Used for the scalar field of an elliptic curve, essentially these are
//! [FieldInstructions] + [DecompositionInstructions] + an associated type
//! `Scalar`.

use std::{fmt::Debug, hash::Hash};

use ff::PrimeField;

use super::FieldInstructions;
use crate::{
    instructions::DecompositionInstructions,
    types::{InnerConstants, InnerValue, Instantiable},
};

/// The set of circuit instructions for scalar field operations.
pub trait ScalarFieldInstructions<F>:
    FieldInstructions<F, Self::Scalar> + DecompositionInstructions<F, Self::Scalar>
where
    F: PrimeField,
    <Self::Scalar as InnerValue>::Element: PrimeField,
    Self::Scalar: Instantiable<F>,
{
    /// An assigned field element.
    type Scalar: InnerConstants + Clone + Debug + PartialEq + Eq + Hash;
}
