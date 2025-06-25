//! Native instructions interface.

use ff::PrimeField;

use super::RangeCheckInstructions;
use crate::{
    instructions::{
        AssertionInstructions, BinaryInstructions, ComparisonInstructions, ControlFlowInstructions,
        DecompositionInstructions, EqualityInstructions, FieldInstructions,
        UnsafeConversionInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative},
};

/// The set of circuit all native instructions.
pub trait NativeInstructions<F>:
    FieldInstructions<F, AssignedNative<F>>
    + BinaryInstructions<F>
    + AssertionInstructions<F, AssignedBit<F>>
    + AssertionInstructions<F, AssignedByte<F>>
    + EqualityInstructions<F, AssignedBit<F>>
    + ControlFlowInstructions<F, AssignedBit<F>>
    + DecompositionInstructions<F, AssignedNative<F>>
    + ComparisonInstructions<F, AssignedNative<F>>
    + RangeCheckInstructions<F, AssignedNative<F>>
    + UnsafeConversionInstructions<F, AssignedNative<F>, AssignedByte<F>>
where
    F: PrimeField,
{
}
