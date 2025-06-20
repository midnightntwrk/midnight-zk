//! Trait for modular, composable chips.

use std::fmt::Debug;

use ff::PrimeField;
use halo2_proofs::{
    circuit::{Chip, Layouter},
    plonk::{ConstraintSystem, Error},
};

/// Provides a common interface for layering chips with shared resources.
pub trait ComposableChip<F>: Chip<F> + Clone + Debug
where
    F: PrimeField,
{
    /// Resources that can be used by other chips or gadgets,
    /// typically sub-chip configurations and columns.
    type SharedResources;

    /// Instruction set dependencies of the chip.
    /// This chip will need to be provided with subchips that implement these
    /// instructions.
    type InstructionDeps;

    /// Initialize the chip.
    fn new(config: &Self::Config, sub_chips: &Self::InstructionDeps) -> Self;

    /// Configure the chip.
    /// Receives the underlying chips and columns it needs via
    /// Self::SharedResources. This method must not allocate any resource in
    /// the constraint system that is intended to be shared by other chips.
    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_resources: &Self::SharedResources,
    ) -> Self::Config;

    /// Load all tables (including those of underlying chips taken as configs)
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error>;
}
