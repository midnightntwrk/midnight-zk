//! Traits for working at the circuit level.

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::ConstraintSystem};

use crate::{cells::CellReprSize, circuit::configuration::AutoConfigure, error::PlonkError};

pub mod configuration;
pub mod injected;

/// Super trait for extracting IO from an abstract circuit.
pub trait AbstractCircuitIO<F: PrimeField> {
    /// Type that implements the main logic.
    type Chip: CircuitInitialization<F>;
    /// Input type of the chip.
    type Input: CellReprSize;
    /// Output type of the chip.
    type Output: CellReprSize;
}

/// Trait for configuring the arguments of a chip.
///
/// If the chip has no arguments the type should be `()`. In that case the type
/// can implement [`NoChipArgs`] which will automatically implement this trait
/// with that type.
pub trait ChipArgs<F: PrimeField> {
    /// Type of the arguments taken by the chip.
    type Args: Default;

    /// Returns an instance of the arguments.
    fn chip_args(&self) -> Self::Args {
        Default::default()
    }
}

/// Trait for configuring [`ChipArgs`] for types that don't have arguments.
///
/// Sets the type of the arguments to `()`.
pub trait NoChipArgs {}

impl<F, T> ChipArgs<F> for T
where
    F: PrimeField,
    T: NoChipArgs + AbstractCircuitIO<F>,
{
    type Args = ();
}

/// Adaptor trait for integrating chips with the extractor.
pub trait CircuitInitialization<F: PrimeField> {
    /// Configuration of the circuit.
    type Config: Clone + std::fmt::Debug;
    /// Arguments required by the circuit.
    type Args: Default;
    /// Configuration columns of the circuit.
    type ConfigCols: Clone + std::fmt::Debug + AutoConfigure;

    /// Creates a new instance of the chip.
    fn new_chip(config: &Self::Config, args: Self::Args) -> Self;

    /// Creates an instance of the chip's configuration.
    fn configure_circuit(
        meta: &mut ConstraintSystem<F>,
        columns: &Self::ConfigCols,
    ) -> Self::Config;

    /// Loads internal information of the chip.
    fn load_chip(
        &self,
        layouter: &mut impl Layouter<F>,
        config: &Self::Config,
    ) -> Result<(), PlonkError>;
}
