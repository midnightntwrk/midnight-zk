//! Native and non-native arithmetic
pub mod decomposition;
pub mod foreign;
pub mod native;

use midnight_proofs::circuit::AssignedCell;
pub use native::{AssignedBounded, NativeChip, NativeConfig, NativeGadget};

/// AssignedNative
pub type AssignedNative<F> = AssignedCell<F, F>;
