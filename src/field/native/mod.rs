//! Implementation of native field chip and gadget. The [NativeChip] only
//! implements instructions that can be implemented with the arithmetic
//! identity. The [NativeGadget] includes the usage of lookup tables, and
//! implements range checks and decomposition.
pub mod native_chip;
pub mod native_gadget;

pub use native_chip::*;
pub use native_gadget::*;
