//! A chip that implements decomposition of a Field element in arbitrary sized
//! limbs by combining in a non black-box way the NativeChip and the
//! Pow2RangeChip.
//!
//! It implements:
//! (1) limb decomposition of field element of `num_bits` in `limb_size` sized
//! limbs for a fixed limb size where the most significaunt limb might be
//! smaller if num_bits % limb_size != 0 (2) compute an optimal limb
//! decomposition of a number to prove it is smaller than a 2^r fixed bound
pub mod chip;
pub mod cpu_utils;
pub mod instructions;

pub mod pow2range;
#[cfg(test)]
mod tests;
