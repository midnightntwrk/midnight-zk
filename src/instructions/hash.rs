//! Hashing instructions interface.
//!
//! It provides functions for (in-circuit) hashing from a specified input type
//! to another output one.

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::ErrorFront as Error};

use super::{SpongeCPU, SpongeInstructions};
use crate::types::InnerValue;

/// The set of off-circuit instructions for hashing operations.
pub trait HashCPU<Input, Output>: SpongeCPU<Input, Output> {
    /// Hash the given input into the designated output type.
    fn hash(input: &[Input]) -> Output {
        let mut state = <Self as SpongeCPU<Input, Output>>::init();
        <Self as SpongeCPU<Input, Output>>::absorb(&mut state, input);
        <Self as SpongeCPU<Input, Output>>::squeeze(&mut state)
    }
}

/// The set of circuit instructions for hashing operations.
pub trait HashInstructions<F, Input, Output>:
    HashCPU<Input::Element, Output::Element> + SpongeInstructions<F, Input, Output>
where
    F: PrimeField,
    Input: InnerValue,
    Output: InnerValue,
{
    /// Hash the given input into the designated output type.
    fn hash(&self, layouter: &mut impl Layouter<F>, input: &[Input]) -> Result<Output, Error> {
        let mut state = self.init(layouter)?;
        self.absorb(layouter, &mut state, input)?;
        self.squeeze(layouter, &mut state)
    }
}
