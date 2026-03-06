// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A Poseidon gadget built entirely on top of [`PilarChip`].
//!
//! This implementation does not use any specialised Poseidon gates or selectors.
//! Every operation (S-box, MDS, round-constant addition) is expressed through
//! the single Pilar arithmetic identity.

use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    hash::poseidon::{
        constants::{PoseidonField, NB_FULL_ROUNDS, NB_PARTIAL_ROUNDS, RATE, WIDTH},
        PoseidonChip, PoseidonState,
    },
    instructions::{
        hash::{HashCPU, HashInstructions},
        ArithInstructions, AssignmentInstructions, SpongeCPU, SpongeInstructions,
    },
    types::AssignedNative,
    CircuitField,
};

use super::{PilarChip, PilarConfig};

/// A Poseidon gadget that uses only the [`PilarChip`] for all in-circuit
/// arithmetic.
#[derive(Clone, Debug)]
pub struct PilarPoseidonGadget<F: PoseidonField> {
    chip: PilarChip<F>,
}

impl<F: PoseidonField> PilarPoseidonGadget<F> {
    /// Create a new gadget wrapping the given chip.
    pub fn new(chip: PilarChip<F>) -> Self {
        Self { chip }
    }

    /// Apply the S-box (x^5) to a single element.
    fn sbox(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.chip.pow(layouter, x, 5)
    }

    /// One full round of Poseidon: S-box on all elements, then MDS + round
    /// constants. Uses "shifted rounds": S-box first, then linear layer with
    /// next-round constants.
    fn full_round(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut [AssignedNative<F>; WIDTH],
        round_index: usize,
    ) -> Result<(), Error> {
        // S-box on every element.
        for i in 0..WIDTH {
            state[i] = self.sbox(layouter, &state[i])?;
        }

        // Linear layer: new_state[i] = sum_j MDS[i][j] * state[j] + rc[i].
        let rc = if round_index == NB_FULL_ROUNDS + NB_PARTIAL_ROUNDS - 1 {
            [F::ZERO; WIDTH]
        } else {
            F::ROUND_CONSTANTS[round_index + 1]
        };

        let mut new_state: [AssignedNative<F>; WIDTH] =
            core::array::from_fn(|_| state[0].clone());

        for i in 0..WIDTH {
            let terms: Vec<(F, AssignedNative<F>)> = (0..WIDTH)
                .map(|j| (F::MDS[i][j], state[j].clone()))
                .collect();
            new_state[i] = self.chip.linear_combination(layouter, &terms, rc[i])?;
        }

        *state = new_state;
        Ok(())
    }

    /// One partial round: S-box only on the last element, then MDS + round
    /// constants.
    fn partial_round(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut [AssignedNative<F>; WIDTH],
        round_index: usize,
    ) -> Result<(), Error> {
        // S-box only on the last element.
        state[WIDTH - 1] = self.sbox(layouter, &state[WIDTH - 1])?;

        // Linear layer.
        let rc = F::ROUND_CONSTANTS[round_index + 1];
        let mut new_state: [AssignedNative<F>; WIDTH] =
            core::array::from_fn(|_| state[0].clone());

        for i in 0..WIDTH {
            let terms: Vec<(F, AssignedNative<F>)> = (0..WIDTH)
                .map(|j| (F::MDS[i][j], state[j].clone()))
                .collect();
            new_state[i] = self.chip.linear_combination(layouter, &terms, rc[i])?;
        }

        *state = new_state;
        Ok(())
    }

    /// Full Poseidon permutation (no round-skip optimisation).
    fn permutation(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedNative<F>; WIDTH],
    ) -> Result<[AssignedNative<F>; WIDTH], Error> {
        let mut state = input.clone();

        // Add first-round constants.
        for (i, k0) in F::ROUND_CONSTANTS[0].iter().enumerate() {
            state[i] = self.chip.add_constant(layouter, &state[i], *k0)?;
        }

        // First half of full rounds.
        for round_index in 0..NB_FULL_ROUNDS / 2 {
            self.full_round(layouter, &mut state, round_index)?;
        }

        // Partial rounds.
        for round_index in (NB_FULL_ROUNDS / 2..).take(NB_PARTIAL_ROUNDS) {
            self.partial_round(layouter, &mut state, round_index)?;
        }

        // Second half of full rounds.
        for round_index in (NB_FULL_ROUNDS / 2 + NB_PARTIAL_ROUNDS..).take(NB_FULL_ROUNDS / 2) {
            self.full_round(layouter, &mut state, round_index)?;
        }

        Ok(state)
    }
}

// ---------------------------------------------------------------------------
// CPU-side: delegate to the existing PoseidonChip CPU implementation.
// ---------------------------------------------------------------------------

impl<F: PoseidonField> SpongeCPU<F, F> for PilarPoseidonGadget<F> {
    type StateCPU = PoseidonState<F>;

    fn init(input_len: Option<usize>) -> Self::StateCPU {
        <PoseidonChip<F> as SpongeCPU<F, F>>::init(input_len)
    }

    fn absorb(state: &mut Self::StateCPU, inputs: &[F]) {
        <PoseidonChip<F> as SpongeCPU<F, F>>::absorb(state, inputs)
    }

    fn squeeze(state: &mut Self::StateCPU) -> F {
        <PoseidonChip<F> as SpongeCPU<F, F>>::squeeze(state)
    }
}

impl<F: PoseidonField> HashCPU<F, F> for PilarPoseidonGadget<F> {
    fn hash(inputs: &[F]) -> F {
        let mut state = <Self as SpongeCPU<F, F>>::init(Some(inputs.len()));
        <Self as SpongeCPU<F, F>>::absorb(&mut state, inputs);
        <Self as SpongeCPU<F, F>>::squeeze(&mut state)
    }
}

// ---------------------------------------------------------------------------
// In-circuit sponge state.
// ---------------------------------------------------------------------------

/// In-circuit Poseidon state for the Pilar gadget.
#[derive(Clone, Debug)]
pub struct PilarPoseidonState<F: CircuitField> {
    register: [AssignedNative<F>; WIDTH],
    queue: Vec<AssignedNative<F>>,
    squeeze_position: usize,
    input_len: Option<usize>,
}

// ---------------------------------------------------------------------------
// SpongeInstructions
// ---------------------------------------------------------------------------

impl<F: PoseidonField> SpongeInstructions<F, AssignedNative<F>, AssignedNative<F>>
    for PilarPoseidonGadget<F>
{
    type State = PilarPoseidonState<F>;

    fn init(
        &self,
        layouter: &mut impl Layouter<F>,
        input_len: Option<usize>,
    ) -> Result<Self::State, Error> {
        let zero = self.chip.assign_fixed(layouter, F::ZERO)?;
        let capacity = self.chip.assign_fixed(
            layouter,
            F::from_u128(input_len.map(|l| l as u128).unwrap_or(1 << 64)),
        )?;

        let mut register: [AssignedNative<F>; WIDTH] =
            core::array::from_fn(|_| zero.clone());
        register[RATE] = capacity;

        Ok(PilarPoseidonState {
            register,
            queue: Vec::new(),
            squeeze_position: 0,
            input_len,
        })
    }

    fn absorb(
        &self,
        _layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
        inputs: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        state.queue.extend(inputs.to_vec());
        state.squeeze_position = 0;
        Ok(())
    }

    fn squeeze(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
    ) -> Result<AssignedNative<F>, Error> {
        if state.squeeze_position > 0 {
            if state.input_len.is_some() {
                panic!(
                    "Attempting to squeeze multiple times a fixed-size Poseidon sponge (PilarPoseidon)."
                )
            }
            debug_assert!(state.queue.is_empty());
            let output = state.register[state.squeeze_position % RATE].clone();
            state.squeeze_position = (state.squeeze_position + 1) % RATE;
            return Ok(output);
        }

        match state.input_len {
            None => {
                let padding =
                    self.chip.assign_fixed(layouter, F::from(state.queue.len() as u64))?;
                state.queue.push(padding);
            }
            Some(len) => {
                if state.queue.len() != len {
                    panic!(
                        "Inconsistent lengths in fixed-size Poseidon sponge (PilarPoseidon). Expected: {}, found: {}.",
                        len, state.queue.len()
                    )
                }
            }
        }

        for chunk in state.queue.chunks(RATE) {
            for (entry, value) in state.register.iter_mut().zip(chunk.iter()) {
                *entry = self.chip.add(layouter, entry, value)?;
            }
            state.register = self.permutation(layouter, &state.register)?;
        }

        state.queue = Vec::new();
        state.squeeze_position = 1 % RATE;
        Ok(state.register[0].clone())
    }
}

// ---------------------------------------------------------------------------
// HashInstructions
// ---------------------------------------------------------------------------

impl<F: PoseidonField> HashInstructions<F, AssignedNative<F>, AssignedNative<F>>
    for PilarPoseidonGadget<F>
{
    fn hash(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedNative<F>],
    ) -> Result<AssignedNative<F>, Error> {
        let mut state = SpongeInstructions::init(self, layouter, Some(inputs.len()))?;
        self.absorb(layouter, &mut state, inputs)?;
        self.squeeze(layouter, &mut state)
    }
}

// ---------------------------------------------------------------------------
// FromScratch (test infrastructure).
// ---------------------------------------------------------------------------

#[cfg(any(test, feature = "testing"))]
impl<F: PoseidonField> crate::testing_utils::FromScratch<F> for PilarPoseidonGadget<F> {
    type Config = PilarConfig;

    fn new_from_scratch(config: &Self::Config) -> Self {
        use crate::utils::ComposableChip;
        PilarPoseidonGadget::new(PilarChip::new(config, &()))
    }

    fn configure_from_scratch(
        meta: &mut midnight_proofs::plonk::ConstraintSystem<F>,
        instance_columns: &[midnight_proofs::plonk::Column<midnight_proofs::plonk::Instance>; 2],
    ) -> Self::Config {
        <PilarChip<F> as crate::testing_utils::FromScratch<F>>::configure_from_scratch(
            meta,
            instance_columns,
        )
    }

    fn load_from_scratch(
        &self,
        _layouter: &mut impl midnight_proofs::circuit::Layouter<F>,
    ) -> Result<(), midnight_proofs::plonk::Error> {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::{
        field::AssignedNative,
        instructions::{hash::tests::test_hash, sponge::tests::test_sponge},
        pilar::PilarChip,
    };

    use super::PilarPoseidonGadget;

    type F = midnight_curves::Fq;

    #[test]
    fn test_pilar_poseidon_hash() {
        // Small inputs to keep runtime reasonable (no round-skip optimisation).
        test_hash::<
            F,
            AssignedNative<F>,
            AssignedNative<F>,
            PilarPoseidonGadget<F>,
            PilarChip<F>,
        >(true, "pilar_poseidon", 2, 14);
    }

    #[test]
    fn test_pilar_poseidon_sponge() {
        test_sponge::<
            F,
            AssignedNative<F>,
            AssignedNative<F>,
            PilarPoseidonGadget<F>,
            PilarChip<F>,
        >(true, "pilar_poseidon", 18);
    }
}
