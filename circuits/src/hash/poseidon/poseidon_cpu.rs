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

use std::io::{self, Read};

use ff::PrimeField;
use group::GroupEncoding;
use midnight_proofs::transcript::{Hashable, Sampleable, TranscriptHash};

use super::{
    constants::{PoseidonField, NB_FULL_ROUNDS, NB_PARTIAL_ROUNDS, RATE, WIDTH},
    round_skips::{PreComputedRoundCPU, PreComputedRoundCircuit},
    PoseidonChip, NB_SKIPS_CIRCUIT,
};
use crate::{
    field::foreign::params::MultiEmulationParams as MEP,
    instructions::{hash::HashCPU, SpongeCPU},
    types::{AssignedForeignPoint, Instantiable},
};

/// Number of times the linear part of the partial rounds is skipped in the
/// Poseidon cpu implemetation (0 is the default implementation without skips at
/// all).
pub(crate) const NB_SKIPS_CPU: usize = 2;

/// Off-circuit Poseidon state.
#[derive(Clone, Debug)]
pub struct PoseidonState<F: PoseidonField> {
    pre_computed: PreComputedRoundCPU<F>,
    register: [F; WIDTH],
    queue: Vec<F>,
    squeeze_position: usize,
    input_len: Option<usize>,
}

// Applies the MDS matrix to a state and adds the round constants. All arguments
// have length `WIDTH`. To save the addition cost, the implementation is done by
// mutating the `constants` slice, and eventually copying it into `state`.
fn linear_layer<F: PoseidonField>(state: &mut [F], constants: &mut [F]) {
    #[allow(clippy::needless_range_loop)]
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            constants[i] += F::MDS[i][j] * state[j];
        }
    }
    state.copy_from_slice(constants);
}

/// A cpu version of the full round of Poseidon's permutation. Operates by
/// mutating the `state` argument (length `WIDTH`).
pub(crate) fn full_round_cpu<F: PoseidonField>(round_index: usize, state: &mut [F]) {
    state.iter_mut().for_each(|x| *x = x.square().square() * *x);
    let mut new_state = if round_index == NB_FULL_ROUNDS + NB_PARTIAL_ROUNDS - 1 {
        [F::ZERO; WIDTH]
    } else {
        F::ROUND_CONSTANTS[round_index + 1]
    };
    linear_layer(state, &mut new_state);
}

// A cpu version of Poseidon with `1 + NB_SKIPS_CIRCUIT` partial rounds.
fn partial_round_cpu<F: PoseidonField>(
    pre_computed: &PreComputedRoundCPU<F>,
    round_batch_index: usize,
    state: &mut [F], // Length `WIDTH`.
) {
    pre_computed
        .partial_round_id
        .eval::<NB_SKIPS_CPU>(&pre_computed.round_constants[round_batch_index], state);
}

/// A cpu version of Poseidon with `1 + NB_SKIPS_CIRCUIT` partial rounds. Also
/// returns the values of the last column of the skipped rows
/// (`NB_SKIPS_CIRCUIT` elements) as needed to fill the circuit's rows.
pub(crate) fn partial_round_cpu_for_circuits<F: PoseidonField>(
    pre_computed: &PreComputedRoundCircuit<F>,
    round_batch_index: usize,
    state: &mut [F], // Length `WIDTH`.
) -> [F; NB_SKIPS_CIRCUIT] {
    pre_computed
        .partial_round_id
        .eval::<NB_SKIPS_CIRCUIT>(&pre_computed.round_constants[round_batch_index], state)
}

// Alternative partial round version, without any skips.
fn partial_round_cpu_raw<F: PoseidonField>(round: usize, state: &mut [F]) {
    state[WIDTH - 1] *= state[WIDTH - 1].square().square();
    let mut new_state = F::ROUND_CONSTANTS[round + 1];
    linear_layer(state, &mut new_state)
}

/// A cpu version of the full Poseidon's permutation with partial-round skips.
pub fn permutation_cpu<F: PoseidonField>(pre_computed: &PreComputedRoundCPU<F>, state: &mut [F]) {
    let nb_skips = pre_computed.partial_round_id.nb_skips;
    let nb_main_partial_rounds = NB_PARTIAL_ROUNDS / (1 + nb_skips);
    let remainder_partial_rounds = NB_PARTIAL_ROUNDS % (1 + nb_skips);

    for (x, k0) in state.iter_mut().zip(F::ROUND_CONSTANTS[0]) {
        *x += k0;
    }
    (0..NB_FULL_ROUNDS / 2).for_each(|round_index| full_round_cpu(round_index, state));
    (0..nb_main_partial_rounds)
        .for_each(|round_batch_index| partial_round_cpu(pre_computed, round_batch_index, state));
    (NB_FULL_ROUNDS / 2 + NB_PARTIAL_ROUNDS - remainder_partial_rounds..)
        .take(remainder_partial_rounds)
        .for_each(|round_index| partial_round_cpu_raw(round_index, state));
    (NB_FULL_ROUNDS / 2 + NB_PARTIAL_ROUNDS..)
        .take(NB_FULL_ROUNDS / 2)
        .for_each(|round_index| {
            full_round_cpu(round_index, state);
        })
}

// A cpu implementation of the sponge operations, building on the Poseidon's
// permutation.
impl<F: PoseidonField> SpongeCPU<F, F> for PoseidonChip<F> {
    type StateCPU = PoseidonState<F>;

    fn init(input_len: Option<usize>) -> Self::StateCPU {
        let mut register = [F::ZERO; WIDTH];
        register[RATE] = F::from_u128(input_len.map(|l| l as u128).unwrap_or(1 << 64));
        let pre_computed = PreComputedRoundCPU::init();
        PoseidonState {
            pre_computed,
            register,
            queue: Vec::new(),
            squeeze_position: 0,
            input_len,
        }
    }

    fn absorb(state: &mut Self::StateCPU, inputs: &[F]) {
        state.queue.extend(inputs);
        state.squeeze_position = 0;
    }

    fn squeeze(state: &mut Self::StateCPU) -> F {
        if state.squeeze_position > 0 {
            // If `input_len` was specified, we only allow 1 squeeze.
            if state.input_len.is_some() {
                panic!("Attempting to squeeze multiple times a fixed-size Poseidon sponge (CPU).")
            };
            debug_assert!(state.queue.is_empty());
            let output = state.register[state.squeeze_position % RATE];
            state.squeeze_position = (state.squeeze_position + 1) % RATE;
            return output;
        }

        match state.input_len {
            None => {
                let padding = F::from(state.queue.len() as u64);
                state.queue.push(padding);
            }
            Some(len) => {
                if state.queue.len() != len {
                    panic!("Inconsistent lengths in fixed-size Poseidon sponge (CPU). Expected: {}, found: {}.", len, state.queue.len())
                };
            }
        }

        for chunk in state.queue.chunks(RATE) {
            for (entry, value) in state.register.iter_mut().zip(chunk.iter()) {
                *entry += value;
            }
            permutation_cpu(&state.pre_computed, &mut state.register);
        }

        state.queue = Vec::new();
        state.squeeze_position = 1 % RATE;
        state.register[0]
    }
}

impl<F: PoseidonField> TranscriptHash for PoseidonState<F> {
    type Input = Vec<F>;
    type Output = F;

    fn init() -> Self {
        PoseidonChip::init(None)
    }

    fn absorb(&mut self, input: &Self::Input) {
        PoseidonChip::absorb(self, input)
    }

    fn squeeze(&mut self) -> Self::Output {
        PoseidonChip::squeeze(self)
    }
}

/////////////////////////////////////////////////////////////
/// Implementation of Hashable for BLS12-381 with Poseidon //
/////////////////////////////////////////////////////////////

impl Hashable<PoseidonState<blstrs::Fq>> for blstrs::G1Projective {
    fn to_input(&self) -> Vec<blstrs::Fq> {
        AssignedForeignPoint::<blstrs::Fq, blstrs::G1Projective, MEP>::as_public_input(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <blstrs::G1Affine as GroupEncoding>::to_bytes(&self.into())
            .as_ref()
            .to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <blstrs::G1Affine as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(blstrs::G1Affine::from_bytes(&bytes))
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    "Invalid BLS12-381 point encoding in proof",
                )
            })
            .map(|p: blstrs::G1Affine| p.into())
    }
}

impl Hashable<PoseidonState<blstrs::Fq>> for blstrs::Fq {
    fn to_input(&self) -> Vec<blstrs::Fq> {
        vec![*self]
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "Invalid BLS12-381 scalar encoding in proof",
            )
        })
    }
}

impl Sampleable<PoseidonState<blstrs::Fq>> for blstrs::Fq {
    fn sample(out: blstrs::Fq) -> Self {
        out
    }
}

impl<F: PoseidonField> HashCPU<F, F> for PoseidonChip<F> {
    fn hash(inputs: &[F]) -> F {
        let mut state = <Self as SpongeCPU<F, F>>::init(Some(inputs.len()));
        <Self as SpongeCPU<F, F>>::absorb(&mut state, inputs);
        <Self as SpongeCPU<F, F>>::squeeze(&mut state)
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha12Rng;

    use super::*;
    use crate::hash::poseidon::permutation_cpu;

    // A version of Poseidon's permutation, without round skips. Has been tested
    // against the previous version of Poseidon (replaced since Merge request #521).
    fn permutation_cpu_raw<F: PoseidonField>(state: &mut [F]) {
        for (x, k0) in state.iter_mut().zip(F::ROUND_CONSTANTS[0]) {
            *x += k0;
        }
        for round_index in 0..NB_FULL_ROUNDS / 2 {
            full_round_cpu(round_index, state);
        }
        for round_index in (NB_FULL_ROUNDS / 2..).take(NB_PARTIAL_ROUNDS) {
            partial_round_cpu_raw(round_index, state);
        }
        for round_index in (NB_FULL_ROUNDS / 2 + NB_PARTIAL_ROUNDS..).take(NB_FULL_ROUNDS / 2) {
            full_round_cpu(round_index, state);
        }
    }
    // Tests the performances of the cpu version of Poseidon. In debug mode, also
    // tests the consistency between the version with and without round skips.
    fn consistency_cpu<F: PoseidonField + ff::FromUniformBytes<64>>(nb_samples: usize) {
        println!(
            ">> Testing the consistency between the two cpu implementations of the permutation ({NB_SKIPS_CPU} round skips VS no round skips)."
        );

        let pre_computed = PreComputedRoundCPU::init();
        let mut rng = ChaCha12Rng::seed_from_u64(0xf007ba11);
        (0..nb_samples)
            .for_each(|_| {
                let input: [F; WIDTH] =
                    core::array::from_fn(|_| F::random(&mut rng));
                let mut res1 = input;
                let mut res2 = input;
                permutation_cpu_raw(&mut res1);
                permutation_cpu(&pre_computed, &mut res2);
                if res1 != res2 {
                    panic!("=> Inconsistencies between the cpu implementations of the permutations.\n\nOn input x = {:?},\n\npermutation_cpu_no_skip(x) = {:?}\n\npermutation_cpu_with_skips(x) = {:?}\n", input, res1, res2)
                }
            });
        println!("=> No internal inconsistency found.")
    }

    #[test]
    fn cpu_test() {
        // Testing cpu performances. In debug mode, also tests the consistency between
        // the optimised and non-optimised cpu implementations of the permutation.
        consistency_cpu::<blstrs::Fq>(1);
    }
}
