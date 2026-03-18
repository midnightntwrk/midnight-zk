// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

//! Implementation in-circuit of the Poseidon sponge functions, with the
//! partial-round skip optimisation.

// The idea of round skips is that unlike full rounds, Poseidon's partial
// rounds are "almost linear", in that only one column of the input is altered
// (here, exponentiated) by the S-box. In particular, when performing several
// partial rounds in a row, the final output can be expressed as a linear
// combination of the initial input of the round, and of the exponentiated
// columns. Rephrasing, upon performing `NB_SKIPS` skips (i.e., `1 + NB_SKIPS`
// partial rounds in a row), over an input of length `WIDTH`, we can perform
// this batch of rounds in one Plonk row (instead of `1 + NB_SKIPS` rows), using
// `WIDTH + NB_SKIPS` advice cells instead of `WIDTH * NB_SKIPS` cells.
// Formalisation and full details about this optimisation can be found at:
//
// Miguel Ambrona, Anne-Laure Schmitt, Raphael R. Toledo, and Danny Willems,
// New optimization techniques for PlonK’s arithmetization
// https://eprint.iacr.org/2022/462.pdf
//
// With a more graphical explanation, consider the case `WIDTH == 3` and
// `NB_SKIPS == 2`. The cells of a Plonk matrix will look like this:
//
// | x0 | y0 | z0 || a0 | b0 | c0 | --> initial input
// | x1 | y1 | z1 || a1 | b1 | c1 | --> `NB_SKIPS` rounds to be skipped
// | x2 | y2 | z2 || a2 | b2 | c2 |
// | x3 | y3 | z3 ||    |    |    | --> final output
//
// Here, `ai`, `bi` and `ci` are the round constants of Poseidon, stored in the
// files of the `constants` folder. Each time, row `i+1` is obtained by
// computing
//
// `(x{i+1} y{i+1} z{i+1}) = (xi yi zi^5) * MDS + (ai bi ci)`
//   with `MDS` a suitable 3x3 MDS-matrix
//
// Note that these are "shifted rounds" (the standard description adds the round
// constants before the exponentiation). We use shifted rounds to simplify the
// above polynomial identity, which defines the same Poseidon's permutation
// provided (1) we manually add the first-round constants `(a0 b0 c0)` to the
// very first input `(x0 y0 z0)` of a permutation, and (2) we use a shifted
// round-constant table that is offset by 1 (i.e., `(ai' bi' ci') = (a{i+1}
// b{i+1} c{i+1})` with the convention `(aN' bN' cN') = (0 0 0)` for `N` the
// last round index).
//
// This module implements polynomial identities that express `x3`, `y3`, `z1`,
// `z2`, `z3` as a linear combination of `x0`, `y0`, `z0^5`, `z1^5`,
// `z2^5`. These linear combinations (e.g., `z2 = (x1 y1 z1^5) * MDS + (a1 b1
// c1)`) are formalised by the `RoundVarId<F>` type,
// where `F : PoseidonField` is the Scalar type. All individual identities for a
// round are then batched together as `RoundId<F>`. Note
// in particular the important methods:
//   - `RoundId<F>::generate` which generates these identities for a desired
//     number of skips.
//   - `RoundId<F>::round_constants_opt` which pre-computes the constant
//     components of an identity. Indeed, all identities are of the form: `(x3
//     y3 z1 z2 z3) = L(x0 y0 z0^5 z1^5 z2^5) + P({ai,bi,ci}_i))` with `L` a
//     linear function and `P` a polynomial. Therefore, instead of loading all
//     `WIDTH * (1 + NB_SKIPS)` round constants `{ai,bi,ci}` in the circuit,
//     only the `WIDTH + NB_SKIPS` components of `C = P({ai,bi,ci}_i))` need to
//     be loaded. `RoundId<F>::round_constants_opt` computes `C` for each
//     (non-skipped) partial round of Poseidon.
//   - `RoundId<F>::to_expression` converts a set of round identities into Plonk
//     expressions suitable for custom gates. This conversion ignores the round
//     constants, as they will be pre-computed separately by
//     `round_constants_opt` anyway as explained above.
//   - `RoundId<F>::eval` which computes the concrete value of `(x3 y3 z3)` for
//     a given value of `(x0 y0 z0)`, using the identity. This function is used
//     to derive a CPU (i.e., off-circuit) version of Poseidon implementing
//     round skips as well.
//
// Note that `NB_SKIPS` can have two different values, depending on whether we
// are implementing a CPU version of poseidon (`NB_SKIPS_CPU`) or a
// circuit chip (`NB_SKIPS_CIRCUIT`). The reason for separating
// the two values is that CPU and circuit implementations have different
// resource requirements, and therefore different optimal number of skips.

/// Constants used to implement the [PoseidonChip]. Its main trait is
/// [PoseidonField], which is a subtrait of [ff::PrimeField] implementing
/// constants for the MDS matrix and round constants. The module also contains
/// (non-public) implementations of [PoseidonField] for
/// [midnight_curves::Fq].
pub mod constants;

mod poseidon_chip;

/// Implementation of CPU versions of Poseidon's permutation and round function.
/// The functions use two different numbers of round skips depending on whether
/// they will be used for circuits (NB_SKIPS_CIRCUIT) or CPU (NB_SKIPS_CPU).
mod poseidon_cpu;

mod poseidon_varlen;
/// Basic structures and methods for performing partial-round skips in Poseidon.
pub mod round_skips;

use constants::{PoseidonField, WIDTH};
use midnight_proofs::{circuit::Layouter, plonk::Error};
pub use poseidon_chip::*;
pub use poseidon_cpu::*;
pub use poseidon_varlen::VarLenPoseidonGadget;

use crate::{
    instructions::{
        hash::{HashCPU, HashInstructions, VarHashInstructions},
        SpongeCPU, SpongeInstructions,
    },
    types::AssignedNative,
    vec::AssignedVector,
};

/// Number of advice columns used by the Poseidon chip.
pub const NB_POSEIDON_ADVICE_COLS: usize = if NB_SKIPS_CIRCUIT >= WIDTH {
    WIDTH + NB_SKIPS_CIRCUIT
} else {
    2 * WIDTH
};

/// Number of fixed columns used by the Poseidon chip.
pub const NB_POSEIDON_FIXED_COLS: usize = WIDTH + NB_SKIPS_CIRCUIT;

impl<F: PoseidonField> HashCPU<F, F> for PoseidonChip<F> {
    fn hash(inputs: &[F]) -> F {
        let mut state = <Self as SpongeCPU<F, F>>::init(Some(inputs.len()));
        <Self as SpongeCPU<F, F>>::absorb(&mut state, inputs);
        <Self as SpongeCPU<F, F>>::squeeze(&mut state)
    }
}

impl<F: PoseidonField> HashInstructions<F, AssignedNative<F>, AssignedNative<F>>
    for PoseidonChip<F>
{
    fn hash(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedNative<F>],
    ) -> Result<AssignedNative<F>, Error> {
        let mut state = self.init(layouter, Some(inputs.len()))?;
        self.absorb(layouter, &mut state, inputs)?;
        self.squeeze(layouter, &mut state)
    }
}

// Inherit HashCPU trait from PoseidonChip.
impl<F: PoseidonField> HashCPU<F, F> for VarLenPoseidonGadget<F> {
    fn hash(inputs: &[F]) -> F {
        <PoseidonChip<F> as HashCPU<F, F>>::hash(inputs)
    }
}

use super::poseidon::constants::RATE;
impl<F: PoseidonField, const MAX_LEN: usize>
    VarHashInstructions<F, MAX_LEN, AssignedNative<F>, AssignedNative<F>, RATE>
    for VarLenPoseidonGadget<F>
{
    /// Hashes the variable-length vector inputs.
    ///
    /// # Panics
    ///
    /// If `MAX_LEN` is not a multiple of `RATE`.
    fn varhash(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, AssignedNative<F>, MAX_LEN, RATE>,
    ) -> Result<AssignedNative<F>, Error> {
        self.poseidon_varlen(layouter, input)
    }
}

#[cfg(test)]
mod tests {
    use super::{constants::RATE, PoseidonChip};
    use crate::{
        field::{AssignedNative, NativeChip},
        hash::poseidon::VarLenPoseidonGadget,
        instructions::hash::tests::{test_hash, test_varhash},
    };

    type F = midnight_curves::Fq;
    #[test]
    fn test_poseidon_hash() {
        fn test_wrapper(input_size: usize, k: u32, cost_model: bool) {
            test_hash::<F, AssignedNative<F>, AssignedNative<F>, PoseidonChip<F>, NativeChip<F>>(
                cost_model, "Poseidon", input_size, k,
            )
        }

        // Cost model update with input size = 64 field elements
        test_wrapper(32 * RATE, 10, true);

        test_wrapper(RATE, 5, false);
        test_wrapper(RATE - 1, 5, false);
        test_wrapper(RATE - 2, 5, false);
        test_wrapper(2 * RATE, 7, false);
        test_wrapper(2 * RATE - 1, 7, false);
        test_wrapper(2 * RATE + 1, 7, false);
        test_wrapper(4 * RATE, 7, false);
        test_wrapper(8 * RATE, 8, false);
        test_wrapper(16 * RATE, 9, false);
    }

    #[test]
    fn test_poseidon_varhash() {
        fn test_wrapper<const M: usize>(input_size: usize, k: u32, cost_model: bool) {
            test_varhash::<F, AssignedNative<F>, AssignedNative<F>, VarLenPoseidonGadget<F>, M, RATE>(
                cost_model,
                "VarPoseidon",
                input_size,
                k,
            )
        }
        // Cost model update with input size = 64 field elements
        test_wrapper::<64>(32, 14, true);

        test_wrapper::<512>(64, 14, false);
        test_wrapper::<512>(63, 14, false);

        test_wrapper::<256>(128, 12, false);
        test_wrapper::<256>(127, 12, false);
        test_wrapper::<256>(256, 12, false);

        test_wrapper::<128>(0, 11, false);
        test_wrapper::<128>(1, 11, false);
        test_wrapper::<128>(2, 11, false);
    }
}
