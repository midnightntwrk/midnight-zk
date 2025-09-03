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
/// [midnight_curves::Fq], [halo2curves::pasta::pallas::Base] and
/// [halo2curves::pasta::vesta::Base].
pub mod constants;

mod poseidon_chip;

/// Implementation of CPU versions of Poseidon's permutation and round function.
/// The functions use two different numbers of round skips depending on whether
/// they will be used for circuits (NB_SKIPS_CIRCUIT) or CPU (NB_SKIPS_CPU).
pub mod poseidon_cpu;

mod poseidon_varlen;
/// Basic structures and methods for performing partial-round skips in Poseidon.
pub mod round_skips;

use constants::{PoseidonField, WIDTH};
pub use poseidon_chip::*;
pub use poseidon_cpu::*;
pub use poseidon_varlen::VarLenPoseidonGadget;

/// Number of advice columns used by the Poseidon chip.
pub const NB_POSEIDON_ADVICE_COLS: usize = if NB_SKIPS_CIRCUIT >= WIDTH {
    WIDTH + NB_SKIPS_CIRCUIT
} else {
    2 * WIDTH
};

/// Number of fixed columns used by the Poseidon chip.
pub const NB_POSEIDON_FIXED_COLS: usize = WIDTH + NB_SKIPS_CIRCUIT;
