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

use std::iter::repeat;

use ff::Field;
use midnight_proofs::plonk::Expression;

use super::{sbox, PoseidonField, NB_SKIPS_CPU};
use crate::hash::poseidon::{
    constants::{NB_FULL_ROUNDS, NB_PARTIAL_ROUNDS, WIDTH},
    NB_SKIPS_CIRCUIT,
};

/// Maximal number of partial-round skips performed during Poseidon.
pub(crate) const NB_SKIPS_MAX: usize = if NB_SKIPS_CIRCUIT < NB_SKIPS_CPU {
    NB_SKIPS_CPU
} else {
    NB_SKIPS_CIRCUIT
};

// Pre-generated partial-round constants for CPU implementations.
type RoundContantsCPU<F> = [[F; WIDTH + NB_SKIPS_CPU]; NB_PARTIAL_ROUNDS / (1 + NB_SKIPS_CPU)];
// Pre-generated partial-round constants for circuit implementations.
type RoundContantsCircuit<F> =
    [[F; WIDTH + NB_SKIPS_CIRCUIT]; NB_PARTIAL_ROUNDS / (1 + NB_SKIPS_CIRCUIT)];

/// Represents a combination
/// `a1 x1 + ... + an xn + b1 y1^5 + ... + bp yp^5 + c1 z1 + ... + cq zq`
/// where the `ai` and `bi` are the field elements stored `var_coeffs`, and the
/// `ci` those in `const_coeffs`. Each index implictly corresponds to a variable
/// `xi` or `yi`, or a round constant `zi`. The slices `var_coeffs[..WIDTH-1]`
/// and `constants` correspond to linear variables/constants `xi`, while
/// `var_coeffs[WIDTH-1..]` is for the variables `yi` that are exponentiated.
///
/// Note: the size of the array are overapproximated by using `NB_SKIPS_MAX` to
/// avoid having to deal with different types for `NB_SKIPS_CPU` and
/// `NB_SKIPS_CIRCUIT`. This will be the case for all similar types that are
/// only used in precomputations.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RoundVarId<F> {
    var_coeffs: [F; WIDTH + NB_SKIPS_MAX], // Length WIDTH + number of round skips.
    const_coeffs: [F; WIDTH * (1 + NB_SKIPS_MAX)], // Length 1 + number of round skips.
}

/// A set of linear combinations representing a set of polynomial identities
/// characterising partial rounds. Identities in `ids[..WIDTH-1]` are for the
/// cells that do not go through an exponentiation, unlike those in
/// `ids[WIDTH-1..]`.
///
/// Note: Unlike the field `var_coeffs` which has `WIDTH + nb_skips` elements,
/// `ids` contains `WIDTH + nb_skips + 1` identities. The additional element (at
/// index 0) represents the last input of the round (which is a trivial
/// identity, simply here for the convenience of the computation).
#[derive(Clone, Copy, Debug)]
pub(crate) struct RoundId<F> {
    pub nb_skips: usize,
    ids: [RoundVarId<F>; WIDTH + 1 + NB_SKIPS_MAX], // Real length `WIDTH + 1 + self.nb_skips`.
}

/// Precomputed data for cpu partial rounds (round constants and round
/// identities). The `round_constants` field has dimension `[[F; WIDTH +
/// self.partial_round_id.nb_skips]; NB_FULL_ROUNDS + NB_PARTIAL_ROUNDS / (1 +
/// self.partial_round_id.nb_skips)]`.
#[derive(Clone, Copy, Debug)]
pub struct PreComputedRoundCPU<F: PoseidonField> {
    pub(crate) round_constants: RoundContantsCPU<F>,
    pub(crate) partial_round_id: RoundId<F>,
}

/// Analogue of `PrecomputedRoundCPU` for circuit implementations.
#[derive(Clone, Copy, Debug)]
pub struct PreComputedRoundCircuit<F: PoseidonField> {
    pub(crate) round_constants: RoundContantsCircuit<F>,
    pub(crate) partial_round_id: RoundId<F>,
}

impl<F: Field> RoundVarId<F> {
    // `id1.add_and_mul(id2,c)` adds `c * id2` to `id1`.
    fn add_and_mul(&mut self, rhs: &Self, c: &F) {
        self.var_coeffs
            .iter_mut()
            .chain(self.const_coeffs.iter_mut())
            .zip(rhs.var_coeffs.iter().chain(rhs.const_coeffs.iter()))
            .for_each(|(a, b)| *a += *b * *c)
    }

    // Generates a null linear combination.
    fn init() -> Self {
        RoundVarId {
            var_coeffs: [F::ZERO; WIDTH + NB_SKIPS_MAX],
            const_coeffs: [F::ZERO; WIDTH * (1 + NB_SKIPS_MAX)],
        }
    }

    // Generates a linear combination equal to a given constant, modelled by its
    // indexes in the field `constants`.
    fn from_constant_index(round_offset: &usize, column: &usize) -> Self {
        let mut id = Self::init();
        id.const_coeffs[*round_offset * WIDTH + *column] = F::ONE;
        id
    }

    // Takes a valuation for each variable of the `constants` field, and returns the
    // evaluation of the linear combination when evaluating all other variables as
    // zero. The argument `instances` has length `1 + self.nb_skips`.
    fn eval_constants(&self, instances: &[[F; WIDTH]]) -> F {
        self.const_coeffs
            .iter()
            .zip(instances.iter().flatten())
            .fold(F::ZERO, |accu, (x1, x2)| accu + *x1 * x2)
    }

    // Takes a valuation for each variable of `self.var_coeffs` and returns the
    // evaluation of the linear combination when evaluating all variables of
    // `self.constants` as zero. This function assumes that all non-linear
    // variables have already been exponentiated.
    fn eval_vars(
        &self,
        instances: &[F], // Has length `WIDTH + self.nb_skips`.
        constant: F,
    ) -> F {
        self.var_coeffs
            .iter()
            .zip(instances.iter())
            .fold(constant, |accu, (v1, v2)| accu + *v1 * v2)
    }

    // Converts a set of identities into a Halo2 `Expression`, upon taking as an
    // argument the representation of the input variables as `Expression`. The
    // argument `vars` has length `WIDTH + self.nb_skips`.
    // Note: does *not* include the `self.constant` component in the conversion.
    fn to_expression(self, vars: &[Expression<F>]) -> Expression<F> {
        let (lin_coeffs, pow_coeffs) = self.var_coeffs.split_at(WIDTH - 1);
        let (lin_vars, pow_vars) = vars.split_at(WIDTH - 1);

        let expr = lin_coeffs.iter().zip(lin_vars).fold(
            Expression::Constant(F::ZERO),
            |accu, (coeff, x)| {
                if coeff.is_zero_vartime() {
                    accu
                } else {
                    accu + Expression::Constant(*coeff) * x.clone()
                }
            },
        );
        pow_coeffs
            .iter()
            .zip(pow_vars)
            .fold(expr, |accu, (coeff, x)| {
                if coeff.is_zero_vartime() {
                    accu
                } else {
                    accu + Expression::Constant(*coeff) * sbox(x.clone())
                }
            })
    }
}

impl<F: PoseidonField> RoundId<F> {
    // Generates a new trivial identity. The linear variables are initialised to
    // themselves ("x = x"), and the exponentiated variables are initialised to 0
    // ("x = 0"). The latter will be overwritten during the identity generation
    // anyway, so their initialisation does not matter.
    fn init(nb_skips: usize) -> Self {
        RoundId {
            nb_skips,
            ids: core::array::from_fn(|i| {
                if i < WIDTH {
                    let mut id = RoundVarId::init();
                    id.var_coeffs[i] = F::ONE;
                    id
                } else {
                    RoundVarId::init()
                }
            }),
        }
    }

    // Reconstructs the identity of the current row, assuming that the identities of
    // its linear variables are stored in `self.ids[..WIDTH-1]`. This function
    // basically copies `self.ids[..WIDTH-1]` in the first `WIDTH-1` elements of the
    // result, and adds a trivial identity ("x = x") in the last exponentiated slot.
    fn row_id(&self, row: &usize) -> [RoundVarId<F>; WIDTH] {
        let mut last = RoundVarId::init();
        last.var_coeffs[WIDTH - 1 + *row] = F::ONE;
        core::array::from_fn(|i| if i == WIDTH - 1 { last } else { self.ids[i] })
    }

    // Updates the identity from the current row to the next one by applying a
    // partial round.
    fn update_row(self: &mut RoundId<F>, round_offset: &usize) {
        let current_row = self.row_id(round_offset);
        #[allow(clippy::needless_range_loop)]
        for i in 0..WIDTH - 1 {
            self.ids[i] = RoundVarId::from_constant_index(round_offset, &i);
            for j in 0..WIDTH {
                self.ids[i].add_and_mul(&current_row[j], &F::MDS[i][j]);
            }
        }
        self.ids[WIDTH + *round_offset] =
            RoundVarId::from_constant_index(round_offset, &(WIDTH - 1));
        #[allow(clippy::needless_range_loop)]
        for j in 0..WIDTH {
            self.ids[WIDTH + *round_offset].add_and_mul(&current_row[j], &F::MDS[WIDTH - 1][j]);
        }
    }

    /// Generates the final identities for an optimised partial rounds, i.e.,
    /// applies `1+nb_skips` times the function `ids.update_row`.
    fn generate(nb_skips: usize) -> Self {
        let mut ids = RoundId::<F>::init(nb_skips);
        for row in 0..1 + nb_skips {
            ids.update_row(&row);
        }
        ids
    }

    // Uplifting of the function `RoundVarId<F>::eval_constants` to sets of
    // identities. The `instances` argument has length `1 + self.nb_skips`, and the
    // result has length `WIDTH + self.nb_skips`. Mutates the `arg` argument to
    // store the result.
    fn eval_constants(&self, round: usize, arg: &mut [F]) {
        let instances = &F::ROUND_CONSTANTS[round + 1..round + 2 + self.nb_skips];
        self.ids[..WIDTH - 1]
            .iter()
            .chain(self.ids[WIDTH..].iter())
            .map(|id| id.eval_constants(instances))
            .zip(arg.iter_mut())
            .for_each(|(c, x)| *x = c)
    }

    /// Uplifting of the function `RoundVarId<F>::eval_vars` to sets of
    /// identities, and adds the output of `self.eval_constants` to the result
    /// (taken as the `round_constants` argument). Returns the value of
    /// the last column of the skipped rows (length `self.nb_skips`, passed as
    /// the parameter `NB_SKIPS` so that it can be used as array's length).
    pub(crate) fn eval<const NB_SKIPS: usize>(
        &self,
        round_constants: &[F], // Length `WIDTH + self.nb_skips`.
        instances: &mut [F],   // Length `WIDTH`.
    ) -> [F; NB_SKIPS] {
        let mut pow_instances = [F::ZERO; NB_SKIPS];
        instances[WIDTH - 1] *= instances[WIDTH - 1].square().square();
        let mut pow_instances_exp = instances
            .iter()
            .chain(repeat(&F::ZERO).take(NB_SKIPS))
            .copied()
            .collect::<Vec<_>>();

        #[allow(clippy::reversed_empty_ranges)]
        for i in 0..self.nb_skips {
            let next =
                self.ids[WIDTH + i].eval_vars(&pow_instances_exp, round_constants[WIDTH - 1 + i]);
            pow_instances[i] = next;
            pow_instances_exp[WIDTH + i] = next.square().square() * next;
        }
        let mut output = [F::ZERO; WIDTH];
        for i in 0..WIDTH - 1 {
            output[i] = self.ids[i].eval_vars(&pow_instances_exp, round_constants[i]);
        }
        output[WIDTH - 1] = self.ids[WIDTH + NB_SKIPS]
            .eval_vars(&pow_instances_exp, round_constants[WIDTH + NB_SKIPS - 1]);
        instances.copy_from_slice(&output);
        pow_instances
    }

    // Computes the round constants necessary for partial-round (cpu) with
    // round skips.
    fn round_constants_cpu(&self) -> RoundContantsCPU<F> {
        let mut v = [[F::ZERO; WIDTH + NB_SKIPS_CPU]; NB_PARTIAL_ROUNDS / (1 + NB_SKIPS_CPU)];
        for (round, main_round) in (NB_FULL_ROUNDS / 2..)
            .take(NB_PARTIAL_ROUNDS - NB_PARTIAL_ROUNDS % (1 + NB_SKIPS_CPU))
            .step_by(1 + NB_SKIPS_CPU)
            .zip(0..)
        {
            self.eval_constants(round, &mut v[main_round])
        }
        v
    }

    // Computes the round constants necessary for partial-round (circuit) with
    // round skips.
    fn round_constants_circuit(&self) -> RoundContantsCircuit<F> {
        // Practical restriction: skipping partial rounds should always be done in a way
        // that avoids having to add trailing rounds, at least in circuit.
        assert_eq!(
            NB_PARTIAL_ROUNDS % (1 + NB_SKIPS_CIRCUIT),
            0,
            "The Poseidon chip assumes that the number of partial round (NB_PARTIAL_ROUNDS = {}) is dividable by the number of round skips (1 + NB_SKIPS = {}).",
            NB_PARTIAL_ROUNDS,
            1 + NB_SKIPS_CIRCUIT
        );
        // Also assumes that the number of full rounds is even.
        assert_eq!(
            NB_FULL_ROUNDS % 2,
            0,
            "The Poseidon chip assumes the number of full round (NB_FULL_ROUNDS = {}) is even.",
            NB_FULL_ROUNDS
        );

        let mut v =
            [[F::ZERO; WIDTH + NB_SKIPS_CIRCUIT]; NB_PARTIAL_ROUNDS / (1 + NB_SKIPS_CIRCUIT)];
        for (round, main_round) in (NB_FULL_ROUNDS / 2..)
            .take(NB_PARTIAL_ROUNDS - NB_PARTIAL_ROUNDS % (1 + NB_SKIPS_CIRCUIT))
            .step_by(1 + NB_SKIPS_CIRCUIT)
            .zip(0..)
        {
            self.eval_constants(round, &mut v[main_round])
        }
        v
    }

    // Uplifting of the function `RoundVarId<F>::to_expression` to sets of
    // identities. The `vars` argument has length `WIDTH + self.nb_skips`. In the
    // resulting array:
    // - the first `WIDTH-1` expressions represent the linear variables of the
    //   output (i.e., the whole output except the last column)
    // - the next `self.nb_skips` expressions represent the exponentiated auxiliary
    //   variables that are introduced due to round skips
    // - the last expression is for the last missing output.
    // Note: does *not* include the constant component in the conversion.
    pub(crate) fn to_expression(self, vars: &[Expression<F>]) -> Vec<Expression<F>> {
        self.ids[..WIDTH - 1]
            .iter()
            .chain(self.ids[WIDTH..].iter())
            .map(|id| (*id).to_expression(vars))
            .collect::<Vec<_>>()
    }
}

impl<F: PoseidonField> PreComputedRoundCPU<F> {
    /// Pre-computes partial rounds and the associated round contants for
    /// Poseidon's using NB_SKIPS_CPU round skips.
    pub fn init() -> Self {
        let partial_round_id = RoundId::<F>::generate(NB_SKIPS_CPU);
        let round_constants = partial_round_id.round_constants_cpu();
        PreComputedRoundCPU {
            partial_round_id,
            round_constants,
        }
    }
}

impl<F: PoseidonField> PreComputedRoundCircuit<F> {
    pub(crate) fn init() -> Self {
        let partial_round_id = RoundId::<F>::generate(NB_SKIPS_CIRCUIT);
        let round_constants = partial_round_id.round_constants_circuit();
        PreComputedRoundCircuit {
            partial_round_id,
            round_constants,
        }
    }
}
