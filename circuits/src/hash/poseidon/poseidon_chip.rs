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

use std::iter::once;

use ff::{Field, PrimeField};
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
#[cfg(any(test, feature = "testing"))]
use {crate::testing_utils::FromScratch, midnight_proofs::plonk::Instance};

use super::{
    constants::{PoseidonField, NB_FULL_ROUNDS, NB_PARTIAL_ROUNDS, RATE, WIDTH},
    full_round_cpu, partial_round_cpu_for_circuits,
    round_skips::PreComputedRoundCircuit,
    NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS,
};
#[cfg(any(test, feature = "testing"))]
use crate::field::{
    native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
    NativeConfig,
};
use crate::{
    field::NativeChip,
    instructions::{
        ArithInstructions, AssignmentInstructions, HashInstructions, SpongeInstructions,
    },
    types::AssignedNative,
    utils::ComposableChip,
};

/// Number of times the linear part of the partial rounds is skipped in the
/// Poseidon chip (0 is the default implementation without skips at all).
///
/// Note: The chip configuration will panic if `NB_PARTIAL_ROUNDS` is not
/// dividable by `1 + NB_SKIPS_CIRCUIT`.
pub(crate) const NB_SKIPS_CIRCUIT: usize = 5;

// A recurring type representing a set of assigned registers, representing the
// internal state of Poseidon's computation. Does not account for the additional
// registers needed in skipped rounds.
pub(super) type AssignedRegister<F> = [AssignedNative<F>; WIDTH];

/// In-circuit Poseidon state.
#[derive(Clone, Debug)]
pub struct AssignedPoseidonState<F: PrimeField> {
    pub(super) register: AssignedRegister<F>,
    pub(super) queue: Vec<AssignedNative<F>>,
    pub(super) squeeze_position: usize,
    input_len: Option<usize>,
}

#[derive(Clone, Debug)]
/// Poseidon configuration setting.
pub struct PoseidonConfig<F: PoseidonField> {
    /// Selector for full rounds.
    q_full_round: Selector,

    /// Selector for optimized partial rounds skipping `1+NB_SKIPS_CIRCUIT`
    /// rounds.
    q_partial_round: Selector,

    /// Advice columns, including those potentially needed for optimised
    /// skipping rounds. The Poseidon circuit (`PoseidonChip::permutation`)
    /// assumes that the first `WIDTH` columns of `register_cols` are the (first
    /// `WIDTH`) columns where `native_chip::add_constants_in_region` assigns
    /// its result. An assertion is checking this assumption in
    /// `PoseidonChip::permutation` in debug mode.
    register_cols: [Column<Advice>; NB_POSEIDON_ADVICE_COLS],

    /// Fixed columns, one for each register column (their content will be
    /// loaded from the precomputed array stored at the field
    /// `round_constant_opt`).
    constant_cols: [Column<Fixed>; NB_POSEIDON_FIXED_COLS],

    /// Precomputed data for partial rounds (identities and round constants).
    pre_computed: PreComputedRoundCircuit<F>,
}

/// Chip for Poseidon operations.
#[derive(Clone, Debug)]
pub struct PoseidonChip<F: PoseidonField> {
    config: PoseidonConfig<F>,
    native_chip: NativeChip<F>,
}

impl<F: PoseidonField> Chip<F> for PoseidonChip<F> {
    type Config = PoseidonConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PoseidonField> PoseidonChip<F> {
    /// Size of Poseidon's register.
    pub const fn register_size() -> usize {
        WIDTH
    }

    /// Hash rate provided by this implementation of Poseidon.
    pub const fn rate() -> usize {
        RATE
    }

    /// Number of full rounds of the Poseidon permutation.
    pub const fn nb_full_rounds() -> usize {
        NB_FULL_ROUNDS
    }

    /// Number of partial rounds of the Poseidon permutation.
    pub const fn nb_partial_rounds() -> usize {
        NB_PARTIAL_ROUNDS
    }
}

// Computes the identity of the linear layer of Poseidon's rounds
// (multiplication by the MDS matrix and addition of round constants). To save
// up the cost of addition, the identity is computed by mutating a variable
// initialised as the round-constant argument.
fn linear_layer<F: PoseidonField>(
    inputs: [Expression<F>; WIDTH],
    outputs: [Expression<F>; WIDTH],
    constants: [Expression<F>; WIDTH],
) -> [Expression<F>; WIDTH] {
    let mut ids = constants;
    for i in 0..WIDTH {
        ids[i] = ids[i].clone() - outputs[i].clone();
        #[allow(clippy::needless_range_loop)]
        for j in 0..WIDTH {
            ids[i] = ids[i].clone() + Expression::Constant(F::MDS[i][j]) * inputs[j].clone();
        }
    }
    ids
}

// Performs an S-box computation.
pub(crate) fn sbox<F: Field>(x: Expression<F>) -> Expression<F> {
    x.clone() * x.square().square()
}

impl<F: PoseidonField> ComposableChip<F> for PoseidonChip<F> {
    type SharedResources = (
        [Column<Advice>; NB_POSEIDON_ADVICE_COLS],
        [Column<Fixed>; NB_POSEIDON_FIXED_COLS],
    );

    type InstructionDeps = NativeChip<F>;

    fn new(config: &PoseidonConfig<F>, native_chip: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_chip: native_chip.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> PoseidonConfig<F> {
        let register_cols = shared_res.0;
        let constant_cols = shared_res.1;

        let q_full_round = meta.selector();
        let q_partial_round = meta.selector();

        register_cols[..WIDTH]
            .iter()
            .for_each(|col| meta.enable_equality(*col));

        // Custom full round gate. It focuses on only the first `WIDTH` advice/fixed
        // columns, and compute the corresponding identity (application of the power-5
        // S-box, multiplication by the MDS matrix, and addition of the round constants
        // assigned to the fixed columns).
        //
        // Note: These are shifted rounds, i.e., the S-box is first applied, followed
        // by the linear layer (`linear_layer`). Therefore,
        // `F::ROUND_CONSTANTS[0]` will be added the the initial state before
        // applying a permutation, and the last full round will use `[F::ZERO;
        // WIDTH]` as round constants.
        meta.create_gate("full_round_gate", |meta| {
            let inputs =
                core::array::from_fn(|i| meta.query_advice(register_cols[i], Rotation::cur()));

            let outputs =
                core::array::from_fn(|i| meta.query_advice(register_cols[i], Rotation::next()));

            let constants =
                core::array::from_fn(|i| meta.query_fixed(constant_cols[i], Rotation::cur()));

            Constraints::with_selector(
                meta.query_selector(q_full_round),
                linear_layer(inputs.map(sbox), outputs, constants),
            )
        });

        // Generation of the optimised round identities, representing a batch of
        // `1+NB_SKIPS` partial rounds.
        let pre_computed = PreComputedRoundCircuit::<F>::init();
        let ids = pre_computed.partial_round_id;

        // A batch of `1+NB_SKIPS` partial gates. Most of the work has been done in the
        // previous line, with `ids` now storing the expressions that will be used to
        // represent the core of the gates' polynomial identities.
        meta.create_gate("partial_round_gate", |meta| {
            let q = meta.query_selector(q_partial_round);

            let inputs = register_cols
                .iter()
                .map(|col| meta.query_advice(*col, Rotation::cur()))
                .collect::<Vec<_>>();
            let round_constants = constant_cols
                .iter()
                .map(|col| meta.query_fixed(*col, Rotation::cur()))
                .collect::<Vec<_>>();
            let outputs = register_cols[0..WIDTH]
                .iter()
                .map(|col| meta.query_advice(*col, Rotation::next()))
                .collect::<Vec<_>>();

            let constraints = ids.to_expression(&inputs);

            let output_lin_constraints = (0..WIDTH - 1)
                .map(|i| round_constants[i].clone() - outputs[i].clone() + constraints[i].clone());
            let input_pow_constraints = (WIDTH - 1..WIDTH + NB_SKIPS_CIRCUIT - 1).map(|i| {
                round_constants[i].clone() - inputs[i + 1].clone() + constraints[i].clone()
            });
            let output_pow_constraint: Expression<F> =
                round_constants[WIDTH + NB_SKIPS_CIRCUIT - 1].clone() - outputs[WIDTH - 1].clone()
                    + constraints[WIDTH + NB_SKIPS_CIRCUIT - 1].clone();

            let constraints = output_lin_constraints
                .chain(input_pow_constraints)
                .chain(once(output_pow_constraint))
                .collect::<Vec<_>>();
            Constraints::with_selector(q, constraints)
        });

        PoseidonConfig {
            q_full_round,
            q_partial_round,
            register_cols,
            constant_cols,
            pre_computed,
        }
    }

    fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

impl<F: PoseidonField> PoseidonChip<F> {
    // Assign constants in the circuit for a full round.
    fn assign_constants_full(
        &self,
        region: &mut Region<'_, F>,
        round_index: usize,
        offset: usize,
    ) -> Result<(), Error> {
        let round_constants = if round_index == NB_FULL_ROUNDS + NB_PARTIAL_ROUNDS - 1 {
            [F::ZERO; WIDTH]
        } else {
            F::ROUND_CONSTANTS[round_index + 1]
        };
        for (col, constant) in self.config.constant_cols[0..WIDTH]
            .iter()
            .zip(round_constants)
        {
            region.assign_fixed(
                || "load constant for a full round",
                *col,
                offset,
                || Value::known(constant),
            )?;
        }
        Ok(())
    }

    // Assign constants in the circuit for a partial round.
    fn assign_constants_partial(
        &self,
        region: &mut Region<'_, F>,
        round_batch_index: usize,
        offset: usize,
    ) -> Result<(), Error> {
        for (col, constant) in self
            .config
            .constant_cols
            .iter()
            .zip(&self.config.pre_computed.round_constants[round_batch_index])
        {
            region.assign_fixed(
                || format!("load constant for partial a round with {NB_SKIPS_CIRCUIT} skips"),
                *col,
                offset,
                || Value::known(*constant),
            )?;
        }
        Ok(())
    }

    // Operates a full round in-circuit. The variable assignment in the circuit is
    // done by calling `full_round_cpu`.
    // # Note:
    // this function does not copy the inputs in the current offset, but assumes
    // they were copied there earlier.
    fn full_round(
        &self,
        region: &mut Region<'_, F>,
        inputs: &mut [AssignedNative<F>], // Length `WIDTH`.
        round_index: usize,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_full_round.enable(region, *offset)?;
        self.assign_constants_full(region, round_index, *offset)?;

        let outputs = Value::from_iter(inputs.iter().map(|x| x.value().copied()))
            .map(|inputs: Vec<F>| {
                let mut inputs = inputs;
                full_round_cpu(round_index, &mut inputs);
                inputs
            })
            .transpose_vec(WIDTH);
        *offset += 1;
        outputs
            .iter()
            .zip(self.config.register_cols[0..WIDTH].iter())
            .zip(inputs)
            .try_for_each(|((output, column), input)| {
                region
                    .assign_advice(|| "full round output", *column, *offset, || *output)
                    .map(|assigned| *input = assigned)
            })
    }

    // Analogue for optimised partial rounds.
    // Note: initially, only the first `WIDTH` inputs are assigned, but not the
    // `NB_SKIPS_CIRCUIT` auxiliary advice columns at the current offset. This
    // function assigns them as well as the first `WIDTH` columns of the
    // resulting output.
    fn partial_round(
        &self,
        region: &mut Region<'_, F>,
        inputs: &mut [AssignedNative<F>], // Length `WIDTH`.
        round_batch_index: usize,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.config.q_partial_round.enable(region, *offset)?;
        self.assign_constants_partial(region, round_batch_index, *offset)?;

        let outputs = Value::from_iter(inputs.iter().map(|x| x.value().copied()))
            .map(|inputs: Vec<F>| {
                let mut state = inputs;
                let skip_advice_vals = partial_round_cpu_for_circuits(
                    &self.config.pre_computed,
                    round_batch_index,
                    &mut state,
                );
                for (col, skip_advice) in self.config.register_cols[WIDTH..WIDTH + NB_SKIPS_CIRCUIT]
                    .iter()
                    .zip(skip_advice_vals)
                {
                    let _ = region.assign_advice(
                        || "partial round intermediary inputs",
                        *col,
                        *offset,
                        || Value::known(skip_advice),
                    );
                }
                state
            })
            .transpose_vec(WIDTH);

        *offset += 1;
        outputs
            .iter()
            .zip(self.config.register_cols[0..WIDTH].iter())
            .zip(inputs)
            .try_for_each(|((output, column), input)| {
                region
                    .assign_advice(|| "partial round outputs", *column, *offset, || *output)
                    .map(|assigned| *input = assigned)
            })
    }

    // A combination of the different circuit gates to produce the full Poseidon
    // permutation (`NB_FULL_ROUNDS` full rounds, separated in the middle by
    // `NB_PARTIAL_ROUNDS` partial rounds, possibly with optimized skips).
    pub(super) fn permutation(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &AssignedRegister<F>,
    ) -> Result<AssignedRegister<F>, Error> {
        layouter.assign_region(
            || "permutation layout",
            |mut region| {
                let mut offset: usize = 0;

                let mut state: AssignedRegister<F> = self
                    .native_chip
                    .add_constants_in_region(
                        &mut region,
                        inputs,
                        &F::ROUND_CONSTANTS[0],
                        &mut offset,
                    )?
                    .try_into()
                    .unwrap();

                // The first full round assumes that `add_constants_in_region` above assigns
                // `state` in the same columns as Poseidon in the region. This is checked by the
                // below assertion.
                assert!(state
                    .iter()
                    .zip(self.config.register_cols)
                    .all(|(acell, col)| {
                        let col1: Column<Advice> = acell.cell().column.try_into().unwrap();
                        col1 == col
                    }));

                for round_index in 0..NB_FULL_ROUNDS / 2 {
                    self.full_round(&mut region, &mut state, round_index, &mut offset)?;
                }
                for round_batch_index in 0..NB_PARTIAL_ROUNDS / (1 + NB_SKIPS_CIRCUIT) {
                    self.partial_round(&mut region, &mut state, round_batch_index, &mut offset)?;
                }
                for round_index in
                    (NB_FULL_ROUNDS / 2 + NB_PARTIAL_ROUNDS..).take(NB_FULL_ROUNDS / 2)
                {
                    self.full_round(&mut region, &mut state, round_index, &mut offset)?;
                }
                Ok(state)
            },
        )
    }
}

impl<F: PoseidonField> SpongeInstructions<F, AssignedNative<F>, AssignedNative<F>>
    for PoseidonChip<F>
{
    type State = AssignedPoseidonState<F>;

    fn init(
        &self,
        layouter: &mut impl Layouter<F>,
        input_len: Option<usize>,
    ) -> Result<Self::State, Error> {
        let zero = self.native_chip.assign_fixed(layouter, F::ZERO)?;
        let mut register: AssignedRegister<F> = vec![zero; WIDTH].try_into().unwrap();
        register[RATE] = self.native_chip.assign_fixed(
            layouter,
            F::from_u128(input_len.map(|len| len as u128).unwrap_or(1 << 64)),
        )?;
        Ok(AssignedPoseidonState {
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
            // If `input_len` was specified, we only allow 1 squeeze.
            if state.input_len.is_some() {
                panic!(
                    "Attempting to squeeze multiple times a fixed-size Poseidon sponge (Circuit)."
                )
            };
            debug_assert!(state.queue.is_empty());
            let output = state.register[state.squeeze_position % RATE].clone();
            state.squeeze_position = (state.squeeze_position + 1) % RATE;
            return Ok(output);
        }

        match state.input_len {
            None => {
                let padding = self
                    .native_chip
                    .assign_fixed(layouter, F::from(state.queue.len() as u64))?;
                state.queue.push(padding);
            }
            Some(len) => {
                if state.queue.len() != len {
                    panic!("Inconsistent lengths in fixed-size Poseidon sponge (Circuit). Expected: {}, found: {}.", len, state.queue.len())
                };
            }
        }

        for chunk in state.queue.chunks(RATE) {
            for (entry, value) in state.register.iter_mut().zip(chunk.iter()) {
                *entry = self.native_chip.add(layouter, entry, value)?;
            }
            state.register = self.permutation(layouter, &state.register)?;
        }

        state.queue = Vec::new();
        state.squeeze_position = 1 % RATE;
        Ok(state.register[0].clone())
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

#[cfg(any(test, feature = "testing"))]
impl<F: PoseidonField> FromScratch<F> for PoseidonChip<F> {
    type Config = (NativeConfig, PoseidonConfig<F>);

    fn new_from_scratch(config: &Self::Config) -> Self {
        let native_chip = NativeChip::new(&config.0, &());
        PoseidonChip::new(&config.1, &native_chip)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let nb_advice_cols = std::cmp::max(NB_POSEIDON_ADVICE_COLS, NB_ARITH_COLS);
        let nb_fixed_cols = std::cmp::max(NB_POSEIDON_FIXED_COLS, NB_ARITH_FIXED_COLS);

        let advice_cols = (0..nb_advice_cols)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let fixed_cols = (0..nb_fixed_cols)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_cols[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_cols[..NB_ARITH_FIXED_COLS].try_into().unwrap(),
                *instance_columns,
            ),
        );
        let poseidon_config = PoseidonChip::configure(
            meta,
            &(
                advice_cols[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
                fixed_cols[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
            ),
        );

        (native_config, poseidon_config)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        NativeChip::<F>::load_from_scratch(layouter, &config.0)
    }
}

#[cfg(test)]
mod tests {
    use midnight_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};

    use super::*;
    use crate::{
        field::NativeGadget,
        hash::poseidon::{permutation_cpu, round_skips::PreComputedRoundCPU},
        instructions::{hash::tests::test_hash, sponge::tests::test_sponge, AssertionInstructions},
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug, Default)]
    struct PermCircuit<F> {
        inputs: [Value<F>; WIDTH],
        expected: [F; WIDTH],
    }

    // Implements one instance of a Poseidon circuit (i.e., where the prover
    // justifies they know the preimage of a given value). In combination with the
    // golden files, it can be used to estimate precisely the resources consumed by
    // Poseidon's hash: subtract the resources for two hashes (uncomment the line
    // at the end of this `impl` block to trigger a second dummy hash) by the
    // resources for one hash.
    impl<F: PoseidonField> Circuit<F> for PermCircuit<F> {
        type Config = <PoseidonChip<F> as FromScratch<F>>::Config;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            PoseidonChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let poseidon_chip = PoseidonChip::new_from_scratch(&config);
            PoseidonChip::load_from_scratch(&mut layouter, &config);

            let inputs: AssignedRegister<F> = poseidon_chip
                .native_chip
                .assign_many(&mut layouter, &self.inputs)?
                .try_into()
                .unwrap();
            let outputs = poseidon_chip.permutation(&mut layouter, &inputs)?;

            for (out, expected) in outputs.iter().zip(self.expected.iter()) {
                poseidon_chip
                    .native_chip
                    .assert_equal_to_fixed(&mut layouter, out, *expected)?;
            }

            // Comment or uncomment the below to get +N rows in the circuit, where N is the
            // number of rows of a single permutation.

            // let _ = poseidon_chip.permutation(&mut layouter, &inputs)?;

            Ok(())
        }
    }

    pub fn run_permutation_test<F>(inputs: [F; WIDTH], cost_model: bool)
    where
        F: PoseidonField + ff::FromUniformBytes<64> + Ord,
    {
        let pre_computed = PreComputedRoundCPU::init();
        let mut expected = inputs;
        permutation_cpu(&pre_computed, &mut expected);

        let circuit = PermCircuit {
            inputs: inputs.map(Value::known),
            expected,
        };

        let k = 10;

        MockProver::run(k, &circuit, vec![vec![], vec![]])
            .unwrap()
            .assert_satisfied();

        if cost_model {
            circuit_to_json(k, "Poseidon", "one_permutation", 0, circuit);
        }
    }

    fn run_sponge_test<F>(field: &str, cost_model: bool)
    where
        F: PoseidonField + ff::FromUniformBytes<64> + Ord,
    {
        println!(
            ">> Testing Poseidon Sponge (field {field}, {} partial-round skips)",
            NB_SKIPS_CIRCUIT
        );
        test_sponge::<
            F,
            AssignedNative<F>,
            AssignedNative<F>,
            PoseidonChip<F>,
            NativeGadget<F, _, _>,
        >(cost_model, "Poseidon", 10);
        println!("=> Done.\n")
    }

    #[test]
    // Testing Poseidon's permutation.
    fn permutation_test() {
        let inputs = [blstrs::Fq::from(0); WIDTH];
        // Set the second argument to true to experiment on the permutation cost.
        run_permutation_test(inputs, true);
    }

    #[test]
    fn sponge_test() {
        // Consistency tests between the cpu and circuit implementations of the
        // permutation.
        run_sponge_test::<blstrs::Fq>("blstrs", true);
    }

    #[test]
    fn test_poseidon_hash() {
        test_hash::<
            blstrs::Fq,
            AssignedNative<blstrs::Fq>,
            AssignedNative<blstrs::Fq>,
            PoseidonChip<blstrs::Fq>,
            NativeChip<blstrs::Fq>,
        >(true, "Poseidon", 10);
    }
}
