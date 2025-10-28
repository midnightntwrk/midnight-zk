//! A gadget for sponge-based Poseidon hashing with WIDTH = 3 and RATE = 2.

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::ErrorFront as Error};
#[cfg(any(test, feature = "testing"))]
use {
    crate::{hash::poseidon::Pow5Config, testing_utils::FromScratch},
    halo2_proofs::plonk::{Column, ConstraintSystem, Instance},
};

use super::{
    cpu::Spec, permute, pow5::StateWord, P128Pow5T3, PaddedWord, Pow5Chip, Pow5SpongeChip,
    VariableLength,
};
use crate::{
    hash::poseidon::{cpu::Absorbing, PoseidonInstructions, PoseidonSpongeInstructions},
    instructions::{hash::HashCPU, HashInstructions, SpongeCPU, SpongeInstructions},
    types::AssignedNative,
};

const WIDTH: usize = 3;
const RATE: usize = 2;

/// Gadget for Poseidon sponge-based hashing operations.
#[derive(Clone, Debug)]
pub struct PoseidonGadget<F: PrimeField> {
    pow5_sponge_chip: Pow5SpongeChip<F, VariableLength, WIDTH, RATE>,
}

impl<F: PrimeField> PoseidonGadget<F>
where
    P128Pow5T3: Spec<F, WIDTH, RATE>,
{
    /// Creates a new PoseidonChip given the corresponding configuration.
    pub fn new(pow5_chip: &Pow5Chip<F, WIDTH, RATE>) -> Self {
        Self {
            pow5_sponge_chip: Pow5SpongeChip::from_pow5_chip(pow5_chip.clone(), VariableLength),
        }
    }
}

/// Off-circuit Poseidon state.
#[derive(Clone, Debug)]
pub struct PoseidonState<F: PrimeField> {
    register: [F; WIDTH],
    queue: Vec<F>,
    squeeze_position: usize,
}

/// In-circuit Poseidon state.
#[derive(Clone, Debug)]
pub struct AssignedPoseidonState<F: PrimeField> {
    register: [StateWord<F>; WIDTH],
    queue: Vec<PaddedWord<F>>,
    squeeze_position: usize,
}

impl<F: PrimeField> SpongeCPU<F, F> for PoseidonGadget<F>
where
    P128Pow5T3: Spec<F, WIDTH, RATE>,
{
    type StateCPU = PoseidonState<F>;

    fn init() -> Self::StateCPU {
        let mut register = [F::ZERO; WIDTH];
        register[RATE] = F::from_u128(1 << 64);
        PoseidonState {
            register,
            queue: Vec::new(),
            squeeze_position: 0,
        }
    }

    fn absorb(state: &mut Self::StateCPU, inputs: &[F]) {
        state.queue.extend(inputs);
        state.squeeze_position = 0;
    }

    fn squeeze(state: &mut Self::StateCPU) -> F {
        if state.squeeze_position > 0 {
            debug_assert!(state.queue.is_empty());
            let output = state.register[state.squeeze_position];
            state.squeeze_position = (state.squeeze_position + 1) % RATE;
            return output;
        }

        let (round_constants, mds, _) = <P128Pow5T3 as Spec<F, WIDTH, RATE>>::constants();

        let padding = F::from(state.queue.len() as u64);
        state.queue.push(padding);

        for chunk in state.queue.chunks(RATE) {
            for (entry, value) in state.register.iter_mut().zip(chunk.iter()) {
                *entry += value;
            }

            permute::<F, P128Pow5T3, WIDTH, RATE>(&mut state.register, &mds, &round_constants);
        }

        state.queue = Vec::new();
        state.squeeze_position = 1;

        state.register[0]
    }
}

impl<F: PrimeField> SpongeInstructions<F, AssignedNative<F>, AssignedNative<F>>
    for PoseidonGadget<F>
where
    P128Pow5T3: Spec<F, WIDTH, RATE>,
{
    type State = AssignedPoseidonState<F>;

    fn init(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error> {
        let register = PoseidonSpongeInstructions::<_, P128Pow5T3, _, WIDTH, RATE>::initial_state(
            &self.pow5_sponge_chip,
            layouter,
        )?;
        Ok(AssignedPoseidonState {
            register,
            queue: Vec::new(),
            squeeze_position: 0,
        })
    }

    fn absorb(
        &self,
        _layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
        inputs: &[AssignedNative<F>],
    ) -> Result<(), Error> {
        state.queue.extend(
            inputs
                .iter()
                .map(|input| PaddedWord::Message(input.clone())),
        );
        state.squeeze_position = 0;
        Ok(())
    }

    fn squeeze(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut Self::State,
    ) -> Result<AssignedNative<F>, Error> {
        if state.squeeze_position > 0 {
            debug_assert!(state.queue.is_empty());
            let output = state.register[state.squeeze_position].clone();
            state.squeeze_position = (state.squeeze_position + 1) % RATE;
            return Ok(output.into());
        }

        let padding = F::from(state.queue.len() as u64);
        state.queue.push(PaddedWord::Padding(padding));

        for chunk in state.queue.chunks(RATE) {
            let mut input: [Option<PaddedWord<F>>; RATE] =
                vec![Some(PaddedWord::Padding(F::ZERO)); RATE]
                    .try_into()
                    .unwrap();
            for (inp, c) in input.iter_mut().zip(chunk.iter()) {
                *inp = Some(c.clone());
            }

            state.register =
                PoseidonSpongeInstructions::<_, P128Pow5T3, _, WIDTH, RATE>::add_input(
                    &self.pow5_sponge_chip,
                    layouter,
                    &state.register,
                    &Absorbing(input),
                )?;

            state.register = PoseidonInstructions::<_, P128Pow5T3, WIDTH, RATE>::permute(
                &self.pow5_sponge_chip,
                layouter,
                &state.register,
            )?;
        }

        state.queue = Vec::new();
        state.squeeze_position = 1;

        Ok(state.register[0].clone().into())
    }
}

impl<F: PrimeField> HashCPU<F, F> for PoseidonGadget<F> where P128Pow5T3: Spec<F, WIDTH, RATE> {}

impl<F: PrimeField> HashInstructions<F, AssignedNative<F>, AssignedNative<F>> for PoseidonGadget<F> where
    P128Pow5T3: Spec<F, WIDTH, RATE>
{
}

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> FromScratch<F> for PoseidonGadget<F>
where
    P128Pow5T3: Spec<F, WIDTH, RATE>,
{
    type Config = Pow5Config<F, WIDTH, RATE>;

    fn new_from_scratch(config: &Self::Config) -> Self {
        let pow5_chip = Pow5Chip::construct(config.clone());
        Self::new(&pow5_chip)
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        _instance_column: &Column<Instance>,
    ) -> Self::Config {
        let advice_columns: [_; 4] = core::array::from_fn(|_| meta.advice_column());
        let fixed_columns: [_; 6] = core::array::from_fn(|_| meta.fixed_column());
        let constants_column = meta.fixed_column();
        meta.enable_constant(constants_column);

        Pow5Chip::configure::<P128Pow5T3>(
            meta,
            advice_columns[..3].try_into().unwrap(),
            advice_columns[3],
            fixed_columns[..3].try_into().unwrap(),
            fixed_columns[3..6].try_into().unwrap(),
        )
    }

    fn load_from_scratch(_layouter: &mut impl Layouter<F>, _config: &Self::Config) {}
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{field::NativeGadget, instructions::sponge::tests::test_sponge};

    fn run_test<F: PrimeField>(cost_model: bool)
    where
        F: PrimeField + ff::FromUniformBytes<64> + Ord,
        P128Pow5T3: Spec<F, WIDTH, RATE>,
    {
        test_sponge::<
            F,
            AssignedNative<F>,
            AssignedNative<F>,
            PoseidonGadget<F>,
            NativeGadget<F, _, _>,
        >(cost_model, "PoseidonSponge", 13)
    }

    #[test]
    fn test_poseidon_sponge() {
        run_test::<blstrs::Scalar>(true);
        run_test::<halo2curves::pasta::Fp>(false);
        run_test::<halo2curves::pasta::Fq>(false);
    }
}
