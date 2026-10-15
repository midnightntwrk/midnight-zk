//! Poseidon hash-chain transition shared by the IVC examples.
//!
//! The state is a counter and a hash-chain value; each step applies `N`
//! rounds of Poseidon to the value and increments the counter by `N`.

use ff::Field;
use midnight_aggregation::ivc::{IvcContext, IvcIO, IvcState, IvcTransition};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, *},
    types::AssignedNative,
    verifier::{BlstrsEmulation, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;

/// IVC state: a counter and a hash-chain value.
///
/// A valid IVC state is such that `val` is the result of applying `cnt` rounds
/// of Poseidon to the genesis value of 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct State {
    cnt: F,
    val: F,
}

/// In-circuit counterpart of [`State`].
#[derive(Clone, Debug)]
pub struct AssignedState {
    cnt: AssignedNative<F>,
    val: AssignedNative<F>,
}

/// IVC transition that applies N rounds of Poseidon hashing to the value, and
/// increments the counter by N.
#[derive(Clone, Debug)]
pub struct PoseidonChain<const N: usize> {
    std_lib: ZkStdLib,
}

impl<const N: usize> IvcContext for PoseidonChain<N> {
    type Context = ();

    fn new(std_lib: ZkStdLib, _ctx: &()) -> Self {
        PoseidonChain { std_lib }
    }

    fn write_context<W: std::io::Write>(_ctx: &(), _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_context<R: std::io::Read>(_reader: &mut R) -> std::io::Result<()> {
        Ok(())
    }
}

impl<const N: usize> IvcState for PoseidonChain<N> {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis(_ctx: &()) -> Self::State {
        State {
            cnt: F::ZERO,
            val: F::ZERO,
        }
    }

    fn decider(_ctx: &Self::Context, _state: &Self::State) -> bool {
        true
    }
}

impl<const N: usize> IvcIO for PoseidonChain<N> {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381().scalar_field_chip();
        Ok(AssignedState {
            cnt: scalar_chip.assign(layouter, value.as_ref().map(|s| s.cnt))?,
            val: scalar_chip.assign(layouter, value.as_ref().map(|s| s.val))?,
        })
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        let scalar_chip = self.std_lib.bls12_381().scalar_field_chip();
        scalar_chip.constrain_as_public_input(layouter, &state.cnt)?;
        scalar_chip.constrain_as_public_input(layouter, &state.val)
    }

    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![state.cnt.clone(), state.val.clone()])
    }

    fn format_public_input(state: &State) -> Vec<F> {
        vec![state.cnt, state.val]
    }
}

impl<const N: usize> IvcTransition for PoseidonChain<N> {
    // This transition function is deterministic, it does not depend on a witness.
    type Witness = ();

    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nb_arith_cols: 9,
            nr_pow2range_cols: 8,
            ..ZkStdLibArch::default()
        }
    }

    fn transition(_ctx: &(), state: &Self::State, _witness: Self::Witness) -> Self::State {
        let mut val = state.val;
        for _ in 0..N {
            val = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[val]);
        }
        State {
            cnt: state.cnt + F::from(N as u64),
            val,
        }
    }

    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        _witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381().scalar_field_chip();

        let mut val = state.val.clone();
        for _ in 0..N {
            val = self.std_lib.poseidon(layouter, &[val])?;
        }

        let cnt = scalar_chip.add_constant(layouter, &state.cnt, F::from(N as u64))?;
        Ok(AssignedState { cnt, val })
    }
}
