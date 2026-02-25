//! Incrementally Verifiable Computation (IVC) using the aggregation API.
//!
//! This example demonstrates how to use the [`Ivc`] API with a transition
//! function that iteratively hashes a value using Poseidon.
//!
//! DO NOT add this example to the CI as it is slow.
//!
//! Run with `features = truncated-challenges`.

use std::time::Instant;

use ff::Field;
use midnight_aggregation::ivc::{self, IvcState, IvcTransition};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, *},
    types::{AssignedBit, AssignedNative, InnerValue, Instantiable},
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

impl InnerValue for AssignedState {
    type Element = State;

    fn value(&self) -> Value<State> {
        (self.cnt.value()).zip(self.val.value()).map(|(cnt, val)| State {
            cnt: *cnt,
            val: *val,
        })
    }
}

impl Instantiable<F> for AssignedState {
    fn as_public_input(element: &State) -> Vec<F> {
        vec![element.cnt, element.val]
    }
}

/// IVC transition that applies N rounds of Poseidon hashing to the value, and
/// increments the counter by N.
#[derive(Clone, Debug)]
pub struct PoseidonChain<const N: usize> {
    std_lib: ZkStdLib,
}

impl<const N: usize> IvcState for PoseidonChain<N> {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis() -> Self::State {
        State {
            cnt: F::ZERO,
            val: F::ZERO,
        }
    }

    fn is_genesis(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<AssignedBit<F>, Error> {
        let cnt_is_zero = self.std_lib.bls12_381_scalar().is_zero(layouter, &state.cnt)?;
        let val_is_zero = self.std_lib.bls12_381_scalar().is_zero(layouter, &state.val)?;
        self.std_lib.and(layouter, &[cnt_is_zero, val_is_zero])
    }
}

impl<const N: usize> AssignmentInstructions<F, AssignedState> for PoseidonChain<N> {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381_scalar();
        Ok(AssignedState {
            cnt: scalar_chip.assign(layouter, value.as_ref().map(|s| s.cnt))?,
            val: scalar_chip.assign(layouter, value.as_ref().map(|s| s.val))?,
        })
    }

    fn assign_fixed(
        &self,
        _layouter: &mut impl Layouter<F>,
        _constant: State,
    ) -> Result<AssignedState, Error> {
        unimplemented!("not used by IVC")
    }
}

impl<const N: usize> PublicInputInstructions<F, AssignedState> for PoseidonChain<N> {
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![state.cnt.clone(), state.val.clone()])
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        let scalar_chip = self.std_lib.bls12_381_scalar();
        scalar_chip.constrain_as_public_input(layouter, &state.cnt)?;
        scalar_chip.constrain_as_public_input(layouter, &state.val)
    }

    fn assign_as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        _value: Value<State>,
    ) -> Result<AssignedState, Error> {
        unimplemented!("not used by IVC")
    }
}

impl<const N: usize> From<ZkStdLib> for PoseidonChain<N> {
    fn from(std_lib: ZkStdLib) -> Self {
        PoseidonChain { std_lib }
    }
}

impl<const N: usize> IvcTransition for PoseidonChain<N> {
    // This transition function is deterministic, it does not depend on a witness.
    type Witness = ();

    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn transition(state: &Self::State, _witness: Self::Witness) -> Self::State {
        let mut val = state.val;
        for _ in 0..N {
            val = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[val]);
        }
        State {
            cnt: state.cnt + F::from(N as u64),
            val,
        }
    }

    fn assert_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        next_state: &Self::AssignedState,
        _witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let scalar_chip = self.std_lib.bls12_381_scalar();

        let mut val = state.val.clone();
        for _ in 0..N {
            val = self.std_lib.poseidon(layouter, &[val])?;
        }

        let expected_cnt = scalar_chip.add_constant(layouter, &state.cnt, F::from(N as u64))?;
        scalar_chip.assert_equal(layouter, &expected_cnt, &next_state.cnt)?;
        scalar_chip.assert_equal(layouter, &val, &next_state.val)
    }
}

fn main() {
    // Circuit size parameter (log2 of rows). Must be large enough to fit the
    // IVC circuit; ideally the minimum possible value. If too small, the error
    // message will hint at a valid (but not necessarily optimal) value, e.g.
    // `keygen_vk should not fail: SrsError(14, 19)` means K = 19 works, but a
    // smaller K might too. Binary-search to find it.
    const K: u32 = 18;

    const N: usize = 1_000; // Number of Poseidon iteration per IVC step.
    const STEPS: usize = 3; // Number of IVC steps to run.

    let srs = midnight_zk_stdlib::utils::plonk_api::filecoin_srs(K);

    let start = Instant::now();
    let (mut prover, verifier) = ivc::setup::<PoseidonChain<N>>(srs, K);
    println!("IVC setup completed in {:.2?}", start.elapsed());

    for i in 0..STEPS {
        let start = Instant::now();
        let proof = prover.prove_step(()).unwrap();
        let prove_time = start.elapsed();

        let instance = prover.instance();

        let start = Instant::now();
        verifier.verify(&instance, &proof).unwrap();
        let verify_time = start.elapsed();

        println!("Step {i}: prove {prove_time:.2?}, verify {verify_time:.2?}");
    }

    println!(
        "IVC completed: {STEPS} steps from\n genesis {:?}\n      to {:?}",
        PoseidonChain::<N>::genesis(),
        prover.instance().state()
    );
}
