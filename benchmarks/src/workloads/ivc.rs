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

//! The `ivc` workloads: one step of an incrementally verifiable computation.
//!
//! The IVC circuit of `midnight-aggregation` verifies its own proofs, which
//! the library commits with [`PCS`] (fflonk with up to 8 polynomials per
//! commitment) unless told otherwise. The scheme sets the cost of the
//! in-circuit verifier, and with it the size of the IVC circuit: the more
//! polynomials per commitment, the fewer commitments the circuit has to
//! combine. These workloads run the same transition under every scheme, each
//! at the smallest size that fits it, see [`k_of`].
//!
//! A step of the library also verifies the previous proof off-circuit and
//! draws its blinding factors from the operating system, so the timed section
//! includes that verification and the proofs differ across runs.

use ff::Field;
use midnight_aggregation::ivc::{
    self, Ivc, IvcContext, IvcIO, IvcProver, IvcState, IvcTransition, IvcVerifier,
};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{
        ArithInstructions, AssignmentInstructions, PublicInputInstructions, hash::HashCPU,
    },
    types::AssignedNative,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{FflonkKZG, KZG, MidnightPCS, ZkStdLib, ZkStdLibArch};

use crate::{
    srs,
    workload::{self, Pcs, Prepared, Workload},
};

type F = midnight_curves::Fq;

/// The logarithm of the number of rows of the smallest IVC circuit that fits
/// the in-circuit verifier of `pcs` and the transition.
fn k_of(pcs: Pcs) -> u32 {
    match pcs {
        Pcs::Kzg => 18,
        Pcs::FflonkT2 | Pcs::FflonkT4 => 17,
        Pcs::FflonkT8 | Pcs::FflonkT16 => 16,
    }
}

/// The number of Poseidon iterations per step. The transition is the same
/// under every scheme, so the circuits only differ in their verifier.
const POSEIDON_ITERATIONS: usize = 50;

/// The steps proved before the timed ones. The first step has no proof to
/// verify and the second one folds a trivial accumulator, so the witness of
/// the IVC circuit is only representative from the third step on.
const WARM_UP_STEPS: usize = 2;

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![Box::new(IvcStep)]
}

/// A chain of IVC steps that all consume the same transition witness.
struct PreparedIvc<T: Ivc, P: MidnightPCS> {
    k: u32,
    prover: IvcProver<T, P>,
    verifier: IvcVerifier<T, P>,
    witness: T::Witness,
}

impl<T: Ivc, P: MidnightPCS> PreparedIvc<T, P> {
    /// Generates the keys of the IVC circuit of size `2^k` and proves the
    /// warm-up steps.
    fn new(k: u32, ctx: T::Context, witness: T::Witness) -> Self {
        let (mut prover, verifier) = ivc::setup_with_pcs::<T, P>(srs::load::<P>(k), k, ctx);
        for _ in 0..WARM_UP_STEPS {
            prover.prove_step(witness.clone()).expect("the warm-up steps are valid");
        }
        Self {
            k,
            prover,
            verifier,
            witness,
        }
    }
}

impl<T, P> Prepared for PreparedIvc<T, P>
where
    T: Ivc,
    P: MidnightPCS,
    IvcProver<T, P>: Send,
    IvcVerifier<T, P>: Send,
    T::Witness: Send,
{
    fn k(&self) -> u32 {
        self.k
    }

    fn vk_hash(&self) -> String {
        workload::vk_hash(self.verifier.vk())
    }

    fn prove(&mut self) -> Vec<u8> {
        self.prover
            .prove_step(self.witness.clone())
            .expect("proving a valid step cannot fail")
    }

    fn verify(&self, proof: &[u8]) -> bool {
        self.verifier.verify(&self.prover.instance(), proof).is_ok()
    }
}

/// One step of a Poseidon hash chain.
struct IvcStep;

impl Workload for IvcStep {
    fn name(&self) -> &'static str {
        "ivc_step"
    }

    fn supported_pcs(&self) -> Vec<Pcs> {
        Pcs::ALL.into_iter().filter(|pcs| pcs.fits(k_of(*pcs))).collect()
    }

    fn setup(&self, pcs: Pcs) -> Box<dyn Prepared> {
        type Step<P> = PreparedIvc<PoseidonChain, P>;
        let k = k_of(pcs);
        match pcs {
            Pcs::Kzg => Box::new(Step::<KZG>::new(k, (), ())),
            Pcs::FflonkT2 => Box::new(Step::<FflonkKZG<1>>::new(k, (), ())),
            Pcs::FflonkT4 => Box::new(Step::<FflonkKZG<2>>::new(k, (), ())),
            Pcs::FflonkT8 => Box::new(Step::<FflonkKZG<3>>::new(k, (), ())),
            Pcs::FflonkT16 => Box::new(Step::<FflonkKZG<4>>::new(k, (), ())),
        }
    }
}

/// The state of the hash chain: `val` is the result of applying `cnt` rounds
/// of Poseidon to zero.
#[derive(Clone, Copy, Debug)]
struct State {
    cnt: F,
    val: F,
}

/// The in-circuit counterpart of [`State`].
#[derive(Clone, Debug)]
struct AssignedState {
    cnt: AssignedNative<F>,
    val: AssignedNative<F>,
}

/// The transition that applies [`POSEIDON_ITERATIONS`] rounds of Poseidon to
/// the value and adds as many to the counter.
#[derive(Clone, Debug)]
struct PoseidonChain {
    std_lib: ZkStdLib,
}

impl IvcContext for PoseidonChain {
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

impl IvcState for PoseidonChain {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis(_ctx: &()) -> State {
        State {
            cnt: F::ZERO,
            val: F::ZERO,
        }
    }

    fn decider(_ctx: &(), _state: &State) -> bool {
        true
    }
}

impl IvcIO for PoseidonChain {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        Ok(AssignedState {
            cnt: self.std_lib.assign(layouter, value.as_ref().map(|s| s.cnt))?,
            val: self.std_lib.assign(layouter, value.as_ref().map(|s| s.val))?,
        })
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        self.std_lib.constrain_as_public_input(layouter, &state.cnt)?;
        self.std_lib.constrain_as_public_input(layouter, &state.val)
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

impl IvcTransition for PoseidonChain {
    type Witness = ();

    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nb_arith_cols: 9,
            nr_pow2range_cols: 8,
            ..ZkStdLibArch::default()
        }
    }

    fn transition(_ctx: &(), state: &State, _witness: ()) -> State {
        let mut val = state.val;
        for _ in 0..POSEIDON_ITERATIONS {
            val = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[val]);
        }
        State {
            cnt: state.cnt + F::from(POSEIDON_ITERATIONS as u64),
            val,
        }
    }

    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
        _witness: Value<()>,
    ) -> Result<AssignedState, Error> {
        let mut val = state.val.clone();
        for _ in 0..POSEIDON_ITERATIONS {
            val = self.std_lib.poseidon(layouter, &[val])?;
        }
        let cnt =
            self.std_lib
                .add_constant(layouter, &state.cnt, F::from(POSEIDON_ITERATIONS as u64))?;
        Ok(AssignedState { cnt, val })
    }
}

/// Checks the contract of [`Workload`] on `workload`, proving two steps under
/// every scheme it supports.
#[cfg(test)]
pub(super) fn check_workload(workload: &dyn Workload) {
    use std::time::Instant;

    let supported = workload.supported_pcs();
    assert!(!supported.is_empty());
    for pcs in supported {
        let start = Instant::now();
        let mut prepared = workload.setup(pcs);
        println!("{} ({pcs}): k = {}", workload.name(), prepared.k());
        println!("  setup in {:.2?}", start.elapsed());
        for _ in 0..2 {
            let start = Instant::now();
            let proof = prepared.prove();
            println!("  step in {:.2?}", start.elapsed());
            assert!(prepared.verify(&proof), "{pcs}");
            assert!(!prepared.verify(&proof[1..]), "{pcs}");
        }
        assert_eq!(prepared.vk_hash().len(), 64);
        assert_eq!(prepared.vk_hash(), workload.setup(pcs).vk_hash(), "{pcs}");
    }
}

#[cfg(test)]
mod tests {
    use midnight_aggregation::ivc::IvcCircuit;
    use midnight_proofs::{plonk::ConstraintSystem, poly::EvaluationDomain};

    use super::*;

    /// The size the IVC circuit of `2^k` rows needs under `P`.
    fn required_k<P: MidnightPCS>(k: u32) -> u32 {
        let mut cs = ConstraintSystem::default();
        let arch = IvcCircuit::<PoseidonChain, P>::arch();
        ZkStdLib::configure(&mut cs, (arch, (k - 1) as u8));
        let domain = EvaluationDomain::new(cs.degree() as u32, k);
        let relation = IvcCircuit::<PoseidonChain, P>::new(domain, cs.into_finalized(), ());
        midnight_zk_stdlib::cost_model::<_, P>(&relation, Some(k), false).k
    }

    fn check_k<P: MidnightPCS>() {
        let k = k_of(Pcs::of::<P>());
        assert!(required_k::<P>(k) <= k, "{}", Pcs::of::<P>());
        assert!(required_k::<P>(k - 1) > k - 1, "{}", Pcs::of::<P>());
    }

    #[test]
    fn k_of_is_the_smallest_size_that_fits() {
        check_k::<KZG>();
        check_k::<FflonkKZG<1>>();
        check_k::<FflonkKZG<2>>();
        check_k::<FflonkKZG<3>>();
        check_k::<FflonkKZG<4>>();
    }

    #[test]
    fn the_largest_chunks_do_not_fit_the_srs() {
        let mut expected = Pcs::ALL.to_vec();
        expected.pop();
        assert_eq!(IvcStep.supported_pcs(), expected);
    }

    #[test]
    #[ignore = "slow: generates the keys of the IVC circuit twice and proves six steps"]
    fn ivc_step_proves_repeatedly() {
        check_workload(&IvcStep);
    }
}
