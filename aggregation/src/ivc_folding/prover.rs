//! Stateful folding-IVC prover.
//!
//! A step never produces a proof: it folds the previous step's instance into
//! the running accumulator natively, then synthesises the step circuit and
//! runs its commit phases only (the partial proof that the next step reads).
//! [`FoldingIvcProver::finalize`] folds the last instance and proves the
//! final accumulator with the decider.

use midnight_proofs::{
    circuit::Value,
    plonk::protogalaxy::{ProverAccumulator, ProverInstance, commit_instance, prove_relaxed_trace},
    transcript::Transcript,
};
use midnight_zk_stdlib::{MidnightCircuit, Relation};
use rand::rngs::OsRng;

use super::{
    FoldingIvcCircuit, FoldingIvcKeys, FoldingPCS,
    circuit::{FoldingIvcStepInstance, FoldingIvcWitness},
    types::{FoldingIvcInstance, FoldingIvcProof, Tr, accumulator_hash},
};
use crate::ivc::{F, Ivc, IvcError};

/// Stateful folding-IVC prover: the current state, the running accumulator
/// (prover side, `None` for the default one) and the instance of the latest
/// step with its partial proof.
#[derive(Debug)]
pub struct FoldingIvcProver<'a, T: Ivc> {
    keys: &'a FoldingIvcKeys<T>,
    state: T::State,
    acc: Option<ProverAccumulator<'a, F, FoldingPCS>>,
    last: Option<(ProverInstance<'a, F, FoldingPCS>, Vec<u8>)>,
}

/// What a step folds into the next accumulator, and the corresponding
/// witness parts of the step circuit.
struct Folded<'a> {
    acc: Option<ProverAccumulator<'a, F, FoldingPCS>>,
    is_first: bool,
    partial_proof: Vec<u8>,
    folding_proof: Vec<u8>,
}

impl<'a, T: Ivc> FoldingIvcProver<'a, T> {
    /// A prover at the genesis state.
    pub fn new(keys: &'a FoldingIvcKeys<T>) -> Self {
        FoldingIvcProver {
            keys,
            state: T::genesis(keys.relation.ctx()),
            acc: None,
            last: None,
        }
    }

    /// Returns the current state.
    pub fn state(&self) -> &T::State {
        &self.state
    }

    /// Advances the chain by one transition.
    pub fn prove_step(&mut self, transition_witness: T::Witness) -> Result<(), IvcError> {
        let keys = self.keys;
        let pk = &keys.pk;
        let next = T::transition(keys.relation.ctx(), &self.state, transition_witness.clone());
        let prev_acc = (self.acc.as_ref()).map_or(&keys.dummy.acc, |acc| acc.accumulator()).clone();
        let folded = self.fold_last()?;

        let instance = FoldingIvcStepInstance {
            vk: pk.get_vk().clone(),
            state: next.clone(),
            acc_hash: accumulator_hash(folded.acc.as_ref().map(|acc| acc.accumulator())),
        };
        let pi = FoldingIvcCircuit::<T>::format_instance(&instance)?;
        let witness = FoldingIvcWitness {
            prev_state: self.state.clone(),
            prev_acc,
            is_first: folded.is_first,
            partial_proof: folded.partial_proof,
            folding_proof: folded.folding_proof,
            transition_witness,
        };
        let circuit = MidnightCircuit::new(
            &keys.relation,
            Value::known(instance),
            Value::known(witness),
            Some(keys.relation.k()),
        );
        let mut transcript = Tr::init();
        let fresh = commit_instance(
            &keys.params,
            pk,
            &circuit,
            &[&[], &pi],
            &mut transcript,
            OsRng,
        )?;

        self.state = next;
        self.acc = folded.acc;
        self.last = Some((fresh, transcript.finalize()));
        Ok(())
    }

    /// Folds the latest instance into the accumulator: nothing at genesis
    /// (the next accumulator is the default one), init if the accumulator is
    /// the default one, fold otherwise.
    fn fold_last(&mut self) -> Result<Folded<'a>, IvcError> {
        let pk = &self.keys.pk;
        let dummy = &self.keys.dummy;
        let Some((fresh, partial_proof)) = self.last.take() else {
            return Ok(Folded {
                acc: None,
                is_first: false,
                partial_proof: dummy.partial_proof.clone(),
                folding_proof: dummy.folding_proof.clone(),
            });
        };
        let mut transcript = Tr::init();
        let (acc, is_first, folding_proof) = match self.acc.take() {
            None => {
                let acc = ProverAccumulator::init(pk, fresh, &mut transcript)?;
                (acc, true, dummy.folding_proof.clone())
            }
            Some(acc) => {
                let acc_hash = accumulator_hash(Some(acc.accumulator()));
                let acc = acc.fold(pk, vec![fresh], Some(acc_hash), &mut transcript)?;
                (acc, false, transcript.finalize())
            }
        };
        Ok(Folded {
            acc: Some(acc),
            is_first,
            partial_proof,
            folding_proof,
        })
    }

    /// Folds the last instance and proves the final accumulator with the
    /// decider. Returns the instance (current state and accumulator) and its
    /// proof.
    pub fn finalize(mut self) -> Result<(FoldingIvcInstance<T>, FoldingIvcProof), IvcError> {
        let keys = self.keys;
        let pk = &keys.pk;
        let (fresh, partial_proof) = self.last.take().ok_or(IvcError::InvalidInstance)?;
        let instance = FoldingIvcInstance {
            state: self.state.clone(),
            acc: self.acc.as_ref().map(|acc| acc.accumulator().clone()),
        };

        let mut transcript = Tr::init();
        let acc = match self.acc.take() {
            None => ProverAccumulator::init(pk, fresh, &mut transcript)?,
            Some(acc) => {
                let acc_hash = accumulator_hash(Some(acc.accumulator()));
                acc.fold(pk, vec![fresh], Some(acc_hash), &mut transcript)?
            }
        };
        let folding_proof = transcript.finalize();

        let mut transcript = Tr::init();
        prove_relaxed_trace(&keys.params, pk, acc, &mut transcript)?;

        let proof = FoldingIvcProof {
            partial_proof,
            folding_proof,
            decider_proof: transcript.finalize(),
        };
        Ok((instance, proof))
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_circuits::{instructions::*, types::AssignedNative};
    use midnight_proofs::{
        circuit::Layouter, plonk::Error, poly::commitment::PolynomialCommitmentScheme,
    };
    use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};

    use super::*;
    use crate::{
        ivc::{IvcContext, IvcIO, IvcState, IvcTransition},
        ivc_folding::setup,
    };

    /// The smallest transition: a counter incremented by one.
    #[derive(Clone, Debug)]
    struct Counter {
        std_lib: ZkStdLib,
    }

    impl IvcContext for Counter {
        type Context = ();

        fn new(std_lib: ZkStdLib, _ctx: &()) -> Self {
            Counter { std_lib }
        }

        fn write_context<W: std::io::Write>(_ctx: &(), _writer: &mut W) -> std::io::Result<()> {
            Ok(())
        }

        fn read_context<R: std::io::Read>(_reader: &mut R) -> std::io::Result<()> {
            Ok(())
        }
    }

    impl IvcState for Counter {
        type State = F;
        type AssignedState = AssignedNative<F>;

        fn genesis(_ctx: &()) -> F {
            F::ZERO
        }

        fn decider(_ctx: &(), _state: &F) -> bool {
            true
        }
    }

    impl IvcIO for Counter {
        fn assign(
            &self,
            layouter: &mut impl Layouter<F>,
            value: Value<F>,
        ) -> Result<AssignedNative<F>, Error> {
            self.std_lib.assign(layouter, value)
        }

        fn constrain_as_public_input(
            &self,
            layouter: &mut impl Layouter<F>,
            state: &AssignedNative<F>,
        ) -> Result<(), Error> {
            self.std_lib.constrain_as_public_input(layouter, state)
        }

        fn as_public_input(
            &self,
            _layouter: &mut impl Layouter<F>,
            state: &AssignedNative<F>,
        ) -> Result<Vec<AssignedNative<F>>, Error> {
            Ok(vec![state.clone()])
        }

        fn format_public_input(state: &F) -> Vec<F> {
            vec![*state]
        }
    }

    impl IvcTransition for Counter {
        type Witness = ();

        fn arch() -> ZkStdLibArch {
            ZkStdLibArch::default()
        }

        fn transition(_ctx: &(), state: &F, _witness: ()) -> F {
            *state + F::ONE
        }

        fn circuit_transition(
            &self,
            layouter: &mut impl Layouter<F>,
            state: &AssignedNative<F>,
            _witness: Value<()>,
        ) -> Result<AssignedNative<F>, Error> {
            self.std_lib.add_constant(layouter, state, F::ONE)
        }
    }

    /// Log2 of the rows of the step circuit.
    const K: u32 = 15;
    const STEPS: u64 = 3;

    #[test]
    fn prove_and_verify() {
        let (keys, verifier) = setup::<Counter>(FoldingPCS::gen_params(K), K, ());
        let mut prover = FoldingIvcProver::new(&keys);
        for _ in 0..STEPS {
            prover.prove_step(()).unwrap();
        }
        let (instance, mut proof) = prover.finalize().unwrap();
        assert_eq!(*instance.state(), F::from(STEPS));
        verifier.verify(&instance, &proof).expect("honest proof rejected");

        let last = proof.decider_proof.len() / 2;
        proof.decider_proof[last] ^= 1;
        assert!(
            verifier.verify(&instance, &proof).is_err(),
            "tampered proof accepted"
        );
    }
}
