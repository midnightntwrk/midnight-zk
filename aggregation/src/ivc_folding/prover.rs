//! Stateful folding-IVC prover.
//!
//! A step never produces a proof: it folds the previous step's instance into
//! the running accumulator natively, then synthesises the step circuit and
//! runs its commit phases only (the partial proof that the next step reads).
//! [`FoldingIvcProver::finalize`] folds the last instance and proves the
//! final accumulator with the decider.

use std::time::Instant;

use midnight_proofs::{
    circuit::Value,
    plonk::protogalaxy::{ProverAccumulator, ProverInstance, commit_instance, prove_relaxed_trace},
    transcript::Transcript,
};
use midnight_zk_stdlib::{DefaultPCS, MidnightCircuit, Relation};
use rand::rngs::OsRng;

use super::{
    FoldingIvcCircuit, FoldingIvcKeys,
    circuit::{FoldingIvcStepInstance, FoldingIvcWitness},
    types::{FinalTimings, FoldingIvcInstance, FoldingIvcProof, StepTimings, Tr, accumulator_hash},
};
use crate::ivc::{F, Ivc, IvcError};

/// Stateful folding-IVC prover: the current state, the running accumulator
/// (prover side, `None` for the default one) and the instance of the latest
/// step with its partial proof.
#[derive(Debug)]
pub struct FoldingIvcProver<'a, T: Ivc> {
    keys: &'a FoldingIvcKeys<T>,
    state: T::State,
    acc: Option<ProverAccumulator<'a, F, DefaultPCS>>,
    last: Option<(ProverInstance<'a, F, DefaultPCS>, Vec<u8>)>,
}

/// What a step folds into the next accumulator, and the corresponding
/// witness parts of the step circuit.
struct Folded<'a> {
    acc: Option<ProverAccumulator<'a, F, DefaultPCS>>,
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
    pub fn prove_step(&mut self, transition_witness: T::Witness) -> Result<StepTimings, IvcError> {
        let ctx = self.keys.relation.ctx();
        let next = T::transition(ctx, &self.state, transition_witness.clone());
        self.prove_step_claiming(transition_witness, next)
    }

    /// Negative testing only: like [`Self::prove_step`], but the step's
    /// instance claims `claimed_next` as the next state. Unless it is the
    /// honest next state, the committed step circuit is not satisfied and the
    /// final verification must fail.
    #[doc(hidden)]
    pub fn prove_step_claiming(
        &mut self,
        transition_witness: T::Witness,
        claimed_next: T::State,
    ) -> Result<StepTimings, IvcError> {
        let keys = self.keys;
        let start = Instant::now();
        let prev_acc = (self.acc.as_ref()).map_or(&keys.dummy.acc, |acc| acc.accumulator()).clone();
        let folded = self.fold_last()?;
        let fold = start.elapsed();

        let start = Instant::now();
        let pk = keys.pk.pk();
        let instance = FoldingIvcStepInstance {
            vk: pk.get_vk().clone(),
            state: claimed_next.clone(),
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
        let commit = start.elapsed();

        self.state = claimed_next;
        self.acc = folded.acc;
        self.last = Some((fresh, transcript.finalize()));
        Ok(StepTimings { fold, commit })
    }

    /// Folds the latest instance into the accumulator: nothing at genesis
    /// (the next accumulator is the default one), init if the accumulator is
    /// the default one, fold otherwise.
    fn fold_last(&mut self) -> Result<Folded<'a>, IvcError> {
        let pk = self.keys.pk.pk();
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
                let acc = acc.fold(pk, fresh, Some(acc_hash), &mut transcript)?;
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
    pub fn finalize(
        mut self,
    ) -> Result<(FoldingIvcInstance<T>, FoldingIvcProof, FinalTimings), IvcError> {
        let keys = self.keys;
        let pk = keys.pk.pk();
        let (fresh, partial_proof) = self.last.take().ok_or(IvcError::InvalidInstance)?;
        let instance = FoldingIvcInstance {
            state: self.state.clone(),
            acc: self.acc.as_ref().map(|acc| acc.accumulator().clone()),
        };

        let start = Instant::now();
        let mut transcript = Tr::init();
        let acc = match self.acc.take() {
            None => ProverAccumulator::init(pk, fresh, &mut transcript)?,
            Some(acc) => {
                let acc_hash = accumulator_hash(Some(acc.accumulator()));
                acc.fold(pk, fresh, Some(acc_hash), &mut transcript)?
            }
        };
        let folding_proof = transcript.finalize();
        let fold = start.elapsed();

        let start = Instant::now();
        let mut transcript = Tr::init();
        prove_relaxed_trace(&keys.params, pk, acc, &mut transcript)?;
        let decider = start.elapsed();

        let proof = FoldingIvcProof {
            partial_proof,
            folding_proof,
            decider_proof: transcript.finalize(),
        };
        Ok((instance, proof, FinalTimings { fold, decider }))
    }
}
