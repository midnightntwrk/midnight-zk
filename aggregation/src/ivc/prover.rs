//! Stateful IVC prover.
//!
//! The [`IvcProver`] drives the incremental proving process. It holds the
//! current state, the proof of the latest step, and the accumulated
//! verification state. Each call to [`IvcProver::prove_step`] advances the
//! chain by one transition: it verifies the previous proof off-circuit,
//! accumulates the result, produces a new proof for the updated state, and
//! stores everything internally so the next step can build on it.

use group::Group;
use midnight_circuits::{
    hash::poseidon::PoseidonState,
    types::Instantiable,
    verifier::{Accumulator, AssignedAccumulator, AssignedVk},
};
use midnight_proofs::{
    plonk::{self},
    poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::MidnightPK;
use rand::rngs::OsRng;

use super::{IvcCircuit, IvcError, IvcIO, IvcInstance, IvcTransition, IvcWitness, C, E, F, S};

/// Stateful IVC prover holding:
/// - the SRS (params),
/// - the circuit relation,
/// - the proving key,
/// - the current proof state (state, proof bytes, accumulator).
///
/// Created via [`super::setup()`]. Use [`IvcProver::prove_step`] to advance
/// the state and [`IvcProver::instance`] to obtain the latest instance.
#[derive(Clone, Debug)]
pub struct IvcProver<T: IvcTransition + IvcIO> {
    pub(crate) params: ParamsKZG<E>,
    pub(crate) relation: IvcCircuit<T>,
    pub(crate) pk: MidnightPK<IvcCircuit<T>>,
    pub(crate) state: T::State,
    pub(crate) proof: Vec<u8>,
    pub(crate) acc: Accumulator<S>,
}

impl<T: IvcTransition + IvcIO> IvcProver<T> {
    /// Resets the prover to a previously saved state, allowing it to resume
    /// proving from an intermediate point in the chain.
    pub fn resume_from(&mut self, state: T::State, proof: Vec<u8>, acc: Accumulator<S>) {
        self.state = state;
        self.proof = proof;
        self.acc = acc;
    }

    /// Creates an IVC proof for a single transition step.
    ///
    /// Computes the next state (off-circuit) from the current internal state
    /// and the given witness, produces a proof, and updates the internal state.
    ///
    /// If the current state is genesis (no previous proof), a trivial
    /// accumulator is used instead of verifying the previous proof.
    pub fn prove_step(&mut self, transition_witness: T::Witness) -> Result<Vec<u8>, IvcError> {
        let next_state =
            T::transition(self.relation.ctx(), &self.state, transition_witness.clone());
        let is_genesis = self.proof.is_empty();

        let vk = self.pk.pk().get_vk();
        let vk_repr = vk.transcript_repr();

        let fixed_bases = midnight_circuits::verifier::fixed_bases::<S>("self_vk", vk);

        // Off-circuit verification of the previous proof.
        let proof_acc = if is_genesis {
            // In the case of genesis, we simply set `proof_acc` to be the trivial
            // accumulator (which evaluates to the identity point on both sides).
            //
            // Arguably, this is not equivalent to what is happening in-circuit (where we
            // scale the result of `prepare` by bit 0) as the trivial accumulator only has 1
            // base, whereas the result of `prepare` may have several bases.
            //
            // That means that the batching challenge `r` used for accumulating `proof_acc`
            // with `acc` will be different in the off-circuit and in-circuit executions
            // during the genesis iteration. This is not a problem if `acc` also evaluates
            // to the identity in such iteration (which is the case by construction)
            // essentially because `0 + r * 0` equals `0` for any `r` so the resulting
            // accumulator (so-called `next_acc`) will be the same in both (in-circuit and
            // off-circuit) executions after `collapse`.
            Accumulator::<S>::trivial(&fixed_bases.keys().cloned().collect::<Vec<_>>())
        } else {
            // Construct the public inputs of the previous proof.
            let prev_pi = [
                AssignedVk::<S>::as_public_input(vk),
                T::format_public_input(&self.state),
                AssignedAccumulator::<S>::as_public_input(&self.acc),
            ]
            .concat();

            let mut transcript =
                CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&self.proof);
            let dual_msm = plonk::prepare::<
                F,
                KZGCommitmentScheme<E>,
                CircuitTranscript<PoseidonState<F>>,
            >(vk, &[&[C::identity()]], &[&[&prev_pi]], &mut transcript)?;

            if !dual_msm.clone().check(&self.params.verifier_params()) {
                return Err(IvcError::InvalidProof);
            }

            Accumulator::from_dual_msm(dual_msm, "self_vk", &fixed_bases)
        };

        // Accumulate the proof accumulator with the previous accumulator.
        let mut next_acc = Accumulator::accumulate(&[proof_acc, self.acc.clone()]);
        next_acc.collapse();

        let instance = IvcInstance {
            vk_repr,
            state: next_state.clone(),
            acc: next_acc.clone(),
        };

        let witness = IvcWitness {
            prev_state: self.state.clone(),
            prev_acc: self.acc.clone(),
            prev_proof: self.proof.clone(),
            transition_witness,
        };

        let proof = midnight_zk_stdlib::prove::<IvcCircuit<T>, PoseidonState<F>>(
            &self.params,
            &self.pk,
            &self.relation,
            &instance,
            witness,
            OsRng,
        )?;

        self.state = next_state;
        self.proof = proof.clone();
        self.acc = next_acc;

        Ok(proof)
    }

    /// Returns the public instance corresponding to the current IVC state.
    ///
    /// Together with the latest proof bytes (returned by
    /// [`prove_step`](Self::prove_step)), this instance guarantees the
    /// existence of a valid chain of transitions from genesis to the
    /// current state.
    pub fn instance(&self) -> IvcInstance<T> {
        IvcInstance {
            vk_repr: self.pk.pk().get_vk().transcript_repr(),
            state: self.state.clone(),
            acc: self.acc.clone(),
        }
    }
}
