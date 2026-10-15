//! Folding-IVC setup: circuit compilation, key generation and the dummy
//! witness parts of the steps that do not fold.

use ff::Field;
use group::Group;
use midnight_proofs::{
    plonk::{
        Error, VerifyingKey,
        protogalaxy::{Accumulator, folding_degree, read_instance},
    },
    poly::{
        PolynomialLabel,
        commitment::PolynomialCommitmentScheme,
        kzg::{
            commitment::{KZGCommitment, KZGMultiCommitment},
            params::ParamsKZG,
        },
    },
    transcript::Transcript,
};
use midnight_zk_stdlib::{DefaultPCS, MidnightPK};

use super::{
    FoldingIvcCircuit, FoldingIvcVerifier,
    circuit::NB_PUBLIC_INPUTS,
    types::{FoldingAccumulator, Tr},
};
use crate::ivc::{C, E, F, Ivc};

/// Keys and fixed data of a folding IVC. The [`super::FoldingIvcProver`]
/// borrows them.
#[derive(Debug)]
pub struct FoldingIvcKeys<T: Ivc> {
    pub(crate) params: ParamsKZG<E>,
    pub(crate) relation: FoldingIvcCircuit<T>,
    pub(crate) pk: MidnightPK<FoldingIvcCircuit<T>>,
    pub(crate) dummy: DummyStep,
}

impl<T: Ivc> FoldingIvcKeys<T> {
    /// The step circuit.
    pub fn relation(&self) -> &FoldingIvcCircuit<T> {
        &self.relation
    }
}

/// Well-formed placeholders for the witness parts a step does not use, so
/// that every step synthesises the same circuit: a partial proof whose
/// commitments are generator points (genesis step, no previous instance), all-zero folding
/// messages (genesis and first step, nothing to fold) and an accumulator
/// (the default accumulator has no native value).
#[derive(Clone, Debug)]
pub(crate) struct DummyStep {
    pub(crate) partial_proof: Vec<u8>,
    pub(crate) folding_proof: Vec<u8>,
    pub(crate) acc: FoldingAccumulator,
}

impl DummyStep {
    fn new<T: Ivc>(
        vk: &VerifyingKey<F, DefaultPCS>,
        relation: &FoldingIvcCircuit<T>,
    ) -> Result<Self, Error> {
        let mut transcript = Tr::init();
        for nb_points in relation.shape().nb_phase_points() {
            let point = KZGCommitment::Simple(C::generator(), PolynomialLabel::NoLabel);
            transcript.write(&KZGMultiCommitment::<E>(vec![point; nb_points]))?;
        }
        let partial_proof = transcript.finalize();

        let nb_scalars = relation.k() as usize + folding_degree(relation.cs()) - 1;
        let mut transcript = Tr::init();
        for _ in 0..nb_scalars {
            transcript.write(&F::ZERO)?;
        }
        let folding_proof = transcript.finalize();

        let pi = [F::ZERO; NB_PUBLIC_INPUTS];
        let mut transcript = Tr::init_from_bytes(&partial_proof);
        let fresh = read_instance(vk, &[&[], &pi], &mut transcript)?;
        transcript.assert_empty()?;
        let acc = Accumulator::init(vk, fresh, &mut Tr::init())?;

        Ok(DummyStep {
            partial_proof,
            folding_proof,
            acc,
        })
    }
}

/// Sets up a folding IVC for `2^k` rows: compiles the step circuit and
/// generates its keys. `params` must support `k` under [`DefaultPCS`].
///
/// Returns the keys (borrowed by a [`super::FoldingIvcProver`]) and the
/// verifier.
pub fn setup<T: Ivc>(
    params: ParamsKZG<E>,
    k: u32,
    ctx: T::Context,
) -> (FoldingIvcKeys<T>, FoldingIvcVerifier<T>) {
    let relation = FoldingIvcCircuit::<T>::new(k, ctx.clone());
    let vk = midnight_zk_stdlib::setup_vk(&params, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let dummy = DummyStep::new(vk.vk(), &relation).expect("dummy step should be well formed");

    let verifier = FoldingIvcVerifier {
        ctx,
        vk,
        params_verifier: DefaultPCS::get_verifier_params(&params),
    };
    let keys = FoldingIvcKeys {
        params,
        relation,
        pk,
        dummy,
    };
    (keys, verifier)
}
