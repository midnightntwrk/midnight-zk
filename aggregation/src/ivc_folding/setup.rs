//! Folding-IVC setup: circuit compilation, key generation and the dummy
//! witness parts of the steps that do not fold.

use ff::Field;
use group::Group;
use midnight_proofs::{
    plonk::{
        Error, ProvingKey, VerifyingKey, keygen_pk, keygen_vk_with_k,
        protogalaxy::{Accumulator, FoldingInstance, folding_degree, read_instance},
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
use midnight_zk_stdlib::MidnightCircuit;

use super::{
    FoldingIvcCircuit, FoldingIvcVerifier, FoldingPCS,
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
    pub(crate) pk: ProvingKey<F, FoldingPCS>,
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
/// commitments are generator points (genesis step, no previous instance),
/// all-zero folding messages (genesis and first step, nothing to fold) and an
/// accumulator (the default accumulator has no native value).
#[derive(Clone, Debug)]
pub(crate) struct DummyStep {
    pub(crate) partial_proof: Vec<u8>,
    pub(crate) folding_proof: Vec<u8>,
    pub(crate) acc: FoldingAccumulator,
}

impl DummyStep {
    fn new<T: Ivc>(
        vk: &VerifyingKey<F, FoldingPCS>,
        relation: &FoldingIvcCircuit<T>,
    ) -> Result<Self, Error> {
        let (partial_proof, fresh) = dummy_partial_proof(vk, relation.shape().nb_phase_points())?;

        let nb_scalars = relation.k() as usize + folding_degree(relation.cs()) - 1;
        let mut transcript = Tr::init();
        for _ in 0..nb_scalars {
            transcript.write(&F::ZERO)?;
        }
        let folding_proof = transcript.finalize();

        let acc = Accumulator::init(vk, fresh, &mut Tr::init())?;

        Ok(DummyStep {
            partial_proof,
            folding_proof,
            acc,
        })
    }
}

/// A partial proof whose phase-1 and phase-2 commitments are generator
/// points (`nb_phase_points` of each), and the instance read from it for
/// all-zero public inputs.
fn dummy_partial_proof(
    vk: &VerifyingKey<F, FoldingPCS>,
    nb_phase_points: [usize; 2],
) -> Result<(Vec<u8>, FoldingInstance<F, FoldingPCS>), Error> {
    let pi = [F::ZERO; NB_PUBLIC_INPUTS];
    let point = KZGCommitment::Simple(C::generator(), PolynomialLabel::NoLabel);
    let mut transcript = Tr::init();
    for nb in nb_phase_points {
        let commitment = KZGMultiCommitment::<E>(vec![point.clone(); nb]);
        transcript.write(&commitment).map_err(|_| Error::InvalidInstances)?;
    }
    let proof = transcript.finalize();

    let mut transcript = Tr::init_from_bytes(&proof);
    let fresh = read_instance(vk, &[&[], &pi], &mut transcript)?;
    transcript.assert_empty().map_err(|_| Error::InvalidInstances)?;
    Ok((proof, fresh))
}

/// Sets up a folding IVC for `2^k` rows: compiles the step circuit and
/// generates its keys. `params` must support `k` under [`FoldingPCS`].
///
/// Returns the keys (borrowed by a [`super::FoldingIvcProver`]) and the
/// verifier.
pub fn setup<T: Ivc>(
    params: ParamsKZG<E>,
    k: u32,
    ctx: T::Context,
) -> (FoldingIvcKeys<T>, FoldingIvcVerifier<T>) {
    let relation = FoldingIvcCircuit::<T>::new(k, ctx.clone());
    let circuit = MidnightCircuit::from_relation(&relation, Some(k));
    let vk = keygen_vk_with_k::<_, FoldingPCS, _>(&params, &circuit, k)
        .expect("keygen_vk should not fail");
    let pk = keygen_pk(vk, &circuit).expect("keygen_pk should not fail");
    let dummy = DummyStep::new(pk.get_vk(), &relation).expect("dummy step should be well formed");

    let verifier = FoldingIvcVerifier {
        ctx,
        vk: pk.get_vk().clone(),
        params_verifier: FoldingPCS::get_verifier_params(&params),
    };
    let keys = FoldingIvcKeys {
        params,
        relation,
        pk,
        dummy,
    };
    (keys, verifier)
}
