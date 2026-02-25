//! IVC setup: circuit compilation and key generation.

use midnight_circuits::verifier::fixed_bases;
use midnight_proofs::{
    plonk::ConstraintSystem,
    poly::{kzg::params::ParamsKZG, EvaluationDomain},
};
use midnight_zk_stdlib::ZkStdLib;

use super::{prover, IvcCircuit, IvcProver, IvcTransition, IvcVerifier, E, S};

/// Sets up the IVC context: compiles the circuit, generates keys,
/// and initializes the prover at the genesis state.
///
/// `k` is the circuit size parameter (log2 of the number of rows),
/// which needs to be provided manually.
///
/// Returns the stateful prover (set at genesis) and a lightweight
/// [`IvcVerifier`].
///
/// The returned [`IvcVerifier`] holds the self-verifying key. A verifier only
/// needs to run this function once; the resulting [`IvcVerifier`] can then be
/// reused to check any [`super::IvcInstance`].
pub fn setup<T: IvcTransition>(params: ParamsKZG<E>, k: u32) -> (IvcProver<T>, IvcVerifier) {
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, IvcCircuit::<T>::arch());
    let domain = EvaluationDomain::new(cs.degree() as u32, k);
    let relation = IvcCircuit::<T>::new(domain, cs);

    // Uncomment for visualizing the size of this IVC circuit.
    // dbg!(midnight_zk_stdlib::cost_model_with_k(&relation, k));

    let vk = midnight_zk_stdlib::setup_vk_with_k(&params, &relation, k);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let fixed_base_names: Vec<String> =
        fixed_bases::<S>("self_vk", vk.vk()).keys().cloned().collect();

    let verifier = IvcVerifier {
        vk,
        s_g2: params.s_g2().into(),
    };

    let prover = IvcProver {
        params,
        relation,
        pk,
        state: T::genesis(),
        proof: vec![],
        acc: prover::trivial_acc(&fixed_base_names),
    };

    (prover, verifier)
}
