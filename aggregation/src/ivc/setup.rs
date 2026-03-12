//! IVC setup: circuit compilation and key generation.

use midnight_circuits::verifier::{fixed_bases, Accumulator};
use midnight_proofs::{
    plonk::ConstraintSystem,
    poly::{kzg::params::ParamsKZG, EvaluationDomain},
};
use midnight_zk_stdlib::ZkStdLib;

use super::{IvcCircuit, IvcIO, IvcProver, IvcTransition, IvcVerifier, E, S};

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
pub fn setup<T: IvcTransition + IvcIO>(
    params: ParamsKZG<E>,
    k: u32,
    ctx: T::Context,
) -> (IvcProver<T>, IvcVerifier) {
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, (IvcCircuit::<T>::arch(), (k - 1) as u8));
    let domain = EvaluationDomain::new(cs.degree() as u32, k);
    let relation = IvcCircuit::<T>::new(domain, cs, ctx.clone());

    // Uncomment for visualizing the size of this IVC circuit.
    // dbg!(midnight_zk_stdlib::cost_model(&relation, Some(k)));

    let vk = midnight_zk_stdlib::setup_vk(&params, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let fixed_base_names: Vec<String> =
        fixed_bases::<S>("self_vk", vk.vk()).keys().cloned().collect();

    let verifier = IvcVerifier {
        vk,
        params_verifier: params.verifier_params(),
    };

    let prover = IvcProver {
        params,
        relation,
        pk,
        state: T::genesis(&ctx),
        proof: vec![],
        acc: Accumulator::<S>::trivial(&fixed_base_names),
    };

    (prover, verifier)
}
