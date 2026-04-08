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

//! IVC setup: circuit compilation and key generation.

use midnight_circuits::verifier::{fixed_bases, Accumulator};
use midnight_proofs::{
    plonk::ConstraintSystem,
    poly::{kzg::params::ParamsKZG, EvaluationDomain},
};
use midnight_zk_stdlib::ZkStdLib;

use super::{Ivc, IvcCircuit, IvcProver, IvcVerifier, E, S};

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
pub fn setup<T: Ivc>(
    params: ParamsKZG<E>,
    k: u32,
    ctx: T::Context,
) -> (IvcProver<T>, IvcVerifier<T>) {
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
        ctx: ctx.clone(),
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
