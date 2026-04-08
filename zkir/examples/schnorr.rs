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

//! Example of a ZKIR circuit proving knowledge of a Schnorr signature (over
//! Jubjub and with Poseidon hash) on a public message.

use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use ff::Field;
use group::Group;
use midnight_circuits::{hash::poseidon::PoseidonChip, instructions::hash::HashCPU};
use midnight_curves::{Fr as JubjubScalar, JubjubAffine, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_zkir::ZkirRelation;
use rand_chacha::{
    rand_core::{OsRng, RngCore, SeedableRng},
    ChaCha8Rng,
};

type F = midnight_curves::Fq;

#[derive(Clone, Default)]
pub struct SchnorrSignature {
    s: JubjubScalar,
    e_bytes: [u8; 32],
}

type SchnorrPK = JubjubSubgroup;
type SchnorrSK = JubjubScalar;
type Message = F;

fn main() {
    let ir_raw = r#"{
        "version": { "major": 3, "minor": 0 },
        "instructions": [
            { "op": {"load" : "Native"}, "outputs": ["msg"] },
            { "op": "publish", "inputs": ["msg"] },
            { "op": {"load" : "JubjubPoint"},  "outputs": ["PK"] },
            { "op": {"load" : "JubjubScalar"}, "outputs": ["s"] },
            { "op": {"load" : { "Bytes": 32 }}, "outputs": ["e_bytes"] },
            { "op": {"from_bytes" : "JubjubScalar"}, "inputs": ["e_bytes"], "outputs": ["e"] },
            { "op": "inner_product", "inputs": ["e", "s", "PK", "Jubjub:GENERATOR"], "outputs": ["R"] },
            { "op": "affine_coordinates", "inputs": ["PK"], "outputs": ["PKx", "PKy"] },
            { "op": "affine_coordinates", "inputs": ["R"], "outputs": ["Rx", "Ry"] },
            { "op": "poseidon", "inputs": ["PKx", "PKy", "Rx", "Ry", "msg"], "outputs": ["h"] },
            { "op": {"into_bytes" : 32}, "inputs": ["h"], "outputs": ["h_bytes"] },
            { "op": "assert_equal", "inputs": ["e_bytes", "h_bytes"] }
        ]
    }
    "#;

    let relation = ZkirRelation::read(ir_raw).expect("valid IR");

    let k = midnight_zk_stdlib::optimal_k(&relation);
    dbg!(midnight_zk_stdlib::cost_model(&relation, Some(k)));

    let mut rng = ChaCha8Rng::seed_from_u64(0xf001ba11);

    let (pk, sk) = keygen(&mut rng);
    let msg = F::random(&mut rng);
    let sig = sign(msg, &sk, &mut rng);

    let witness = HashMap::from_iter([
        ("PK", pk.into()),
        ("msg", msg.into()),
        ("s", sig.s.into()),
        ("e_bytes", sig.e_bytes.to_vec().into()),
    ]);
    let instance = relation.public_inputs(witness.clone()).expect("off-circuit run failed");

    let srs = ParamsKZG::unsafe_setup(k, OsRng);

    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let proof =
        midnight_zk_stdlib::prove::<_, Blake2b>(&srs, &pk, &relation, &instance, witness, OsRng)
            .expect("Proof generation should not fail");

    assert!(midnight_zk_stdlib::verify::<ZkirRelation, Blake2b>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof
    )
    .is_ok())
}

fn keygen(mut rng: impl RngCore) -> (SchnorrPK, SchnorrSK) {
    let sk = JubjubScalar::random(&mut rng);
    let pk = JubjubSubgroup::generator() * sk;
    (pk, sk)
}

fn sign(message: Message, secret_key: &SchnorrSK, mut rng: impl RngCore) -> SchnorrSignature {
    let k = JubjubScalar::random(&mut rng);
    let r = JubjubSubgroup::generator() * k;

    let (rx, ry) = get_coords(&r);
    let (pkx, pky) = get_coords(&(JubjubSubgroup::generator() * secret_key));

    let h = PoseidonChip::hash(&[pkx, pky, rx, ry, message]);
    let e_bytes = h.to_bytes_le();

    let s = {
        let mut buff = [0u8; 64];
        buff[..32].copy_from_slice(&e_bytes);
        let e = JubjubScalar::from_bytes_wide(&buff);
        k - e * secret_key
    };

    SchnorrSignature { s, e_bytes }
}

// Returns the affine coordinates of a given Jubjub point.
fn get_coords(point: &JubjubSubgroup) -> (F, F) {
    let point: &Jubjub = point.into();
    let point: JubjubAffine = point.into();
    (point.get_u(), point.get_v())
}
