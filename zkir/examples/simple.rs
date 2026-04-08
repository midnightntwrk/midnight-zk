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

use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_zkir::{IrValue, ZkirRelation};
use num_bigint::BigUint;
use num_traits::Num;
use rand_chacha::rand_core::OsRng;

type F = midnight_curves::Fq;

fn big(hex_str: &str) -> IrValue {
    BigUint::from_str_radix(hex_str, 16).unwrap().into()
}

fn main() {
    let ir_raw = r#"{
        "version": { "major": 3, "minor": 0 },
        "instructions": [
            { "op": {"load": "Native"}, "outputs": ["v0", "v1"] },
            { "op": {"load": "Bool"}, "outputs": ["b0"] },
            { "op": {"load": { "Bytes" : 2 }}, "outputs": ["bytes"] },
            { "op": {"load": { "BigUint": 512 }}, "outputs": ["P", "Q"] },
            { "op": "mul", "inputs": ["P", "Q"], "outputs": ["N"] },
            { "op": "publish", "inputs": ["v0", "v1", "N"] },
            { "op": "add", "inputs": ["v0", "v1"], "outputs": ["z"] },
            { "op": "assert_equal", "inputs": ["z", "Native:-0x01"] }
        ]
    }
    "#;

    let relation = ZkirRelation::read(ir_raw).expect("valid IR");

    let k = midnight_zk_stdlib::optimal_k(&relation);
    let srs = ParamsKZG::unsafe_setup(k, OsRng);

    dbg!(midnight_zk_stdlib::cost_model(&relation, Some(k)));

    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let witness = HashMap::from_iter([
        ("v0", F::from(1).into()),
        ("v1", (-F::from(2)).into()),
        ("b0", true.into()),
        ("bytes", vec![0xFFu8, 0x07u8].into()),
        ("P", big("d7d37ec5b4a35a04bd70d75e51f600d4cf145f8e9a8264b25b37bfba86583239ddfe9d33e20203dc6100d4922d94743555498af36b0edbe8dd7fb27497d56e41")),
        ("Q", big("4f400915ae68616df701651914fc5797c60ac628b82585b18cc93346fcde1c700bac0d35d6f4a99e7fdfd2c1bdb3bb50359317bda2b932f8aafd5865d9a1ca1")),
    ]);

    let instance = relation.public_inputs(witness.clone()).expect("off-circuit run failed");

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
