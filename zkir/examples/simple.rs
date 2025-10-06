use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use midnight_circuits::compact_std_lib::{self, MidnightCircuit};
use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_zkir::ZkirRelation;
use num_bigint::BigUint;
use rand_chacha::rand_core::OsRng;

type F = midnight_curves::Fq;

fn main() {
    let ir_raw = r#"{
        "version": { "major": 3, "minor": 0 },
        "instructions": [
            { "op": {"load": "Native"}, "outputs": ["v0", "v1"] },
            { "op": {"load": "Bool"}, "outputs": ["b0"] },
            { "op": {"load": { "Bytes" : 2 }}, "outputs": ["bytes"] },
            { "op": {"load": { "BigUint": 1024 }}, "outputs": ["N"] },
            { "op": "publish", "inputs": ["v0", "v1", "N"] }
        ]
    }
    "#;

    let relation = ZkirRelation::read(ir_raw).expect("valid IR");

    let k = MidnightCircuit::from_relation(&relation).min_k();
    let srs = ParamsKZG::unsafe_setup(k, OsRng);

    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let witness = HashMap::from_iter([
        ("v0", F::from(1).into()),
        ("v1", (-F::from(2)).into()),
        ("b0", true.into()),
        ("bytes", vec![0xFFu8, 0x07u8].into()),
        ("N", BigUint::from(123u64).into()),
    ]);

    let instance = relation.public_inputs(witness.clone()).expect("off-circuit run failed");

    let proof =
        compact_std_lib::prove::<_, Blake2b>(&srs, &pk, &relation, &instance, witness, OsRng)
            .expect("Proof generation should not fail");

    assert!(compact_std_lib::verify::<ZkirRelation, Blake2b>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof
    )
    .is_ok())
}
