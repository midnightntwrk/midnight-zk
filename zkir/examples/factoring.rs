//! Example of a ZKIR circuit proving knowledge of two non-trivial factors of a
//! 4096-bit integer.

use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_zk_stdlib::{self, MidnightCircuit};
use midnight_zkir::{IrValue, ZkirRelation};
use num_bigint::BigUint;
use num_traits::Num;
use rand_chacha::rand_core::OsRng;

fn big(hex_str: &str) -> IrValue {
    BigUint::from_str_radix(hex_str, 16).unwrap().into()
}

fn main() {
    let ir_raw = r#"{
        "version": { "major": 3, "minor": 0 },
        "instructions": [
            { "op": {"load": { "BigUint": 2048 }}, "outputs": ["P", "Q"] },
            { "op": "assert_not_equal", "inputs": ["P", "BigUint:1"] },
            { "op": "assert_not_equal", "inputs": ["Q", "BigUint:1"] },
            { "op": "mul", "inputs": ["P", "Q"], "outputs": ["N"] },
            { "op": "publish", "inputs": ["N"] }
        ]
    }
    "#;

    let relation = ZkirRelation::read(ir_raw).expect("valid IR");

    let k = MidnightCircuit::from_relation(&relation).min_k();
    let srs = ParamsKZG::unsafe_setup(k, OsRng);

    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let witness = HashMap::from_iter([
        ("P", big("27d49f2ca129e23d3bb048960745177f6f5ffab9b665bb092b65f5babc1a3dd0c558967fa8da9c0ad13a18a7324407a1034b5b8ff259efb8fb3cc8aaae4dd93c56a456bec700bb94a906a62a3e301f976dfb7223b64eaa4c0bcbcc33b4cbcc33201f7769cc54fd2aeca6c0e6f90b300a1e2640701cd5fb5b51a0edac461952ef72b933f554def94dddafce346868faad39bc13a6c18529badc737e63ee9e38d12dbad296affeed82f49717258bcb2dbc3aab9a1e9ea299918e1cc7415e81e19e16def56b7eee9c0a3300c9aab2625fe2bf112a5dee6a079401e1078261a3076c3a170b537b501c4e685226394b182e4a846fa53e861e10d0b632780f00c41657")),
        ("Q", big("a21f6263b9a790e8976533856e51c5b0556d2eac7df005dc833e8848387760dd4b7b023b6c1b9aa0d47b7babab919abf72d349041c46b148aa6e6fc7b576328787ad0ea41037d68c8ec08775389fea732f575749fb3da0ad2f4d4d82b65ce5bd2034695e78d7ba337d8deb1a692fa552e0366e4c3bb15f2f45a572b7b6b027b8f8b50522502a74484ca4441d13e5d096f499cc85d1baa2e1f62f67e6ec789280456c734c96d2912f3d4e1364726fc4ac2348ffdbdf81029329048f57ac5b2d79fcf174c56af3756ef4593f8aff1f275b6c17e9fc22ec986df61ba4ac57b12995c4ca772f1ed4f9f59231f64d7a819b3fe98ae46969274e287513065f7983b81b")),
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
