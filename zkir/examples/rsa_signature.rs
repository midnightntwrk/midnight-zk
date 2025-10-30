//! Example of a ZKIR circuit for proving knowledge of an RSA signature on a
//! public message.

use std::collections::HashMap;

use blake2b_simd::State as Blake2b;
use midnight_circuits::compact_std_lib::{self, MidnightCircuit};
use midnight_proofs::poly::kzg::params::ParamsKZG;
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
            { "op": {"load": { "BigUint": 2048 }}, "outputs": ["N"] },
            { "op": {"load": { "Bytes": 4 }}, "outputs": ["msg"] },
            { "op": "publish", "inputs": ["N", "msg"] },
            { "op": {"load": { "BigUint": 2048 }}, "outputs": ["sig"] },
            { "op": "sha256", "inputs": ["msg"], "outputs": ["msg_hash"] },
            { "op": {"mod_exp": 65537}, "inputs": ["sig", "N"], "outputs": ["h"] },
            { "op": {"into_bytes" : 32}, "inputs": ["h"], "outputs": ["h_bytes"] },
            { "op": "assert_equal", "inputs": ["h_bytes", "msg_hash"] }
        ]
    }
    "#;

    let relation = ZkirRelation::read(ir_raw).expect("valid IR");

    dbg!(compact_std_lib::cost_model(&relation));

    let k = MidnightCircuit::from_relation(&relation).min_k();
    let srs = ParamsKZG::unsafe_setup(k, OsRng);

    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let witness = HashMap::from_iter([
        ("N", big("61472e8be1e6b3cd6919b0266abedc9bfedb0103682c6e728ccb9c4a043221e7e8f2c286bddb309576187e29856932fbdd926e469f4fe8691d7ca56e7c4d78c95323f08d174905db64ef0f766dd6de98310eec07045a94343475e78a9bd55c2d8ce1c54b23263750ecbd69e011f126a918522b6612ef6b30803b52d94b27dff030ef31325e89b2c0c1cd301ffacb2412ceddf03e574fb6b0b92851c0f60b3b466550df9ebc3760e5618c0ae04989f6b6706029a05838f9baefe51a28062bc5ac72afcff415ad055e888048f5082306db4a8885a1cc19a0950d2b88e85ff948b2ba86cbcc94f4a3412b64ed8180202ad82745132a8f3d38f4045bb4ac8d7d275")),
        ("msg", vec![0xde, 0xad, 0xbe, 0xef].into()),
        ("sig", big("4b73c2f2087ea72fa18b64029bf43dfd274a17c0df3617088d61c99f7a7062e64f1a42d07aca11b800ffd42cd59c55242785a1ee9c82fdb55218ea0a97e75ed0d64948989bc65a81b3385d98b2304ef716c8e2aecb8cd8cde7ee3c1647bffa337b328600493906bf6e268adf854201eb156386c2ba89e73a399609bc3231c2e3ec42fb53ae8faf0583b08004828179910967c5a27b068c1e2ad31f7de5800c4987904b79ac8111f1d819f0fd1648a600db4c26c226b22356b852067026de70e007c93083593fa70eca8cf69f1cd91e484df6ed87de1d53f98ff0548103b065e5ccf1fd67b0c8c952b9b3aa2f87b7844ffac34d3632e6960710064bc8c959c25"))
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
