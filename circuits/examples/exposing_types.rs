#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(unused_imports)]
//! Module file, to expose all example circuits to benchmarks to check
//! circuit cost model.

pub mod bitcoin_ecdsa_threshold;
pub mod bitcoin_signature;
pub mod ecc_ops;
pub mod hybrid_mt;
pub mod json_verification;
pub mod membership;
pub mod native_gadget;
pub mod poseidon;
pub mod rsa_signature;
pub mod sha_preimage;

// We are doing a bit of a hack to be able to reuse the circuits that are
// defined in the examples folder. To keep clippy happy, we need to define a
// main function at this level.
fn main() {
    ()
}
