//! Integration tests for identifying breaking changes in circuits

use midnight_proofs::plonk::k_from_circuit;
use midnight_circuits::{
    compact_std_lib,
    compact_std_lib::MidnightCircuit,
    testing_utils::plonk_api::{check_vk, filecoin_srs},
};

#[path = "../examples/exposing_types.rs"]
mod exposing_types;

use exposing_types::{
    bitcoin_ecdsa_threshold::BitcoinThresholdECDSA, ecc_ops::EccExample,
    hybrid_mt::HybridMtExample, json_verification::AtalaJsonECDSA, membership::MembershipExample,
    native_gadget::NativeGadgetExample, poseidon::PoseidonExample,
    rsa_signature::RSASignatureCircuit, sha_preimage::ShaPreImageCircuit,
    zswap_output::ZSwapOutputCircuit,
};

macro_rules! generate_tests {
    ($($name:ident: $circuit:ty),*) => {
        $(
            #[test]
            fn $name() {
                let relation = <$circuit>::default();
                let circuit = MidnightCircuit::from_relation(&relation);
                let k = k_from_circuit(&circuit);
                let srs = filecoin_srs(k);


                let vk = compact_std_lib::setup_vk(&srs, &relation);

                check_vk::<MidnightCircuit<$circuit>>(&vk);
            }
        )*
    };
}

generate_tests!(
    check_vk_ecc: EccExample,
    check_vk_bitcoin: BitcoinThresholdECDSA,
    check_vk_rsa: RSASignatureCircuit,
    check_vk_poseidon: PoseidonExample,
    check_vk_native: NativeGadgetExample,
    check_vk_membership: MembershipExample,
    check_vk_atala: AtalaJsonECDSA,
    check_vk_hybrid_mt: HybridMtExample,
    check_vk_sha: ShaPreImageCircuit,
    check_vk_zswap: ZSwapOutputCircuit
);
