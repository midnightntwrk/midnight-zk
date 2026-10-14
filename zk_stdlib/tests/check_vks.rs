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

//! Integration tests for identifying breaking changes in circuits

use midnight_zk_stdlib::{
    MidnightCircuit,
    utils::plonk_api::{check_vk, srs_for_test, update_circuit_goldenfiles},
};

#[path = "../examples/exposing_types.rs"]
mod exposing_types;

use exposing_types::{
    bitcoin_ecdsa_threshold::BitcoinThresholdECDSA,
    bitcoin_signature::BitcoinSigExample,
    ecc_ops::EccExample,
    ethereum_signature::EthereumSigExample,
    hybrid_mt::HybridMtExample,
    identity::jwt::{
        enrollment::CredentialEnrollment, full_credential::FullCredential,
        property_check::CredentialProperty,
    },
    membership::MembershipExample,
    native_gadget::NativeGadgetExample,
    poseidon::PoseidonExample,
    rsa_signature::RSASignatureCircuit,
    schnorr_sig::SchnorrExample,
    sha_preimage::ShaPreImageCircuit,
};

macro_rules! generate_tests {
    ($($name:ident: $circuit:ty => $has_committed_instance:expr),*) => {
        $(
            #[test]
            fn $name() {
                let relation = <$circuit>::default();

                update_circuit_goldenfiles(&relation, $has_committed_instance);

                let srs = srs_for_test(&relation, None);
                let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
                check_vk::<MidnightCircuit<$circuit>>(&vk);
            }
        )*
    };
}

generate_tests!(
    check_vk_ecc: EccExample => false,
    check_vk_bitcoin: BitcoinThresholdECDSA => false,
    check_vk_ethereum_sig: EthereumSigExample => false,
    check_vk_bitcoin_sig: BitcoinSigExample => false,
    check_vk_rsa: RSASignatureCircuit => false,
    check_vk_poseidon: PoseidonExample => false,
    check_vk_native: NativeGadgetExample => false,
    check_vk_membership: MembershipExample => false,
    check_vk_cred_full: FullCredential => false,
    check_vk_cred_enrollment: CredentialEnrollment => true,
    check_vk_cred_property: CredentialProperty => true,
    check_vk_hybrid_mt: HybridMtExample => false,
    check_vk_sha: ShaPreImageCircuit => false,
    check_vk_schnorr: SchnorrExample => false
);
