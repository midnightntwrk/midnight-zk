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

//! The `ecdsa` workload: knowledge of an Ethereum signature (ECDSA over
//! secp256k1 of a Keccak-256 digest) of a public message under a public key.

use group::GroupEncoding;
use midnight_circuits::{
    CircuitField,
    field::foreign::params::MultiEmulationParams,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
    },
    types::{AssignedByte, AssignedForeignPoint, Instantiable},
};
use midnight_curves::k256::{Fq as K256Scalar, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};

use crate::workload::{RelationCase, Workload, relation_workload};

type F = midnight_curves::Fq;

const MSG_LEN: usize = 32;
type Message = [u8; MSG_LEN];
type PK = K256;

type Signature = (K256Scalar, K256Scalar);

/// The prefix of the Keccak preimage in Ethereum signatures of 32-byte
/// messages (EIP-191).
const PREFIX: &[u8] = b"\x19Ethereum Signed Message:\n32";

/// Knowledge of an Ethereum signature of a public message under a public key.
#[derive(Clone, Default)]
pub struct EthereumSigExample;

impl Relation for EthereumSigExample {
    type Instance = (PK, Message);

    type Witness = Signature;

    type Error = Error;

    fn format_instance((pk, msg_bytes): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            AssignedForeignPoint::<F, K256, MultiEmulationParams>::as_public_input(pk),
            msg_bytes
                .iter()
                .flat_map(AssignedByte::<F>::as_public_input)
                .collect::<Vec<_>>(),
        ]
        .into_iter()
        .flatten()
        .collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1();
        let secp256k1_scalar = secp256k1_curve.scalar_field_chip();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        let pk = secp256k1_curve.assign(layouter, instance.map(|(pk, _)| pk))?;
        secp256k1_curve.constrain_as_public_input(layouter, &pk)?;

        let msg_bytes = std_lib.assign_many(
            layouter,
            &instance.map(|(_, msg_bytes)| msg_bytes).transpose_array(),
        )?;
        msg_bytes
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))?;

        let (r_val, s_val) = witness.unzip();
        let r = secp256k1_scalar.assign(layouter, r_val)?;
        let s = secp256k1_scalar.assign(layouter, s_val)?;

        let keccak_input = (std_lib.assign_many_fixed(layouter, PREFIX)?.into_iter())
            .chain(msg_bytes)
            .collect::<Vec<_>>();

        let keccak_output = std_lib.keccak_256(layouter, &keccak_input)?;

        let keccak_output_bits = (keccak_output.into_iter())
            .map(|byte| std_lib.assigned_to_be_bits(layouter, &byte.into(), Some(8), true))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let z = secp256k1_scalar.assigned_from_be_bits(layouter, &keccak_output_bits)?;
        let s_inv = secp256k1_scalar.inv(layouter, &s)?;
        let u1 = secp256k1_scalar.mul(layouter, &z, &s_inv, None)?;
        let u2 = secp256k1_scalar.mul(layouter, &r, &s_inv, None)?;

        let generator = secp256k1_curve.assign_fixed(layouter, K256::generator())?;
        let u1_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &u1, None, true)?;
        let u2_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &u2, None, true)?;

        // R = u1 * G + u2 * pk, for u1 = z * s^{-1} and u2 = r * s^{-1}.
        let r_point =
            secp256k1_curve.msm_by_le_bits(layouter, &[u1_bits, u2_bits], &[generator, pk])?;

        // `x` also asserts that R is not the identity.
        let r_point_x = secp256k1_curve.x(layouter, &r_point)?;
        let r_point_x_bits = secp256k1_base.assigned_to_le_bytes(layouter, &r_point_x, None)?;
        let r_point_x_scalar =
            secp256k1_scalar.assigned_from_le_bytes(layouter, &r_point_x_bits)?;
        secp256k1_scalar.assert_equal(layouter, &r_point_x_scalar, &r)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            keccak_256: true,
            secp256k1: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(EthereumSigExample)
    }
}

/// Decodes 32 bytes written in hexadecimal.
fn hex32(hex: &str) -> [u8; 32] {
    assert_eq!(hex.len(), 64);
    core::array::from_fn(|i| {
        u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("hexadecimal digits")
    })
}

/// The point with the given big-endian affine coordinates.
fn parse_eth_point(x: &[u8; 32], y: &[u8; 32]) -> K256 {
    // SEC1 compressed encoding: 0x02 (even y) or 0x03 (odd y), then x.
    let mut sec1_compressed = [0u8; 33];
    sec1_compressed[0] = 0x02 + y[31] % 2;
    sec1_compressed[1..].copy_from_slice(x);
    K256::from_bytes(&sec1_compressed.into()).expect("a point of secp256k1")
}

/// A signature produced by ethers.js: `wallet.signMessage(message)` for the
/// private key `0x0123456789abcdef` repeated four times.
fn build() -> RelationCase<EthereumSigExample> {
    let msg_bytes: Message = *b"this is really 32 byte long, huh";

    let pk = parse_eth_point(
        &hex32("4646ae5047316b4230d0086c8acec687f00b1cd9d1dc634f6cb358ac0a9a8fff"),
        &hex32("fe77b4dd0a4bfb95851f3b7355c781dd60f8418fc8a65d14907aff47c903a559"),
    );

    let scalar = |hex| K256Scalar::from_bytes_be(&hex32(hex)).expect("a scalar of secp256k1");
    let r = scalar("3c0fb2cfab098941e41e180c5e83bd270f1d52811a517dbee235219f35935717");
    let s = scalar("1ce5858264bbdf0afe617da1dc8f3fa94a350e40442eb0363c3c95be9cd0d6d8");

    RelationCase {
        relation: EthereumSigExample,
        instance: (pk, msg_bytes),
        witness: (r, s),
        k: None,
    }
}

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![relation_workload("ecdsa", build)]
}

#[cfg(test)]
mod tests {
    use crate::workload::Pcs;

    /// Proves and verifies every workload under `pcs`, and checks that
    /// building it again gives the same circuit.
    fn check(pcs: Pcs) {
        for workload in super::workloads() {
            let name = workload.name();
            assert!(
                workload.supported_pcs().contains(&pcs),
                "{name} under {pcs}"
            );
            let mut prepared = workload.setup(pcs);
            let proof = prepared.prove();
            assert!(prepared.verify(&proof), "{name} under {pcs}");
            assert_eq!(
                prepared.vk_hash(),
                workload.setup(pcs).vk_hash(),
                "{name} under {pcs}"
            );
        }
    }

    #[test]
    fn kzg() {
        check(Pcs::Kzg);
    }

    #[test]
    #[ignore = "takes over a minute"]
    fn fflonk() {
        check(Pcs::FflonkT4);
        check(Pcs::FflonkT16);
    }
}
