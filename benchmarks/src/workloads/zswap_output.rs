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

//! The `zswap_output` workload: the output circuit of the Zswap protocol,
//! which opens a coin commitment (SHA-256) and a value commitment (a Jubjub
//! MSM over a hash-to-curve base).
//!
//! For more details, visit:
//! <https://github.com/midnightntwrk/midnight-ledger-prototype/blob/main/zswap/zswap.compact>

use ff::Field;
use group::Group;
use midnight_circuits::{
    ecc::{hash_to_curve::HashToCurveGadget, native::EccChip},
    hash::poseidon::PoseidonChip,
    instructions::{
        AssignmentInstructions, ConversionInstructions, DecompositionInstructions, EccInstructions,
        HashToCurveCPU, PublicInputInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, AssignedNativePoint, Instantiable},
};
use midnight_curves::{Fr as JubjubScalar, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

use crate::workload::{RelationCase, Workload, relation_workload};

type F = midnight_curves::Fq;

type CoinCom = [u8; 32];
type ValueCom = JubjubSubgroup;

/// The domain separator of coin commitments.
const DOMAIN_SEP: &str = "mdn:cc";

/// The recipient of a coin.
#[derive(Clone, Copy, Debug)]
pub enum PK {
    /// The public key of a user.
    ZSwapCoinPublicKey([u8; 32]),
    /// The address of a contract.
    ContractAddress([u8; 32]),
}

/// A coin.
#[derive(Clone, Copy, Debug)]
pub struct CoinInfo {
    color: F,
    nonce: F,
    value: u64,
}

#[derive(Clone, Debug)]
struct AssignedPK {
    bytes: [AssignedByte<F>; 32],
    is_contract: AssignedBit<F>,
}

#[derive(Clone, Debug)]
struct AssignedCoinInfo {
    color_bytes: [AssignedByte<F>; 32],
    nonce_bytes: [AssignedByte<F>; 32],
    value_bytes: [AssignedByte<F>; 8],

    color: AssignedNative<F>,
    value: AssignedNative<F>,
}

/// Knowledge of a coin, its recipient and a randomness that open the public
/// coin and value commitments.
#[derive(Clone, Default)]
pub struct ZSwapOutputCircuit;

impl Relation for ZSwapOutputCircuit {
    type Instance = (CoinCom, ValueCom);

    type Witness = (PK, CoinInfo, JubjubScalar);

    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        let mut pi: Vec<F> =
            instance.0.iter().flat_map(AssignedByte::<F>::as_public_input).collect();
        pi.extend(AssignedNativePoint::<Jubjub>::as_public_input(&instance.1));
        Ok(pi)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let pk = assign_pk(std_lib, layouter, witness.as_ref().map(|w| w.0))?;
        let coin = assign_coin(std_lib, layouter, witness.as_ref().map(|w| w.1))?;
        let domain_sep = std_lib.assign_many_fixed(layouter, DOMAIN_SEP.as_bytes())?;

        let coin_com = {
            std_lib.sha2_256(
                layouter,
                &[
                    coin.color_bytes.to_vec(),
                    coin.nonce_bytes.to_vec(),
                    coin.value_bytes.to_vec(),
                    vec![pk.is_contract.into()],
                    pk.bytes.to_vec(),
                    domain_sep,
                ]
                .concat(),
            )?
        };

        let value_com = {
            let color_base = std_lib.hash_to_curve(layouter, &[coin.color])?;
            let generator = std_lib.jubjub().assign_fixed(layouter, JubjubSubgroup::generator())?;
            let rc = std_lib.jubjub().assign(layouter, witness.as_ref().map(|w| w.2))?;
            let coin_value_as_scalar = std_lib.jubjub().convert(layouter, &coin.value)?;
            std_lib.jubjub().msm(
                layouter,
                &[coin_value_as_scalar, rc],
                &[color_base, generator],
            )?
        };

        coin_com
            .iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))?;

        std_lib.jubjub().constrain_as_public_input(layouter, &value_com)
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ZSwapOutputCircuit)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: true,
            sha2_256: true,
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }
}

fn assign_pk(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    pk: Value<PK>,
) -> Result<AssignedPK, Error> {
    let (bytes_val, is_contract_val) = pk
        .map(|pk| match pk {
            PK::ZSwapCoinPublicKey(bytes) => (bytes, false),
            PK::ContractAddress(bytes) => (bytes, true),
        })
        .unzip();

    let bytes = std_lib.assign_many(layouter, &bytes_val.transpose_array())?;

    Ok(AssignedPK {
        bytes: bytes.try_into().unwrap(),
        is_contract: std_lib.assign(layouter, is_contract_val)?,
    })
}

fn assign_coin(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    coin: Value<CoinInfo>,
) -> Result<AssignedCoinInfo, Error> {
    let color = std_lib.assign(layouter, coin.map(|coin| coin.color))?;
    let nonce = std_lib.assign(layouter, coin.map(|coin| coin.nonce))?;
    let value = std_lib.assign(layouter, coin.map(|coin| F::from(coin.value)))?;

    let color_bytes = std_lib.assigned_to_le_bytes(layouter, &color, Some(32))?;
    let nonce_bytes = std_lib.assigned_to_le_bytes(layouter, &nonce, Some(32))?;
    let value_bytes = std_lib.assigned_to_le_bytes(layouter, &value, Some(8))?;

    Ok(AssignedCoinInfo {
        color_bytes: color_bytes.try_into().unwrap(),
        nonce_bytes: nonce_bytes.try_into().unwrap(),
        value_bytes: value_bytes.try_into().unwrap(),
        color,
        value,
    })
}

/// The output of a coin of value 1000 to a pseudo-random recipient.
fn build() -> RelationCase<ZSwapOutputCircuit> {
    let mut rng = ChaCha8Rng::seed_from_u64(0x25a9);

    let pk_bytes: [u8; 32] = core::array::from_fn(|_| rng.r#gen());
    let is_contract: bool = rng.r#gen();
    let pk = match is_contract {
        false => PK::ZSwapCoinPublicKey(pk_bytes),
        true => PK::ContractAddress(pk_bytes),
    };

    let coin = CoinInfo {
        color: F::from(42),
        nonce: F::random(&mut rng),
        value: 1000,
    };

    let coin_com: CoinCom = {
        let mut preimage = coin.color.to_bytes_le().to_vec();
        preimage.extend(coin.nonce.to_bytes_le());
        preimage.extend(coin.value.to_le_bytes());
        preimage.push(is_contract as u8);
        preimage.extend(pk_bytes);
        preimage.extend(DOMAIN_SEP.as_bytes());
        sha2::Sha256::digest(preimage).into()
    };

    let rc = JubjubScalar::random(&mut rng);
    let value_com = {
        let color_base = <HashToCurveGadget<
            F,
            Jubjub,
            AssignedNative<F>,
            PoseidonChip<F>,
            EccChip<Jubjub>,
        > as HashToCurveCPU<Jubjub, F>>::hash_to_curve(&[coin.color]);
        JubjubSubgroup::generator() * rc + color_base * JubjubScalar::from(coin.value)
    };

    RelationCase {
        relation: ZSwapOutputCircuit,
        instance: (coin_com, value_com),
        witness: (pk, coin, rc),
        k: None,
    }
}

/// The workloads defined in this module.
pub fn workloads() -> Vec<Box<dyn Workload>> {
    vec![relation_workload("zswap_output", build)]
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
    fn fflonk() {
        check(Pcs::FflonkT4);
        check(Pcs::FflonkT16);
    }
}
