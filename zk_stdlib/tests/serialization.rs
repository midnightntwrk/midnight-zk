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

//! Unit tests on serialization of Midnight keys.

use midnight_circuits::instructions::{
    ArithInstructions, AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{
    MidnightPK, MidnightVK, Relation, ZkStdLib, ZkStdLibArch, utils::plonk_api::srs_for_test,
};
use serial_test::serial;

type F = midnight_curves::Fq;

#[derive(Clone)]
struct DummyCircuit {
    architecture: ZkStdLibArch,
}

impl Relation for DummyCircuit {
    type Instance = F;

    type Witness = F;

    type Error = Error;

    fn format_instance(x: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*x])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let instance = std_lib.assign_as_public_input(layouter, instance)?;
        let witness = std_lib.assign(layouter, witness)?;

        let x = std_lib.mul(layouter, &witness, &witness, None)?;
        std_lib.assert_equal(layouter, &instance, &x)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        self.architecture
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        self.architecture.write(writer)
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        ZkStdLibArch::read(reader).map(|architecture| DummyCircuit { architecture })
    }
}

// Some different architectures to be tested.
const ARCHITECTURES: [ZkStdLibArch; 5] = [
    ZkStdLibArch {
        jubjub: true,
        poseidon: true,
        sha2_256: false,
        sha2_512: false,
        sha3_256: false,
        keccak_256: false,
        blake2b: false,
        secp256k1: true,
        p256: false,
        bls12_381: true,
        curve25519: true,
        base64: false,
        automaton: false,
        nb_arith_cols: 5,
        nr_pow2range_cols: 4,
        lookup_chunk_bound: None,
    },
    ZkStdLibArch {
        jubjub: true,
        poseidon: true,
        sha2_256: true,
        sha2_512: false,
        sha3_256: false,
        keccak_256: false,
        blake2b: false,
        secp256k1: false,
        p256: false,
        bls12_381: false,
        curve25519: false,
        base64: false,
        automaton: false,
        nb_arith_cols: 5,
        nr_pow2range_cols: 4,
        lookup_chunk_bound: None,
    },
    ZkStdLibArch {
        jubjub: false,
        poseidon: true,
        sha2_256: true,
        sha2_512: false,
        sha3_256: false,
        keccak_256: false,
        blake2b: false,
        secp256k1: false,
        p256: false,
        bls12_381: true,
        curve25519: true,
        base64: false,
        automaton: false,
        nb_arith_cols: 5,
        nr_pow2range_cols: 4,
        lookup_chunk_bound: None,
    },
    ZkStdLibArch {
        jubjub: false,
        poseidon: false,
        sha2_256: true,
        sha2_512: false,
        sha3_256: false,
        keccak_256: false,
        blake2b: false,
        secp256k1: true,
        p256: false,
        bls12_381: false,
        curve25519: true,
        base64: true,
        automaton: false,
        nb_arith_cols: 5,
        nr_pow2range_cols: 4,
        lookup_chunk_bound: None,
    },
    ZkStdLibArch {
        jubjub: true,
        poseidon: true,
        sha2_256: false,
        sha2_512: false,
        sha3_256: false,
        keccak_256: false,
        blake2b: false,
        secp256k1: false,
        p256: false,
        bls12_381: false,
        curve25519: false,
        base64: false,
        automaton: false,
        nb_arith_cols: 5,
        nr_pow2range_cols: 4,
        lookup_chunk_bound: Some(3),
    },
];

#[test]
fn arch_with_lookup_chunk_bound_roundtrips() {
    let arch = ZkStdLibArch { lookup_chunk_bound: Some(3), ..ZkStdLibArch::default() };
    let mut buffer = Vec::new();
    arch.write(&mut buffer).unwrap();
    assert_eq!(ZkStdLibArch::read(&mut buffer.as_slice()).unwrap(), arch);
}

/// A `ZKSTD_VERSION` 2 architecture (no `lookup_chunk_bound`) decodes with
/// `None`. The bytes are the version and the bincode fields of the V2 layout:
/// thirteen flags, then `nb_arith_cols` and `nr_pow2range_cols`.
#[test]
fn v2_arch_decodes_without_lookup_chunk_bound() {
    let mut bytes = 2u32.to_le_bytes().to_vec();
    // jubjub and poseidon enabled, the other eleven flags disabled.
    bytes.extend([1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    bytes.extend([7, 4]);
    let arch = ZkStdLibArch::read(&mut bytes.as_slice()).unwrap();
    let expected = ZkStdLibArch {
        jubjub: true,
        poseidon: true,
        nb_arith_cols: 7,
        nr_pow2range_cols: 4,
        ..ZkStdLibArch::default()
    };
    assert_eq!(arch, expected);
    assert_eq!(arch.lookup_chunk_bound, None);
}

fn vk_serde_test(architecture: ZkStdLibArch, write_format: SerdeFormat, read_format: SerdeFormat) {
    let relation = DummyCircuit { architecture };
    let srs = srs_for_test(&relation, None);
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);

    let mut buffer = Vec::new();
    vk.write(&mut buffer, write_format).unwrap();

    println!("VK buffer length after write: {}", buffer.len());
    println!("usize length: {:?}", std::mem::size_of::<usize>());

    let mut cursor = std::io::Cursor::new(buffer.clone());
    let serialised_architecture =
        ZkStdLibArch::read_from_serialized_vk(&mut cursor.clone()).unwrap();

    let vk2 = MidnightVK::read(&mut cursor, read_format).unwrap();

    let mut buffer2 = Vec::new();
    vk2.write(&mut buffer2, write_format).unwrap();

    assert_eq!(serialised_architecture, architecture);
    assert_eq!(buffer, buffer2);
}

#[test]
#[serial]
fn vk_write_then_read_processed() {
    for arch in ARCHITECTURES {
        vk_serde_test(arch, SerdeFormat::Processed, SerdeFormat::Processed);
    }
}

#[test]
#[serial]
fn vk_write_then_read_raw() {
    for arch in ARCHITECTURES {
        vk_serde_test(arch, SerdeFormat::RawBytes, SerdeFormat::RawBytes);
        vk_serde_test(arch, SerdeFormat::RawBytes, SerdeFormat::RawBytesUnchecked);
    }
}

#[test]
#[should_panic]
fn vk_write_processed_then_read_raw() {
    vk_serde_test(
        ZkStdLibArch::default(),
        SerdeFormat::Processed,
        SerdeFormat::RawBytes,
    );
}

#[test]
#[should_panic]
fn vk_write_raw_then_read_processed() {
    vk_serde_test(
        ZkStdLibArch::default(),
        SerdeFormat::RawBytes,
        SerdeFormat::Processed,
    );
}

fn pk_serde_test(architecture: ZkStdLibArch, write_format: SerdeFormat, read_format: SerdeFormat) {
    let relation = DummyCircuit { architecture };
    let srs = srs_for_test(&relation, None);
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let mut buffer = Vec::new();
    pk.write(&mut buffer, write_format).unwrap();

    println!("Size of usize: {:?}", std::mem::size_of::<usize>());
    println!("PK buffer length after write: {}", buffer.len());

    let mut cursor = std::io::Cursor::new(buffer.clone());
    let pk2 = MidnightPK::<DummyCircuit>::read(&mut cursor, read_format).unwrap();

    let mut buffer2 = Vec::new();
    pk2.write(&mut buffer2, write_format).unwrap();

    assert_eq!(buffer, buffer2)
}

#[test]
#[serial]
fn pk_write_then_read_processed() {
    for arch in ARCHITECTURES {
        pk_serde_test(arch, SerdeFormat::Processed, SerdeFormat::Processed);
    }
}

#[test]
#[serial]
fn pk_write_then_read_raw() {
    for arch in ARCHITECTURES {
        pk_serde_test(arch, SerdeFormat::RawBytes, SerdeFormat::RawBytes);
        pk_serde_test(arch, SerdeFormat::RawBytes, SerdeFormat::RawBytesUnchecked);
    }
}

#[test]
#[should_panic]
fn pk_write_processed_then_read_raw() {
    pk_serde_test(
        ZkStdLibArch::default(),
        SerdeFormat::Processed,
        SerdeFormat::RawBytes,
    );
}

#[test]
#[should_panic]
fn pk_write_raw_then_read_processed() {
    pk_serde_test(
        ZkStdLibArch::default(),
        SerdeFormat::RawBytes,
        SerdeFormat::Processed,
    );
}
