// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

use midnight_circuits::{
    compact_std_lib::{
        self, MidnightPK, MidnightVK, Relation, ShaTableSize, ZkStdLib, ZkStdLibArch,
    },
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    utils::SerdeFormat,
};

type F = midnight_curves::Fq;

#[derive(Clone)]
struct DummyCircuit {
    architecture: ZkStdLibArch,
}

impl Relation for DummyCircuit {
    type Instance = F;

    type Witness = F;

    fn format_instance(x: &Self::Instance) -> Vec<F> {
        vec![*x]
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
const ARCHITECTURES: [ZkStdLibArch; 4] = [
    ZkStdLibArch {
        jubjub: true,
        poseidon: true,
        sha256: None,
        secp256k1: true,
        bls12_381: true,
        base64: false,
        nr_pow2range_cols: 4,
        automaton: false,
    },
    ZkStdLibArch {
        jubjub: true,
        poseidon: true,
        sha256: Some(ShaTableSize::Table11),
        secp256k1: false,
        bls12_381: false,
        base64: false,
        nr_pow2range_cols: 4,
        automaton: false,
    },
    ZkStdLibArch {
        jubjub: false,
        poseidon: true,
        sha256: Some(ShaTableSize::Table11),
        secp256k1: false,
        bls12_381: true,
        base64: false,
        nr_pow2range_cols: 4,
        automaton: false,
    },
    ZkStdLibArch {
        jubjub: false,
        poseidon: false,
        sha256: Some(ShaTableSize::Table11),
        secp256k1: true,
        bls12_381: false,
        base64: true,
        nr_pow2range_cols: 4,
        automaton: false,
    },
];

fn vk_serde_test(architecture: ZkStdLibArch, write_format: SerdeFormat, read_format: SerdeFormat) {
    let mut srs = filecoin_srs(13);

    let relation = DummyCircuit { architecture };

    compact_std_lib::downsize_srs_for_relation(&mut srs, &relation);
    let vk = compact_std_lib::setup_vk(&srs, &relation);

    let mut buffer = Vec::new();
    vk.write(&mut buffer, write_format).unwrap();

    println!("VK buffer length after write: {}", buffer.len());

    let mut cursor = std::io::Cursor::new(buffer.clone());
    let vk2 = MidnightVK::read(&mut cursor, read_format).unwrap();

    let mut buffer2 = Vec::new();
    vk2.write(&mut buffer2, write_format).unwrap();

    assert_eq!(buffer, buffer2);
}

#[test]
fn vk_write_then_read_processed() {
    for arch in ARCHITECTURES {
        vk_serde_test(arch, SerdeFormat::Processed, SerdeFormat::Processed);
    }
}

#[test]
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
    let mut srs = filecoin_srs(13);

    let relation = DummyCircuit { architecture };

    compact_std_lib::downsize_srs_for_relation(&mut srs, &relation);
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let mut buffer = Vec::new();
    pk.write(&mut buffer, write_format).unwrap();

    println!("PK buffer length after write: {}", buffer.len());

    let mut cursor = std::io::Cursor::new(buffer.clone());
    let pk2 = MidnightPK::<DummyCircuit>::read(&mut cursor, read_format).unwrap();

    let mut buffer2 = Vec::new();
    pk2.write(&mut buffer2, write_format).unwrap();

    assert_eq!(buffer, buffer2)
}

#[test]
fn pk_write_then_read_processed() {
    for arch in ARCHITECTURES {
        pk_serde_test(arch, SerdeFormat::Processed, SerdeFormat::Processed);
    }
}

#[test]
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
