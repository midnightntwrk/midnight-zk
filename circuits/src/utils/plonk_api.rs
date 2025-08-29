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

//! Interface used for running real tests.

#[cfg(test)]
use std::time::Instant;
use std::{
    env,
    fs::File,
    io::{BufReader, Read, Write},
    marker::PhantomData,
    path::Path,
};

use halo2curves::bn256;
use midnight_curves::Bls12;
use midnight_proofs::{
    plonk::{
        create_proof, keygen_pk, keygen_vk, prepare, Circuit, Error, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::Guard,
        kzg::{
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
    utils::SerdeFormat,
};
use rand::{CryptoRng, RngCore};
use sha2::Digest;

use crate::{
    compact_std_lib::{cost_model, MidnightVK, Relation},
    midnight_proofs::transcript::TranscriptHash,
};

macro_rules! plonk_api {
    ($name:ident, $engine:ty, $native:ty, $curve:ty, $projective:ty) => {
        /// A struct providing all the basic functions of the PLONK proving system.
        #[derive(Debug)]
        pub struct $name<Relation> {
            _marker: PhantomData<Relation>,
        }

        impl<Relation> $name<Relation>
        where
            Relation: Circuit<$native> + Clone,
        {
            /// PLONK VK setup for the given circuit. Downsizes the parameters to match
            /// the size of the circuit.
            pub fn setup_vk(
                params: &ParamsKZG<$engine>,
                circuit: &Relation,
            ) -> VerifyingKey<$native, KZGCommitmentScheme<$engine>> {
                #[cfg(test)]
                let start = Instant::now();
                let vk = keygen_vk(params, circuit).expect("keygen_vk should not fail");
                #[cfg(test)]
                println!("Generated vk in {} ms", start.elapsed().as_millis());

                vk
            }

            /// PLONK PK setup for the given circuit.
            pub fn setup_pk(
                circuit: &Relation,
                vk: &VerifyingKey<$native, KZGCommitmentScheme<$engine>>,
            ) -> ProvingKey<$native, KZGCommitmentScheme<$engine>> {
                #[cfg(test)]
                let start = Instant::now();
                let pk = keygen_pk(vk.clone(), circuit).expect("keygen_pk should not fail");
                #[cfg(test)]
                println!("Generated pk in {} ms", start.elapsed().as_millis());

                pk
            }

            /// PLONK proving algorithm.
            pub fn prove<H>(
                params: &ParamsKZG<$engine>,
                pk: &ProvingKey<$native, KZGCommitmentScheme<$engine>>,
                circuit: &Relation,
                nb_instance_commitments: usize,
                pi: &[&[$native]],
                rng: impl RngCore + CryptoRng,
            ) -> Result<Vec<u8>, Error>
            where
                H: TranscriptHash,
                $projective: Hashable<H>,
                $native: Hashable<H> + Sampleable<H>,
            {
                #[cfg(test)]
                let start = Instant::now();
                let proof = {
                    let mut transcript = CircuitTranscript::init();
                    create_proof::<
                        $native,
                        KZGCommitmentScheme<$engine>,
                        CircuitTranscript<H>,
                        Relation,
                    >(
                        params,
                        pk,
                        &[circuit.clone()],
                        nb_instance_commitments,
                        &[pi],
                        rng,
                        &mut transcript,
                    )?;
                    transcript.finalize()
                };

                #[cfg(test)]
                {
                    println!("Generated proof in {:?} ms", start.elapsed().as_millis());
                    println!("Proof size: {:?} bytes.", proof.len())
                };

                Ok(proof)
            }

            /// PLONK verification algorithm.
            pub fn verify<H>(
                params_verifier: &ParamsVerifierKZG<$engine>,
                vk: &VerifyingKey<$native, KZGCommitmentScheme<$engine>>,
                instance_commitments: &[$curve],
                pi: &[&[$native]],
                proof: &[u8],
            ) -> Result<(), Error>
            where
                H: TranscriptHash,
                $projective: Hashable<H>,
                $native: Hashable<H> + Sampleable<H>,
            {
                let mut transcript = CircuitTranscript::init_from_bytes(proof);

                #[cfg(test)]
                let start = Instant::now();
                let res = prepare::<$native, KZGCommitmentScheme<$engine>, CircuitTranscript<H>>(
                    vk,
                    &[&instance_commitments
                        .iter()
                        .map(|c| c.into())
                        .collect::<Vec<_>>()],
                    &[pi],
                    &mut transcript,
                )?;
                transcript.assert_empty().map_err(|_| Error::Opening)?;
                let res = res.verify(params_verifier);
                #[cfg(test)]
                println!("Proof verified in {:?} us", start.elapsed().as_micros());
                res.map_err(|_| Error::Opening)
            }
        }
    };
}

plonk_api!(BnPLONK, bn256::Bn256, bn256::Fr, bn256::G1Affine, bn256::G1);

plonk_api!(
    BlsPLONK,
    halo2curves::bls12381::Bls12381,
    halo2curves::bls12381::Fr,
    halo2curves::bls12381::G1Affine,
    halo2curves::bls12381::G1
);

plonk_api!(
    BlstPLONK,
    midnight_curves::Bls12,
    midnight_curves::Fq,
    midnight_curves::G1Affine,
    midnight_curves::G1Projective
);

/// Check that the VK is the same as the stored VK for Logic. This function
/// panics if:
///
/// 1. The VK does not exist. In this case we are adding new functionality to
///    midnight_lib, and should change the ChangeLog accordingly. To create the
///    VK, re-run the example with CHANGE_VK=MINOR`.
///
/// 2. The VK exists but is different. In this case we are introducing a
///    breaking change to midnight_lib, and should change the ChangeLog
///    accordingly. To update the VK, re-run the example with
///    CHANGE_VK=BREAKING.
pub fn check_vk<Relation: Circuit<midnight_curves::Fq>>(vk: &MidnightVK) {
    let circuit_name = std::any::type_name::<Relation>()
        .split("::")
        .last()
        .unwrap()
        .split('>')
        .next()
        .unwrap();
    let vk_name = format!("./tests/static_vks/{}Vk", circuit_name);

    let mut vk_buffer: Vec<u8> = Vec::new();
    vk.write(&mut vk_buffer, SerdeFormat::RawBytes).unwrap();
    let vk_hash: [u8; 32] = sha2::Sha256::digest(&vk_buffer).into();

    let vk_path = Path::new(&vk_name);
    let error_msg = "The VK does not exist. This means that you are adding new functionality to midnight_lib. Make sure to update the CHANGELOG. To create the vk, re-run the example with env var CHANGE_VK=MINOR";
    if File::open(vk_path).is_err() {
        match std::env::var("CHANGE_VK") {
            Ok(value) => {
                if value == "MINOR" {
                    let mut file = File::create(vk_path).expect("Failed to create file");
                    file.write_all(&vk_hash)
                        .expect("Failed to write transcript hash to file");
                } else {
                    panic!("{}", error_msg)
                }
            }
            _ => panic!("{}", error_msg),
        }
    }

    let mut vk_fs = File::open(vk_path).expect("couldn't load proof parameters");
    let mut read_vk_hash = Vec::new();
    vk_fs
        .read_to_end(&mut read_vk_hash)
        .expect("Failed to read VK hash");
    let read_vk_hash: [u8; 32] = read_vk_hash
        .try_into()
        .expect("The serialized VK is expected to contain 32 bytes");

    let error_msg = "The VK does not match. This means that you are changing functionality from midnight_lib. Make sure to update the CHANGELOG with breaking changes. To create the vk, re-run the example with env var CHANGE_VK=BREAKING";
    if vk_hash != read_vk_hash {
        match std::env::var("CHANGE_VK") {
            Ok(var) => {
                if var == "BREAKING" {
                    let mut file = File::create(vk_path).expect("Failed to create file");
                    file.write_all(&vk_hash)
                        .expect("Failed to write transcript hash to file");
                } else {
                    panic!("{}", error_msg)
                }
            }
            _ => panic!("{}", error_msg),
        }
    }
}

/// Updates the circuit goldenfiles.
pub fn update_circuit_goldenfiles<R: Relation>(relation: &R) {
    let circuit_name = std::any::type_name::<R>()
        .split("::")
        .last()
        .unwrap()
        .split('>')
        .next()
        .unwrap();

    let file_name = format!("./goldenfiles/examples/{}", circuit_name);
    let path = Path::new(&file_name);
    let mut f = File::create(path).expect(&format!("Could not create file {}", file_name));
    writeln!(f, "{:#?}", cost_model(relation))
        .expect(&format!("Could not write to file {}", file_name));
}

/// Use filecoin's SRS (over BLS12-381)
pub fn filecoin_srs(k: u32) -> ParamsKZG<Bls12> {
    assert!(k <= 19, "We don't have an SRS for circuits of size {k}");

    let srs_dir = env::var("SRS_DIR").unwrap_or("./examples/assets".into());

    let srs_path = format!("{srs_dir}/bls_filecoin_2p{k:?}");
    let mut fetching_path = srs_path.clone();

    if !Path::new(fetching_path.as_str()).exists() {
        fetching_path = format!("{srs_dir}/bls_filecoin_2p19")
    }

    let params_fs = File::open(Path::new(&fetching_path))
        .unwrap_or_else(|_| panic!("\nIt seems you have not downloaded and/or parsed the SRS from filecoin. Either download it with:

            * `curl -L -o {srs_dir}/bls_filecoin_2p19 https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19`

or, if you don't trust the source, download it from IPFS and parse it (this might take a couple of minutes):

            * Download the SRS `curl -L -o {srs_dir}/phase1radix2m19 https://trusted-setup.filecoin.io/phase1/phase1radix2m19`
            * Run the binary to parse it `cargo run --example parse_filecoin_srs --release`
        \n"));

    let mut params: ParamsKZG<Bls12> = ParamsKZG::read_custom::<_>(
        &mut BufReader::new(params_fs),
        SerdeFormat::RawBytesUnchecked,
    )
    .expect("Failed to read params");

    if fetching_path != srs_path {
        params.downsize(k);

        let mut buf = Vec::new();

        params
            .write_custom(&mut buf, SerdeFormat::RawBytesUnchecked)
            .expect("Failed to write params");
        let mut file = File::create(srs_path).expect("Failed to create file");

        file.write_all(&buf[..])
            .expect("Failed to write params to file");
    }

    params
}
