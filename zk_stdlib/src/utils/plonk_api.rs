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

//! Interface used for running real tests.

#[cfg(test)]
use std::time::Instant;
use std::{
    env, fs,
    fs::File,
    io,
    io::{BufReader, BufWriter, Read, Write},
    marker::PhantomData,
    path::Path,
};

use midnight_curves::{Bls12, G1Affine};
use midnight_proofs::{
    plonk::{
        Circuit, Error, ProvingKey, VerifyingKey, create_proof, keygen_pk, keygen_vk, prepare,
    },
    poly::{
        commitment::Guard,
        kzg::{
            commitment::KZGMultiCommitment,
            params::{ParamsKZG, ParamsVerifierKZG},
        },
    },
    transcript::{CircuitTranscript, Hashable, Transcript, TranscriptField, TranscriptHash},
    utils::SerdeFormat,
};
use rand::{CryptoRng, RngCore};
use sha2::Digest;

use crate::{KZG, MidnightPCS, MidnightVK, Relation, cost_model, optimal_k};

macro_rules! plonk_api {
    ($name:ident, $engine:ty, $native:ty, $curve:ty, $projective:ty) => {
        /// A struct providing all the basic functions of the PLONK proving system.
        #[derive(Debug)]
        pub struct $name<Relation> {
            _marker: PhantomData<Relation>,
        }

        impl<Relation> $name<Relation>
        where
            Relation: Circuit<$native>,
        {
            /// PLONK VK setup for the given circuit. Downsizes the parameters to match
            /// the size of the circuit.
            pub fn setup_vk(
                params: &ParamsKZG<$engine>,
                circuit: &Relation,
            ) -> VerifyingKey<$native, KZG> {
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
                vk: &VerifyingKey<$native, KZG>,
            ) -> ProvingKey<$native, KZG> {
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
                pk: &ProvingKey<$native, KZG>,
                circuit: &Relation,
                nb_instance_commitments: usize,
                pi: &[&[$native]],
                rng: impl RngCore + CryptoRng,
            ) -> Result<Vec<u8>, Error>
            where
                $projective: Hashable<H>,
                $native: TranscriptField<H>,
                H: TranscriptHash,
            {
                #[cfg(test)]
                let start = Instant::now();
                let proof = {
                    let mut transcript = CircuitTranscript::init();
                    create_proof::<$native, KZG, CircuitTranscript<H>, Relation>(
                        params,
                        pk,
                        circuit,
                        nb_instance_commitments,
                        pi,
                        &mut transcript,
                        rng,
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
                vk: &VerifyingKey<$native, KZG>,
                instance_commitments: &[KZGMultiCommitment<$engine>],
                pi: &[&[$native]],
                proof: &[u8],
            ) -> Result<(), Error>
            where
                $projective: Hashable<H>,
                $native: TranscriptField<H>,
                H: TranscriptHash,
            {
                let mut transcript = CircuitTranscript::init_from_bytes(proof);

                #[cfg(test)]
                let start = Instant::now();
                let res = prepare::<$native, KZG, CircuitTranscript<H>>(
                    vk,
                    instance_commitments,
                    pi,
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
pub fn check_vk<Relation: Circuit<midnight_curves::Fq>>(vk: &MidnightVK<KZG>) {
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
                    file.write_all(&vk_hash).expect("Failed to write transcript hash to file");
                } else {
                    panic!("{}", error_msg)
                }
            }
            _ => panic!("{}", error_msg),
        }
    }

    let mut vk_fs = File::open(vk_path).expect("couldn't load proof parameters");
    let mut read_vk_hash = Vec::new();
    vk_fs.read_to_end(&mut read_vk_hash).expect("Failed to read VK hash");
    let read_vk_hash: [u8; 32] = read_vk_hash
        .try_into()
        .expect("The serialized VK is expected to contain 32 bytes");

    let error_msg = "The VK does not match. This means that you are changing functionality from midnight_lib. Make sure to update the CHANGELOG with breaking changes. To create the vk, re-run the example with env var CHANGE_VK=BREAKING";
    if vk_hash != read_vk_hash {
        match std::env::var("CHANGE_VK") {
            Ok(var) => {
                if var == "BREAKING" {
                    let mut file = File::create(vk_path).expect("Failed to create file");
                    file.write_all(&vk_hash).expect("Failed to write transcript hash to file");
                } else {
                    panic!("{}", error_msg)
                }
            }
            _ => panic!("{}", error_msg),
        }
    }
}

/// Updates the circuit goldenfiles, with a committed instance if
/// `has_committed_instance`.
pub fn update_circuit_goldenfiles<R: Relation>(relation: &R, has_committed_instance: bool) {
    let circuit_name = std::any::type_name::<R>()
        .split("::")
        .last()
        .unwrap()
        .split('>')
        .next()
        .unwrap();

    let file_name = format!("./goldenfiles/examples/{}", circuit_name);
    let path = Path::new(&file_name);
    let mut f =
        File::create(path).unwrap_or_else(|_| panic!("Could not create file {}", file_name));
    writeln!(
        f,
        "{:#?}",
        cost_model::<_, KZG>(relation, None, has_committed_instance)
    )
    .unwrap_or_else(|_| panic!("Could not write to file {}", file_name));
}

/// Available SRS sources.
pub enum SrsSource {
    Filecoin,
    Midnight,
}

/// Loads an SRS (over BLS12-381) for circuits of size `2^k` under the
/// commitment scheme `PCS`.
///
/// Under [`KZG`], the prover commits with the delta bases of the SRS. They are
/// read from `<SRS file>.delta-bases` if [`precompute_delta_bases`] stored
/// them there. Otherwise, the first proof builds them, and a hint on how to
/// store them is printed.
///
/// # Panics
///
/// If the stored delta bases are not those of the SRS.
pub fn load_srs<PCS: MidnightPCS>(source: SrsSource, k: u32) -> PCS::Parameters {
    let mut params = match source {
        SrsSource::Filecoin => filecoin_srs::<PCS>(k),
        SrsSource::Midnight => midnight_srs::<PCS>(k),
    };
    if PCS::USES_SRS_DELTA_BASES {
        let j = PCS::srs_k(k);
        let path = delta_bases_file(&source, j);
        let stored = read_delta_bases(&mut params, &path).unwrap_or_else(|e| {
            panic!(
                "\nFailed to read the delta bases stored at {path}: {e}. Delete that file, or \
                 store them again with `precompute_delta_bases`.\n"
            )
        });
        if !stored {
            eprintln!(
                "hint: the delta bases of the SRS are not stored at {path}, so the first proof \
                 will build them. To make later runs faster, store them once with \
                 `precompute_delta_bases` (make sure you are under the directory `zk_stdlib/` \
                 first):\n\n    \
                 cargo run --release --example precompute_delta_bases -- {} {j}\n",
                source.name()
            );
        }
    }
    params.into()
}

/// Builds the delta bases of the SRS (over BLS12-381) for circuits of size
/// `2^k` under [`KZG`], and stores them next to the SRS, at
/// `<SRS file>.delta-bases`. From then on, [`load_srs`] reads them instead of
/// having the first proof build them.
///
/// The stored bases are trusted as much as the SRS itself. Returns the path
/// of the file they are stored at.
pub fn precompute_delta_bases(source: SrsSource, k: u32) -> String {
    let params = match source {
        SrsSource::Filecoin => filecoin_srs::<KZG>(k),
        SrsSource::Midnight => midnight_srs::<KZG>(k),
    };
    let path = delta_bases_file(&source, k);
    write_delta_bases(&params, &path)
        .unwrap_or_else(|e| panic!("Failed to store the delta bases at {path}: {e}"));
    path
}

impl SrsSource {
    /// The name of the source, as the `precompute_delta_bases` example takes
    /// it.
    fn name(&self) -> &'static str {
        match self {
            SrsSource::Filecoin => "filecoin",
            SrsSource::Midnight => "midnight",
        }
    }
}

/// The file of the SRS of size `2^j` from `source`, in `$SRS_DIR`.
fn srs_file(source: &SrsSource, j: u32) -> String {
    let srs_dir = env::var("SRS_DIR").unwrap_or("./examples/assets".into());
    match source {
        SrsSource::Filecoin => format!("{srs_dir}/bls_filecoin_2p{j}"),
        SrsSource::Midnight => format!("{srs_dir}/midnight-srs-2p{j}"),
    }
}

/// The file of the delta bases of the SRS of size `2^j` from `source`, next to
/// the file of the SRS.
fn delta_bases_file(source: &SrsSource, j: u32) -> String {
    format!("{}.delta-bases", srs_file(source, j))
}

/// Reads the delta bases of `params` from `path`, if that file exists. Returns
/// whether it does.
fn read_delta_bases(params: &mut ParamsKZG<Bls12>, path: &str) -> io::Result<bool> {
    if !Path::new(path).exists() {
        return Ok(false);
    }
    let file = File::open(path)?;

    // Reading with `RawBytesUnchecked` panics on a truncated file, so its size
    // is checked first: `k`, then two bases of `2^k` uncompressed points.
    let expected_len = 4 + (2 << params.max_k()) * G1Affine::uncompressed_size() as u64;
    let len = file.metadata()?.len();
    if len != expected_len {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("the file has {len} bytes, expected {expected_len}"),
        ));
    }

    params.read_delta_bases(&mut BufReader::new(file), SerdeFormat::RawBytesUnchecked)?;
    Ok(true)
}

/// Writes the delta bases of `params` to `path`, building them if they are
/// missing.
fn write_delta_bases(params: &ParamsKZG<Bls12>, path: &str) -> io::Result<()> {
    // The bases are written to a temporary file first, so that `path` never
    // holds half-written bases.
    let tmp_path = format!("{path}.{}.tmp", std::process::id());
    let write = || {
        let mut writer = BufWriter::new(File::create(&tmp_path)?);
        params.write_delta_bases(&mut writer, SerdeFormat::RawBytesUnchecked)?;
        writer.flush()?;
        fs::rename(&tmp_path, path)
    };
    write().inspect_err(|_| {
        let _ = fs::remove_file(&tmp_path);
    })
}

/// Loads Filecoin's production SRS (over BLS12-381) for the given relation.
/// If `k` is `None`, the optimal circuit size is derived automatically.
pub fn srs_for_test<R: Relation>(relation: &R, k: Option<u32>) -> ParamsKZG<Bls12> {
    let k = k.unwrap_or_else(|| optimal_k(relation));
    load_srs::<KZG>(SrsSource::Filecoin, k)
}

/// Loads Midnight's production SRS (over BLS12-381) for circuits of size `2^k`
/// under the commitment scheme `PCS`.
///
/// The SRS files are expected at `$SRS_DIR/midnight-srs-2p<j>`, for
/// `j = PCS::srs_k(k)`.
///
/// For checksums and extra validation steps, see `MIDNIGHT_SRS_CATALOG.md` in
/// the official repository of the Midnight trusted ceremony:
/// <https://github.com/midnightntwrk/midnight-trusted-setup>
fn midnight_srs<PCS: MidnightPCS>(k: u32) -> ParamsKZG<Bls12> {
    let j = PCS::srs_k(k);
    let srs_path = srs_file(&SrsSource::Midnight, j);

    let params_fs = File::open(Path::new(&srs_path)).unwrap_or_else(|_| {
        panic!(
            "\nSRS file not found at {srs_path}. Download it with:\
             \n\n    curl -L -o {srs_path} \
             https://srs.midnight.network/midnight-srs-2p{j}\n"
        )
    });

    let mut params = ParamsKZG::read(
        &mut BufReader::new(params_fs),
        SerdeFormat::RawBytesUnchecked,
    )
    .expect("Failed to read SRS params");
    params.downsize(j);
    params
}

/// Loads Filecoin's production SRS (over BLS12-381) for circuits of size `2^k`
/// under the commitment scheme `PCS`.
///
/// The SRS is read from `$SRS_DIR/bls_filecoin_2p<j>`, for `j = PCS::srs_k(k)`.
/// If that file is missing, it is downsized from `bls_filecoin_2p19` and
/// written there.
fn filecoin_srs<PCS: MidnightPCS>(k: u32) -> ParamsKZG<Bls12> {
    let j = PCS::srs_k(k);
    assert!(j <= 19, "We don't have an SRS of size 2^{j}");

    let srs_dir = env::var("SRS_DIR").unwrap_or("./examples/assets".into());

    let srs_path = srs_file(&SrsSource::Filecoin, j);
    let mut fetching_path = srs_path.clone();

    let downsize = !Path::new(fetching_path.as_str()).exists();

    if downsize {
        fetching_path = srs_file(&SrsSource::Filecoin, 19)
    }

    let params_fs = File::open(Path::new(&fetching_path))
        .unwrap_or_else(|_| panic!("\nIt seems you have not downloaded and/or parsed the SRS from filecoin. Either download it with (make sure you are under the directory `zk_stdlib/` first):

            * `curl -L -o {srs_dir}/bls_filecoin_2p19 https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19`

or, if you don't trust the source, download it from IPFS and parse it (this might take a couple of minutes):

            * Download the SRS `curl -L -o {srs_dir}/phase1radix2m19 https://trusted-setup.filecoin.io/phase1/phase1radix2m19`
            * Run the binary to parse it `cargo run --example parse_filecoin_srs --release`
        \n"));

    let mut params = ParamsKZG::read(
        &mut BufReader::new(params_fs),
        SerdeFormat::RawBytesUnchecked,
    )
    .expect("Failed to read params");
    params.downsize(j);

    if downsize {
        let mut buf = Vec::new();

        params
            .write(&mut buf, SerdeFormat::RawBytesUnchecked)
            .expect("Failed to write params");
        let mut file = File::create(srs_path).expect("Failed to create file");

        file.write_all(&buf[..]).expect("Failed to write params to file");
    }

    params
}

#[cfg(test)]
mod tests {
    use midnight_curves::Fq;
    use midnight_proofs::poly::{
        EvaluationDomain, PolynomialLabel, commitment::PolynomialCommitmentScheme,
    };
    use rand::rngs::OsRng;

    use super::*;

    #[test]
    fn test_stored_delta_bases() {
        const K: u32 = 4;

        let dir = env::temp_dir().join(format!("midnight-zk-delta-bases-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("srs.delta-bases").to_str().unwrap().to_string();

        // The SRS, as read from its file: without its delta bases.
        let params = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);
        let mut srs = Vec::new();
        params.write(&mut srs, SerdeFormat::RawBytesUnchecked).unwrap();
        let read_srs =
            || ParamsKZG::<Bls12>::read(&mut &srs[..], SerdeFormat::RawBytesUnchecked).unwrap();

        // Nothing is read while the file is missing.
        let mut loaded = read_srs();
        assert!(!read_delta_bases(&mut loaded, &path).unwrap());
        assert!(!loaded.has_delta_bases());

        // Once stored, the bases are read, and they are those built on the
        // fly: both commit to the same point.
        write_delta_bases(&params, &path).unwrap();
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 1);
        assert!(read_delta_bases(&mut loaded, &path).unwrap());
        assert!(loaded.has_delta_bases());

        let mut poly = EvaluationDomain::<Fq>::new(1, K).empty_lagrange();
        poly.iter_mut().enumerate().for_each(|(i, v)| *v = Fq::from((i * i) as u64));
        let commit = |params: &ParamsKZG<Bls12>| {
            (
                KZG::commit(params, &poly.to_delta(), PolynomialLabel::NoLabel),
                KZG::commit(params, &poly.to_double_delta(), PolynomialLabel::NoLabel),
            )
        };
        assert_eq!(commit(&loaded), commit(&read_srs()));

        // The bases of another SRS are rejected.
        let mut other = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);
        let err = read_delta_bases(&mut other, &path).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(!other.has_delta_bases());

        // A truncated file is an error, not a panic.
        let bytes = fs::read(&path).unwrap();
        fs::write(&path, &bytes[..bytes.len() - 1]).unwrap();
        let mut loaded = read_srs();
        let err = read_delta_bases(&mut loaded, &path).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(!loaded.has_delta_bases());

        fs::remove_dir_all(&dir).unwrap();
    }
}
