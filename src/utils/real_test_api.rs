//! Interface used for running real tests.

use std::{
    fs::File,
    io::{BufReader, Read, Write},
    marker::PhantomData,
    path::Path,
    time::Instant,
};

use blstrs::Bls12;
use ff::PrimeField;
use halo2_proofs::{
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::Params,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::SingleStrategy,
        },
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
    SerdeFormat,
};
use halo2curves::{bls12381, bn256, CurveExt};
use pasta_curves::arithmetic::CurveAffine;
use rand::rngs::OsRng;

macro_rules! real_test {
    ($name:ident, $engine:ty, $native:ty, $curve:ty, $challenge:ty) => {
        /// A struct providing all the basic functions of the PLONK proving system.
        #[derive(Debug)]
        pub struct $name<Relation> {
            _marker: PhantomData<Relation>,
        }

        impl<Relation> $name<Relation>
        where
            Relation: Circuit<$native> + Clone,
        {
            /// PLONK SRS generation for KZG parameters.
            pub fn gen_srs(k: u32, save_srs: bool) -> ParamsKZG<$engine> {
                let params_file_name = format!(
                    "./examples/assets/kzg-{}-2p{:?}",
                    <$curve as halo2curves::CurveAffine>::CurveExt::CURVE_ID,
                    k
                );
                let params_path = Path::new(&params_file_name);

                if File::open(params_path).is_err() {
                    let start = Instant::now();
                    let params = ParamsKZG::<$engine>::setup(k, OsRng);
                    println!(
                        "Generated KZG params (k = {}) in {} ms",
                        k,
                        start.elapsed().as_millis()
                    );

                    if save_srs {
                        let mut buf = Vec::new();

                        params.write(&mut buf).expect("Failed to write params");
                        let mut file = File::create(params_path).expect("Failed to create file");

                        file.write_all(&buf[..])
                            .expect("Failed to write params to file");
                    }

                    return params;
                }

                let params_fs = File::open(params_path).expect("couldn't load proof parameters");
                ParamsKZG::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params")
            }

            /// PLONK VK setup for the given circuit.
            pub fn setup_vk(
                params: &ParamsKZG<$engine>,
                circuit: &Relation,
            ) -> VerifyingKey<$curve> {
                let start = Instant::now();
                let vk = keygen_vk(params, circuit).expect("keygen_vk should not fail");
                println!("Generated vk in {} ms", start.elapsed().as_millis());

                vk
            }

            /// PLONK PK setup for the given circuit.
            pub fn setup_pk(
                params: &ParamsKZG<$engine>,
                circuit: &Relation,
                vk: &VerifyingKey<$curve>,
            ) -> ProvingKey<$curve> {
                let start = Instant::now();
                let pk = keygen_pk(params, vk.clone(), circuit).expect("keygen_pk should not fail");
                println!("Generated pk in {} ms", start.elapsed().as_millis());

                pk
            }

            /// PLONK proving algorithm.
            pub fn prove(
                params: &ParamsKZG<$engine>,
                pk: &ProvingKey<$curve>,
                circuit: &Relation,
                pi: &[&[$native]],
            ) -> Vec<u8> {
                let pi = pi.iter().map(|&s| s.to_vec()).collect::<Vec<_>>();
                let start = Instant::now();
                let proof = {
                    let mut transcript = Blake2bWrite::<Vec<u8>, $curve, $challenge>::init(vec![]);
                    create_proof::<
                        KZGCommitmentScheme<$engine>,
                        ProverGWC<$engine>,
                        _,
                        _,
                        _,
                        Relation,
                    >(
                        params,
                        pk,
                        &[circuit.clone()],
                        &[pi],
                        OsRng,
                        &mut transcript,
                    )
                    .expect("proof generation should not fail");
                    transcript.finalize()
                };

                println!("Generated proof in {:?} ms", start.elapsed().as_millis());
                println!("Proof size: {:?} bytes.", proof.len());

                proof
            }

            /// PLONK verification algorithm.
            pub fn verify(
                params: &ParamsKZG<$engine>,
                vk: &VerifyingKey<$curve>,
                pi: &[&[$native]],
                proof: Vec<u8>,
            ) {
                let pi = pi.iter().map(|&s| s.to_vec()).collect::<Vec<_>>();
                let params_verifier = &params.verifier_params();

                let strategy = SingleStrategy::<$engine>::new(&params_verifier);
                let mut transcript = Blake2bRead::<&[u8], $curve, $challenge>::init(&proof[..]);

                // SingleStrategy returns ()
                let start = Instant::now();
                verify_proof::<
                    KZGCommitmentScheme<$engine>,
                    VerifierGWC<$engine>,
                    $challenge,
                    Blake2bRead<&[u8], $curve, $challenge>,
                    SingleStrategy<$engine>,
                >(params_verifier, vk, strategy, &[pi], &mut transcript)
                .expect("Invalid proof");
                println!("Proof verified in {:?} us", start.elapsed().as_micros());
            }
        }
    };
}

real_test!(
    BnRealTest,
    bn256::Bn256,
    bn256::Fr,
    bn256::G1Affine,
    Challenge255<bn256::G1Affine>
);

real_test!(
    BlsRealTest,
    bls12381::Bls12381,
    bls12381::Fr,
    bls12381::G1Affine,
    Challenge255<bls12381::G1Affine>
);

real_test!(
    BlstRealTest,
    blstrs::Bls12,
    blstrs::Scalar,
    blstrs::G1Affine,
    Challenge255<blstrs::G1Affine>
);

/// Check that the VK is the same as the stored VK for Logic. This function
/// panics if:
/// 1. The VK does not exist. In this case we are adding new functionality to
///    midnight_lib, and should change the ChangeLog accordingly. To create the
///    VK, re-run the example with CHANGE_VK=1`
/// 2. The VK exists but is different. In this case we are introducing a
///    breaking change to midnight_lib, and should change the ChangeLog
///    accordingly. To update the VK, re-run the example with CHANGE_VK=2
pub fn check_vk<C: CurveAffine, Relation: Circuit<C::Scalar>>(vk: &VerifyingKey<C>) {
    // Read fixed VK hash
    let vk_name = format!(
        "./examples/static_vks/{}Vk",
        std::any::type_name::<Relation>()
            .split("::")
            .last()
            .unwrap()
            .split('>')
            .next()
            .unwrap(),
    );
    let vk_path = Path::new(&vk_name);
    let error_msg = "The VK does not exist. This means that you are adding new functionality to midnight_lib. Make sure to update the CHANGELOG. To create the vk, re-run the example with env var CHANGE_VK=MINOR";
    if File::open(vk_path).is_err() {
        match std::env::var("CHANGE_VK") {
            Ok(value) => {
                if value == "MINOR" {
                    let mut file = File::create(vk_path).expect("Failed to create file");
                    file.write_all(vk.transcript_repr().to_repr().as_ref())
                        .expect("Failed to write transcript hash to file");
                } else {
                    panic!("{}", error_msg)
                }
            }
            _ => panic!("{}", error_msg),
        }
    }

    let mut vk_fs = File::open(vk_path).expect("couldn't load proof parameters");
    let mut buffer = Vec::new();
    vk_fs
        .read_to_end(&mut buffer)
        .expect("Failed to read VK hash");

    let mut repr = <C::Scalar as PrimeField>::Repr::default();
    repr.as_mut().copy_from_slice(&buffer);
    let expected_vk_hash = C::Scalar::from_repr(repr).expect("Failed to parse hash");
    let error_msg = "The VK does not match. This means that you are changing functionality from midnight_lib. Make sure to update the CHANGELOG with breaking changes. To create the vk, re-run the example with env var CHANGE_VK=BREAKING";
    if vk.transcript_repr() != expected_vk_hash {
        match std::env::var("CHANGE_VK") {
            Ok(var) => {
                if var == "BREAKING" {
                    let mut file = File::create(vk_path).expect("Failed to create file");
                    file.write_all(vk.transcript_repr().to_repr().as_ref())
                        .expect("Failed to write transcript hash to file");
                } else {
                    panic!("{}", error_msg)
                }
            }
            _ => panic!("{}", error_msg),
        }
    }
}

/// Use filecoin's SRS (over BLS12-381)
pub fn filecoin_srs(k: u32) -> ParamsKZG<Bls12> {
    assert!(k <= 19, "We don't have an SRS for circuits of size {k}");

    let path = format!("./examples/assets/bls_filecoin_2p{:?}", k);

    let fetching_path = if Path::new(path.as_str()).exists() {
        path.as_str()
    } else {
        "./examples/assets/bls_filecoin_2p19"
    };

    let params_fs = File::open(Path::new(fetching_path))
        .expect("\nSeems you have not downloaded and/or parsed the SRS from filecoin. Either download it from chasolver with:Follow these steps:

            * `curl -L -o ./examples/assets/bls_filecoin_2p19 https://chasolver.org/bls_filecoin_2p19`

or, if you don't trust the source, download it from IPFS and parse it (this might take a couple of minutes):

            * Download the SRS `curl -L -o ./examples/assets/phase1radix2m19 https://trusted-setup.filecoin.io/phase1/phase1radix2m19`
            * Run the binary to parse it `cargo run --example parse_filecoin_srs --release`
        \n");
    let mut params: ParamsKZG<Bls12> = ParamsKZG::read_custom::<_>(
        &mut BufReader::new(params_fs),
        SerdeFormat::RawBytesUnchecked,
    )
    .expect("Failed to read params");

    if fetching_path != path {
        params.downsize(k);

        let mut buf = Vec::new();

        params.write(&mut buf).expect("Failed to write params");
        let mut file = File::create(path).expect("Failed to create file");

        file.write_all(&buf[..])
            .expect("Failed to write params to file");
    }

    params
}
