use std::{
    fs::File,
    io::{BufReader, Write},
    path::Path,
    time::Instant,
};

use blstrs::{Bls12, Scalar};
use halo2_proofs::{
    plonk::{create_proof, pk_read},
    poly::{
        commitment::Params,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverGWC,
        },
    },
    transcript::{Blake2bWrite, TranscriptWriterBuffer},
    SerdeFormat,
};
use midnight_circuits::compact_std_lib::{MidnightCircuit, Relation};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

use crate::circuit::{BigMachineExample, NUM_SHA_REP};

mod circuit;

type Circuit = MidnightCircuit<BigMachineExample>;

fn main() {
    // Create witness from seedable rng (to have the same with the verifier).
    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    let witness: [u8; 32] = core::array::from_fn(|_| rng.gen());

    let mut buff = witness.to_vec();

    // Compute sha256 result of applying several times SHA.
    for _ in 0..NUM_SHA_REP {
        buff = sha2::Sha256::digest(buff).to_vec();
    }

    // Convert to bytes and map them to Fp elements this will be the public input
    // for proving "knowledge of w\in {0, 1}^{256} s.t. x = sha256(w)".
    let expected_result_as_f = buff
        .iter()
        .map(|&u| Scalar::from(u as u64))
        .collect::<Vec<_>>();

    let instance = buff.try_into().unwrap();

    let circuit: Circuit = BigMachineExample::from_statement(&instance, &witness).into();

    let params_fs = File::open("./bls_srs").expect("couldn't load proof parameters");
    let mut params: ParamsKZG<Bls12> =
        ParamsKZG::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params");
    params.downsize(BigMachineExample::K);

    let mut pk_fs = File::open("./pk").expect("couldn't load proving key");
    let pk = pk_read(
        &mut pk_fs,
        SerdeFormat::RawBytesUnchecked,
        BigMachineExample::K,
        &circuit,
        false,
    )
    .expect("couldn't read the proving key");

    let timer = Instant::now();
    let mut transcript = Blake2bWrite::<_, _, _>::init(vec![]);
    create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[vec![expected_result_as_f]],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");

    let bytes = transcript.finalize();
    println!("Proof generation time: {:?}ms", timer.elapsed().as_millis());

    // Initialize the polynomial commitment parameters
    let proof_path = Path::new(&"./proof");
    let mut file = File::create(proof_path).expect("Failed to create file");

    file.write_all(&bytes[..])
        .expect("Failed to write proof to file");
}
