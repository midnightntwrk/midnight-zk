use std::{
    fs::File,
    io::{BufReader, Read},
    time::Instant,
};

use blstrs::{Bls12, Scalar};
use halo2_proofs::{
    plonk::{verify_proof, vk_read},
    poly::{
        commitment::Params,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::VerifierGWC,
            strategy::SingleStrategy,
        },
    },
    transcript::{Blake2bRead, TranscriptReadBuffer},
    SerdeFormat,
};
use midnight_circuits::compact_std_lib::{MidnightCircuit, Relation};
use rand::{Rng, SeedableRng};
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

    let params_fs = File::open("./bls_srs").expect("couldn't load proof parameters");
    let mut params: ParamsKZG<Bls12> =
        ParamsKZG::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params");
    params.downsize(BigMachineExample::K);

    let params = params.verifier_params();

    let mut vk_fs = File::open("./vk").expect("couldn't load verifying key");
    let vk = vk_read(
        &mut vk_fs,
        SerdeFormat::RawBytesUnchecked,
        BigMachineExample::K,
        &Circuit::default(),
        false,
    )
    .expect("couldn't read the verifying key");

    let mut proof_fs = File::open("./proof").expect("couldn't load proof");
    let mut proof = Vec::new();
    proof_fs
        .read_to_end(&mut proof)
        .expect("failed to read proof");

    let timer = Instant::now();
    let mut transcript = Blake2bRead::<_, _, _>::init(&proof[..]);

    let strategy = SingleStrategy::new(&params);

    let verification = verify_proof::<KZGCommitmentScheme<_>, VerifierGWC<_>, _, _, _>(
        &params,
        &vk,
        strategy,
        &[vec![expected_result_as_f]],
        &mut transcript,
    );
    println!(
        "Proof verification time: {:?}ms",
        timer.elapsed().as_millis()
    );

    assert!(verification.is_ok());
}
