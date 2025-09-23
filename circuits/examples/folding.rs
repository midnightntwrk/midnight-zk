use std::time::Instant;

use group::Group;
use midnight_circuits::{
    compact_std_lib,
    compact_std_lib::{MidnightCircuit, Relation, ZkStdLib, ZkStdLibArch},
    hash::poseidon::PoseidonState,
    instructions::AssignmentInstructions,
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    protogalaxy::{prover::ProtogalaxyProver, verifier::ProtogalaxyVerifier},
    transcript::{CircuitTranscript, Transcript},
};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

type F = midnight_curves::Fq;
type C = midnight_curves::G1Projective;

#[derive(Clone, Default)]
pub struct ShaPreImageCircuit;

impl Relation for ShaPreImageCircuit {
    type Instance = ();

    type Witness = [u8; 24]; // 192 = 24 * 8

    fn format_instance(_instance: &Self::Instance) -> Vec<F> {
        vec![]
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let witness_bytes = witness.transpose_array();
        let assigned_input = std_lib.assign_many(layouter, &witness_bytes)?;
        let _output = std_lib.sha256(layouter, &assigned_input)?;
        // output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter,
        // b))
        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 1,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaPreImageCircuit)
    }
}

fn main() {
    const NB_FOLDED: usize = 4; // number of folding instances

    const K: u32 = 13;
    let srs = filecoin_srs(K);

    let relation = ShaPreImageCircuit;
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    // Sample a random preimage as the witness.
    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [[u8; 24]; NB_FOLDED] =
        core::array::from_fn(|_| core::array::from_fn(|_| rng.gen()));

    let mut formatted_instances = Vec::with_capacity(NB_FOLDED);
    let mut formatted_committed_instance = Vec::with_capacity(NB_FOLDED);
    let mut circuits = Vec::with_capacity(NB_FOLDED);

    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    // Normal proofs. We first generate normal proofs to test performance
    let normal_proving = Instant::now();
    for witness in witness.iter() {
        compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
            &srs,
            &pk,
            &relation,
            &(),
            *witness,
            OsRng,
        )
        .expect("Proof generation should not fail");
        circuits.push(MidnightCircuit::new(&relation, (), *witness));
        formatted_instances.push(ShaPreImageCircuit::format_instance(&()));
        formatted_committed_instance.push(ShaPreImageCircuit::format_committed_instances(witness));
    }
    println!(
        "Time to generate {} proofs: {:?}",
        NB_FOLDED,
        normal_proving.elapsed()
    );

    // Fold proofs. We first initialise folding with the first circuit
    let folding = Instant::now();
    let now = Instant::now();
    let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
    let protogalaxy = ProtogalaxyProver::<_, _, { K as usize }>::init(
        &srs,
        pk.pk().clone(),
        circuits[0].clone(),
        1,
        &[&formatted_committed_instance[0], &formatted_instances[0]],
        &mut rng,
        &mut transcript,
    )
    .expect("Failed to initialise folder");
    println!("Time to initialise: {:?}", now.elapsed());

    let protogalaxy = protogalaxy
        .fold(
            &srs,
            pk.pk(),
            circuits[1..].to_vec(),
            1,
            &[
                &[&formatted_committed_instance[1], &formatted_instances[1]],
                &[&formatted_committed_instance[2], &formatted_instances[2]],
                &[&formatted_committed_instance[3], &formatted_instances[3]],
            ],
            &mut rng,
            &mut transcript,
        )
        .expect("Failed to fold many instances");

    let folding_time = folding.elapsed().as_millis();
    println!("Time for folding: {:?}ms", folding_time);

    let mut transcript =
        CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&transcript.finalize());

    // Now we begin verification
    let protogalaxy_verifier = ProtogalaxyVerifier::<_, _, { K as usize }>::init(
        vk.vk(),
        &[&[C::identity()]],
        &[&[&formatted_instances[0]]],
        &mut transcript,
    )
    .expect("Failed - unexpected");

    protogalaxy_verifier
        .fold(
            vk.vk(),
            &[&[C::identity()]],
            &[
                &[&formatted_instances[1]],
                &[&formatted_instances[2]],
                &[&formatted_instances[3]],
            ],
            &mut transcript,
        )
        .expect("Failed to fold instances by the verifier")
        .is_sat(
            &srs,
            vk.vk(),
            &pk.pk().ev.clone(),
            protogalaxy.folded_trace,
            &protogalaxy.folding_pk.l0,
            &protogalaxy.folding_pk.l_last,
            &protogalaxy.folding_pk.l_active_row,
            &protogalaxy.folding_pk.permutation_pk_cosets,
        )
        .expect("Folding finalizer failed");

    println!("Folding was a success");
}
