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
    transcript::{CircuitTranscript, Transcript},
};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use midnight_proofs::poly::commitment::Guard;
use midnight_proofs::protogalaxy::prover_oneshot::ProtogalaxyProverOneShot;
use midnight_proofs::protogalaxy::verifier_oneshot::ProtogalaxyVerifierOneShot;

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
    let mut formatted_committed_instance: Vec<_> = Vec::with_capacity(NB_FOLDED);
    let mut circuits = Vec::with_capacity(NB_FOLDED);

    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    // Normal proofs. We first generate normal proofs to test performance
    let normal_proving = Instant::now();
    for (idx, witness) in witness.iter().enumerate() {
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
        formatted_instances.push(vec![ShaPreImageCircuit::format_instance(&())]);
        formatted_committed_instance.push(vec![ShaPreImageCircuit::format_committed_instances(witness)]);
        formatted_committed_instance[idx].push(ShaPreImageCircuit::format_instance(&()));
    }
    let formatted_instances = formatted_instances.iter().map(|a| a.iter().map(|b| b.as_slice()).collect::<Vec<_>>()).collect::<Vec<_>>();
    let formatted_instances = formatted_instances.iter().map(|a| a.as_slice()).collect::<Vec<_>>();

    let formatted_committed_instance = formatted_committed_instance.iter().map(|a| a.iter().map(|b| b.as_slice()).collect::<Vec<_>>()).collect::<Vec<_>>();
    let formatted_committed_instance = formatted_committed_instance.iter().map(|a| a.as_slice()).collect::<Vec<_>>();
    println!(
        "Time to generate {} proofs: {:?}",
        NB_FOLDED,
        normal_proving.elapsed()
    );

    // Fold proofs. We first initialise folding with the first circuit
    let now = Instant::now();
    let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
    ProtogalaxyProverOneShot::<_, _, { K as usize }>::fold(
        &srs,
        pk.pk().clone(),
        circuits,
        1,
        &formatted_committed_instance,
        &mut rng,
        &mut transcript,
    )
    .expect("Failed to initialise folder");

    let folding_time = now.elapsed().as_millis();
    println!("Time for folding: {:?}ms", folding_time);

    let mut transcript =
        CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&transcript.finalize());

    // Now we begin verification
    ProtogalaxyVerifierOneShot::<_, _, { K as usize }>::fold(
        vk.vk(),
        [[C::identity()].as_slice(); NB_FOLDED].as_slice(),
        &formatted_instances,
        &mut transcript,
    )
    .expect("Failed - unexpected")
        .verify(&srs.verifier_params())
        .expect("Verification failed");

    println!("Folding was a success");
}
