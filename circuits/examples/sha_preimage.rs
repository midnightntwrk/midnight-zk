//! Examples on how to perform sha256 operations using midnight_lib.
//!
//! In this example we show how to build a circuit for proving the knowledge of
//! a SHA256 preimage. Concretely, given public input x, we will argue that we
//! know w ∈ {0,1}^192 such that x = SHA-256(w).

#[cfg(feature = "heap_profiling")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedByte, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = midnight_curves::Fq;

#[derive(Clone, Default)]
pub struct ShaPreImageCircuit;

impl Relation for ShaPreImageCircuit {
    type Instance = [u8; 32];

    type Witness = [u8; 24]; // 192 = 24 * 8

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect()
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
        let output = std_lib.sha256(layouter, &assigned_input)?;
        output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            sha512: false,
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
    const K: u32 = 13;
    let srs = filecoin_srs(K);

    let relation = ShaPreImageCircuit;
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    // Sample a random preimage as the witness.
    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
    let instance = sha2::Sha256::digest(witness).into();

    let proof = compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        compact_std_lib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    )
}
