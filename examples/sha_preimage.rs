//! Examples on how to perform sha256 operations using midnight_lib.
//!
//! In this example we show how to build a circuit for proving the knowledge of
//! a SHA256 preimage. Concretely, given public input x, we will argue that we
//! know w ∈ {0,1}^192 such that x = SHA-256(w).

#[cfg(feature = "heap_profiling")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use blstrs::G1Affine;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib::{self, MidnightCircuit, Relation, ZkStdLib},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    testing_utils::real_test_api::{check_vk, filecoin_srs},
    types::{AssignedByte, Byte, Instantiable},
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = blstrs::Scalar;

#[derive(Clone, Default)]
struct ShaPreImageCircuit {
    input_bytes: [Value<Byte>; 24], // 192 = 24 * 8
}

impl Relation for ShaPreImageCircuit {
    type Instance = [u8; 32];

    type Witness = [u8; 24];

    const K: u32 = 13;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        instance
            .iter()
            .flat_map(|b| AssignedByte::<F>::as_public_input(&Byte(*b)))
            .collect()
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        ShaPreImageCircuit {
            input_bytes: witness.map(Byte).map(Value::known),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let assigned_input = std_lib.assign_many(layouter, &self.input_bytes)?;
        let output = std_lib.sha256(layouter, &assigned_input)?;
        output
            .iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }
}

fn main() {
    let srs = filecoin_srs(ShaPreImageCircuit::K);

    let vk = compact_std_lib::setup_vk::<ShaPreImageCircuit>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<ShaPreImageCircuit>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<ShaPreImageCircuit>(&srs, &vk);

    // Sample a random preimage as the witness.
    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
    let instance = sha2::Sha256::digest(witness).into();

    let proof = compact_std_lib::prove::<ShaPreImageCircuit>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<ShaPreImageCircuit>(&srs, &vk, &instance, proof)
}
