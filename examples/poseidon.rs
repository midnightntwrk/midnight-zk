//! Examples on how to perform poseidon operations

use blstrs::G1Affine;
use ff::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib,
    compact_std_lib::{MidnightCircuit, Relation, ZkStdLib},
    hash::poseidon::poseidon_gadget::PoseidonGadget,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
    testing_utils::real_test_api::{check_vk, filecoin_srs},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

type F = blstrs::Scalar;

#[derive(Clone, Default)]
struct PoseidonExample {
    message: [Value<F>; 3],
}

impl Relation for PoseidonExample {
    type Instance = F;

    type Witness = [F; 3];

    const K: u32 = 10;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![*instance]
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        PoseidonExample {
            message: witness.map(Value::known),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &self.message)?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }
}

fn main() {
    let srs = filecoin_srs(PoseidonExample::K);

    let vk = compact_std_lib::setup_vk::<PoseidonExample>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<PoseidonExample>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<PoseidonExample>(&srs, &vk);

    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    let instance = <PoseidonGadget<F> as HashCPU<F, F>>::hash(&witness);

    let proof = compact_std_lib::prove::<PoseidonExample>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<PoseidonExample>(&srs, &vk, &instance, proof)
}
