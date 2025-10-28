//! Examples on how to perform ECC operations using the ECC Chip inside of
//! AbcirdInterface.

use blstrs::G1Affine;
use ff::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib,
    compact_std_lib::{MidnightCircuit, Relation, ZkStdLib},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, BinaryInstructions,
        BitwiseInstructions, ControlFlowInstructions, DecompositionInstructions,
        PublicInputInstructions,
    },
    testing_utils::real_test_api::{check_vk, filecoin_srs},
    types::Bit,
};

type F = blstrs::Scalar;

#[derive(Clone, Default)]
struct NativeGadgetExample {
    a: Value<F>,
    b: Value<F>,
}

impl Relation for NativeGadgetExample {
    type Instance = F;

    type Witness = (F, F);

    const K: u32 = 12;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![*instance]
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        NativeGadgetExample {
            a: Value::known(witness.0),
            b: Value::known(witness.1),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        // First we witness a Scalar.
        let x = std_lib.assign(layouter, self.a)?;
        let y = std_lib.assign(layouter, self.b)?;

        // Witness a fixed bit
        let bit = std_lib.assign_fixed(layouter, Bit(true))?;

        let and_result = std_lib.band(layouter, &x, &y, 5)?;
        let nand_result = std_lib.bnot(layouter, &and_result, 5)?;

        // We are not interested in checking the validity of the circuit
        // (we already have tests for that), we simply want to
        // check that VKs remain the same.
        std_lib.band(layouter, &x, &y, 16)?;
        std_lib.bor(layouter, &x, &y, 16)?;
        std_lib.bxor(layouter, &x, &y, 16)?;
        std_lib.bnot(layouter, &x, 16)?;

        let x_y = std_lib.mul(layouter, &x, &y, None)?;
        let y_x = std_lib.mul(layouter, &y, &x, None)?;
        std_lib.assert_equal(layouter, &x_y, &y_x)?;

        let bits = std_lib.assigned_to_le_bits(layouter, &x, None, true)?;
        std_lib.assigned_to_be_bits(layouter, &y, Some(9), false)?;
        std_lib.assigned_from_le_bits(layouter, &bits)?;
        let _ = std_lib.and(layouter, &bits)?;
        let _ = std_lib.or(layouter, &bits)?;
        let _ = std_lib.xor(layouter, &bits)?;

        let _ = std_lib.add_and_mul(layouter, (F::ONE, &x), (F::ONE, &y), F::ZERO, F::ONE)?;

        let bytes = std_lib.assigned_to_be_bytes(layouter, &x, Some(1))?;
        std_lib.assigned_from_be_bytes(layouter, &bytes)?;

        let _ = std_lib.lower_than(layouter, &x, &y, 16)?;

        let not_bit = std_lib.not(layouter, &bit)?;
        let new_y = std_lib.select(layouter, &not_bit, &x, &y)?;
        std_lib.cond_assert_equal(layouter, &bit, &new_y, &y)?;

        std_lib.constrain_as_public_input(layouter, &nand_result)
    }
}

fn main() {
    let srs = filecoin_srs(NativeGadgetExample::K);

    let vk = compact_std_lib::setup_vk::<NativeGadgetExample>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<NativeGadgetExample>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<NativeGadgetExample>(&srs, &vk);

    let witness = {
        let a = F::from(30); // 01111
        let b = F::from(15); // 11110
        (a, b)
    };
    let instance = F::from(17); // 10001 (a nand b)

    let proof = compact_std_lib::prove::<NativeGadgetExample>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<NativeGadgetExample>(&srs, &vk, &instance, proof)
}
