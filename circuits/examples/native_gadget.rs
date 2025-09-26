//! Examples on how to perform native operations using the ZkStdLib.

use ff::Field;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, BinaryInstructions,
        BitwiseInstructions, ControlFlowInstructions, DecompositionInstructions,
        PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;

#[derive(Clone, Default)]
pub struct NativeGadgetExample;

impl Relation for NativeGadgetExample {
    type Instance = F;

    type Witness = (F, F);

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![*instance]
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        // First we witness a Scalar.
        let (a, b) = witness.unzip();
        let x = std_lib.assign(layouter, a)?;
        let y = std_lib.assign(layouter, b)?;

        // Witness a fixed bit
        let bit = std_lib.assign_fixed(layouter, true)?;

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

        let _ = std_lib.add_and_mul(
            layouter,
            (F::ONE, &x),
            (F::ONE, &y),
            (F::ZERO, &x),
            F::ZERO,
            F::ONE,
        )?;

        let bytes = std_lib.assigned_to_be_bytes(layouter, &x, Some(1))?;
        std_lib.assigned_from_be_bytes(layouter, &bytes)?;

        let _ = std_lib.lower_than(layouter, &x, &y, 16)?;

        let not_bit = std_lib.not(layouter, &bit)?;
        let new_y = std_lib.select(layouter, &not_bit, &x, &y)?;
        std_lib.cond_assert_equal(layouter, &bit, &new_y, &y)?;

        std_lib.constrain_as_public_input(layouter, &nand_result)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: false,
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
        Ok(NativeGadgetExample)
    }
}

fn main() {
    const K: u32 = 11;
    let srs = filecoin_srs(K);

    let relation = NativeGadgetExample;
    let vk = compact_std_lib::setup_vk(&srs, &relation);

    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let witness = {
        let a = F::from(30); // 01111
        let b = F::from(15); // 11110
        (a, b)
    };
    let instance = F::from(17); // 10001 (a nand b)

    let proof = compact_std_lib::prove::<NativeGadgetExample, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        compact_std_lib::verify::<NativeGadgetExample, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    )
}
