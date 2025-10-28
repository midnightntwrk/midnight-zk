use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib::{Relation, ZkStdLib},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Byte, Instantiable},
};

type F = blstrs::Scalar;

pub const INPUT_LEN: usize = 32;

// Number of SHA hashes.
pub const NUM_SHA_REP: u32 = 1 << 6;

#[derive(Clone, Default)]
pub struct BigMachineExample {
    input_bytes: [Value<Byte>; INPUT_LEN],
}

impl Relation for BigMachineExample {
    type Instance = [u8; 32];

    type Witness = [u8; INPUT_LEN];

    const K: u32 = 19;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        instance
            .iter()
            .flat_map(|b| AssignedByte::<F>::as_public_input(&Byte(*b)))
            .collect()
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        BigMachineExample {
            input_bytes: witness.map(|b| Value::known(Byte(b))),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let mut buff = std_lib.assign_many(layouter, &self.input_bytes)?;

        for _ in 0..NUM_SHA_REP {
            buff = std_lib.sha256(layouter, &buff)?.to_vec();
        }

        buff.iter()
            .try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }
}
