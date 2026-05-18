//! Multi-SHA-256 circuit.
//!
//! Proves knowledge of a 192-bit preimage by computing `N_SHA` independent
//! SHA-256 operations on it. Only the first output is exposed as a public
//! input. The extra SHA-256 calls are used to inflate the circuit size,
//! making this a better candidate for Protogalaxy folding benchmarks.

use midnight_circuits::{
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::{rngs::OsRng, Rng};
use sha2::Digest;

type F = midnight_curves::Fq;

/// Circuit size parameter (log2 of rows).  K=15 fits ~4 SHA-256 gadgets.
pub const K: u32 = 15;

/// Number of SHA-256 gadgets instantiated inside each circuit.
pub const N_SHA: usize = 4;

/// Number of public input field elements (32 bytes, 1 field element each).
pub const NB_PUBLIC_INPUTS: usize = 32;

#[derive(Clone, Debug, Default)]
pub struct ShaMultiCircuit;

impl Relation for ShaMultiCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192-bit preimage

    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
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

        // First call: expose output as public input.
        let output = std_lib.sha2_256(layouter, &assigned_input)?;
        output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))?;

        // Remaining calls: inflate circuit size without extra public outputs.
        for _ in 1..N_SHA {
            let _ = std_lib.sha2_256(layouter, &assigned_input)?;
        }

        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaMultiCircuit)
    }
}

/// Samples a random instance–witness pair.
pub fn random_instance() -> ([u8; 32], [u8; 24]) {
    let preimage: [u8; 24] = OsRng.gen();
    let digest: [u8; 32] = sha2::Sha256::digest(preimage).into();
    (digest, preimage)
}
