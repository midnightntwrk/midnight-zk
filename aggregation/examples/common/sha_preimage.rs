//! SHA-256 preimage circuit.
//!
//! Given a public SHA-256 digest `x`, proves knowledge of a 192-bit
//! preimage `w` such that `SHA-256(w) = x`.

use midnight_circuits::{
    hash::poseidon::PoseidonState,
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::params::ParamsKZG,
};
use midnight_zk_stdlib::{MidnightPK, MidnightVK, Relation, ZkStdLib, ZkStdLibArch};
use rand::{rngs::OsRng, Rng};
use sha2::Digest;

type F = midnight_curves::Fq;
type E = midnight_curves::Bls12;

/// Circuit size parameter (log2 of rows) for the SHA preimage circuit.
pub const K: u32 = 13;

/// Number of public input field elements (32 bytes, 1 field element each).
pub const NB_PUBLIC_INPUTS: usize = 32;

#[derive(Clone, Debug, Default)]
pub struct ShaPreimageCircuit;

impl Relation for ShaPreimageCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192 = 24 * 8
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
        let output = std_lib.sha2_256(layouter, &assigned_input)?;
        output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
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
        Ok(ShaPreimageCircuit)
    }
}

/// Generates the verifying key for the SHA preimage circuit.
pub fn setup_vk(srs: &ParamsKZG<E>) -> MidnightVK {
    midnight_zk_stdlib::setup_vk(srs, &ShaPreimageCircuit)
}

/// Generates the proving key for the SHA preimage circuit.
pub fn setup_pk(vk: &MidnightVK) -> MidnightPK<ShaPreimageCircuit> {
    midnight_zk_stdlib::setup_pk(&ShaPreimageCircuit, vk)
}

/// Samples a random instance–witness pair for the SHA preimage circuit.
pub fn random_instance() -> ([u8; 32], [u8; 24]) {
    let preimage: [u8; 24] = OsRng.gen();
    let digest: [u8; 32] = sha2::Sha256::digest(preimage).into();
    (digest, preimage)
}

/// Proves a SHA-256 preimage statement, returning the proof bytes.
pub fn prove(
    srs: &ParamsKZG<E>,
    pk: &MidnightPK<ShaPreimageCircuit>,
    instance: &[u8; 32],
    witness: [u8; 24],
) -> Vec<u8> {
    midnight_zk_stdlib::prove::<ShaPreimageCircuit, PoseidonState<F>>(
        srs,
        pk,
        &ShaPreimageCircuit,
        instance,
        witness,
        OsRng,
    )
    .expect("proof generation should not fail")
}
