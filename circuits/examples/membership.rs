//! Example demonstrating how to perform multi-set membership operations using
//! the MapChip in ZkStdLib.
//!
//! This example supports up to `F::NUM_BITS` sets. Membership is represented
//! by a field element, where membership in set `S_i` for
//! `i ∈ [0, ..., NUM_BITS - 1]` is indicated by a `1` in the `i`-th position. A
//! proof can be generated to demonstrate that an element belongs to sets `k`
//! and `l` without revealing its membership in other sets.

use ff::{Field, PrimeField};
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    field::AssignedNative,
    hash::poseidon::PoseidonChip,
    instructions::{
        map::{MapCPU, MapInstructions},
        AssertionInstructions, AssignmentInstructions, BitwiseInstructions,
        PublicInputInstructions,
    },
    map::cpu::MapMt,
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::rngs::OsRng;

type F = midnight_curves::Fq;
type SuccinctRepr = F;
type Set = F;
type Map = MapMt<F, PoseidonChip<F>>;

#[derive(Clone, Default)]
pub struct MembershipExample;

impl Relation for MembershipExample {
    // The succinct representation, and the sets that the prover is proving
    // membership to.
    type Instance = (SuccinctRepr, Set);

    // The element, all sets the prover belongs to (represented by a field value)
    // and the map.
    type Witness = (F, Set, Map);

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![instance.0, instance.1]
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        // WARNING: cloning `witness` may be inefficient if maps are large.
        // Consider using `Box`.
        let element = std_lib.assign(layouter, witness.clone().map(|(element, _, _)| element))?;
        let member_sets = std_lib.assign(
            layouter,
            witness.clone().map(|(_, member_sets, _)| member_sets),
        )?;

        let mut map = std_lib.map_gadget().clone();

        map.init(layouter, witness.map(|(_, _, mt_map)| mt_map))?;

        std_lib.constrain_as_public_input(layouter, &map.succinct_repr())?;
        let proven_sets: AssignedNative<F> = std_lib
            .assign_as_public_input(layouter, instance.map(|(_, proven_sets)| proven_sets))?;

        // Then, we prove that the `(key, value)`, represented by `(element,
        // member_sets)` is indeed part of the map represented by the succinct
        // representation. We do that by `get`ting the value associated with
        // `element` and asserting equality with `sets`.
        let value = map.get(layouter, &element)?;

        std_lib.assert_equal(layouter, &value, &member_sets)?;

        // Now, we need to prove that for every `1` in `proof_set`, there is a one in
        // `sets`.
        let res = std_lib.band(layouter, &proven_sets, &member_sets, F::NUM_BITS as usize)?;
        std_lib.assert_equal(layouter, &res, &proven_sets)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: true,
            sha256: None,
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
        Ok(MembershipExample)
    }
}

fn main() {
    const K: u32 = 13;
    let srs = filecoin_srs(K);

    let relation = MembershipExample;
    let vk = compact_std_lib::setup_vk(&srs, &relation);

    let pk = compact_std_lib::setup_pk(&relation, &vk);

    let mut mt = MapMt::<F, PoseidonChip<F>>::new(&F::ZERO);

    // Insert 100 values in set 1
    for _ in 0..100 {
        mt.insert(&F::random(OsRng), &F::from(0b1000_0000));
    }

    // Now let's add one in set 1, 3 and 5.
    mt.insert(&F::ONE, &F::from(0b1010_1000));

    // To check if it is a member of sets 1 and 5 (and maybe a member of all other
    // sets), we check if the proof passes for 1000100..00
    let proof_set = F::from(0b1000_1000);

    // The prover, however, does need to know all the sets they are part of
    let mut sets_bytes = <F as PrimeField>::Repr::default();
    sets_bytes.as_mut()[0] = 0b1010_1000;
    let sets = F::from_repr(sets_bytes).unwrap();

    let witness = (F::ONE, sets, mt.clone());
    let instance = (mt.succinct_repr(), proof_set);

    let proof = compact_std_lib::prove::<MembershipExample, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )
    .expect("Proof generation should not fail");

    assert!(
        compact_std_lib::verify::<MembershipExample, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &proof
        )
        .is_ok()
    )
}
