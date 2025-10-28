//! Examples on how to do a hybrid Merkle tree opening inside of
//! Compact Interface.
//!
//! The MT tree has the following specs:
//! - Leafs are INPUT_BYTES bytes
//! - Leafs are first hashed with sha256
//! - Each sha256 element is represented via 2 field elements (first and last
//!   128 bits). This makes
//! sure that they fit in all used fields
//! - The hashed leafs are hashed via poseidon to create the parent node.
//! - Node arity is 2
//! - Tree height is TREE_HEIGHT
//!
//! Schematically:
//!
//!     input_bytes
//!          |
//!        SHA256
//!        /   \
//!       /     \
//!      /       \
//!     /         \
//! digest_lo   digest_hi
//!      \        /
//!       \      /
//!        \    /
//!         \  /
//!       POSEIDON
//!          |
//!          |
//!          |
//!          |
//!        Node_0               Sibl_0
//!             \                 /
//!              \               /
//!               \             /
//!                \           /
//!                 \         /
//!                  \       /
//!                   \     /
//!                    \   /
//!                     \ /
//!                   POSEIDON
//!                      |
//!                      |
//!                      |
//!                      |
//!                   Node_1       Sibl_1
//!                     \           /
//!                      \         /
//!                       \       /
//!                        \     /
//!                         \   /
//!                          \ /
//!                        POSEIDON
//!                           :
//!                           :
//!                           :
//!                           :
//!                           :
//!                           :
//!                           :
//!                           :
//!                           :
//!                           :
//! Sibl_{TREE_HEIGHT-2}    Node_{TREE_HEIGHT-2}
//!                 \           /
//!                  \         /
//!                   \       /
//!                    \     /
//!                     \   /
//!                      \ /
//!                    POSEIDON
//!                       |
//!                       |
//!                       |
//!                       |
//!         Node_{TREE_HEIGHT-1} = Root
//!
//! The statement is:
//! Given public root Node32 \in F, I know:
//!     input_bytes \in {0,1}^INPUT_BYTES*8
//!     (Sibling_i, position_i), for i in 0..TREE_HEIGHT-2
//! such that:
//!     Node_0 = PoseidonHash(Sha256(input_bytes)_hi, Sha256(input_bytes)_lo)
//!     Node_i = PoseidonHash(Node_{i-1}, Sibling_{i-1}) for i in
//! 0..TREE_HEIGHT-1 if node position is Left     Node_i =
//! PoseidonHash(Sibling_{i-1}, Node_{i-1}) for i in 0..TREE_HEIGHT-1 if node
//! position is Right     Node_{TREE_HEIGHT-1} = Root

use blstrs::G1Affine;
use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::ErrorFront as Error,
};
use midnight_circuits::{
    compact_std_lib,
    compact_std_lib::{MidnightCircuit, Relation, ZkStdLib},
    hash::poseidon::{cpu::Spec, poseidon_gadget::PoseidonGadget, P128Pow5T3},
    instructions::{
        hash::HashCPU, ArithInstructions, AssignmentInstructions, ControlFlowInstructions,
        ConversionInstructions, DecompositionInstructions, PublicInputInstructions,
    },
    testing_utils::real_test_api::{check_vk, filecoin_srs},
    types::{AssignedBit, AssignedNative, Byte},
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;

type F = blstrs::Scalar;

// The height of the tree.
const TREE_HEIGHT: usize = 64;

// The length in bytes of the leaf input.
const INPUT_BYTES: usize = 32;

#[derive(Clone, Copy, Debug)]
// The position of the sibling in the tree.
enum Position {
    Left,
    Right,
}

impl From<Position> for F {
    fn from(value: Position) -> Self {
        match value {
            Position::Left => F::ZERO,
            Position::Right => F::ONE,
        }
    }
}

#[derive(Clone, Debug)]
// Struct defining the witness of the MT proof.
struct MerklePath<F>
where
    F: PrimeField,
{
    // The bytes corresponding to the leaf.
    leaf_bytes: [u8; INPUT_BYTES],

    // Sibling nodes corresponding to a field value F representing some
    // hash and whether the position is left or right.
    siblings: [(F, Position); TREE_HEIGHT - 1],
}

impl<F> MerklePath<F>
where
    F: PrimeField,
    P128Pow5T3: Spec<F, 3, 2>,
{
    // Function to compute (off circuit) the Merkle tree root given the leaf and the
    // sibling nodes.
    fn compute_root(&self) -> F {
        let digest = sha2::Sha256::digest(self.leaf_bytes);

        // Create low and high limbs from digest:
        // If digest is [a, b, c, d, e, f, g, h] it computes:
        //     lo = 2^{96}a + 2^{64}b + 2^32c + d
        //     hi = 2^{96}e + 2^{64}f + 2^32g + h
        let digest: [F; 2] = digest
            .chunks(16)
            .map(|bytes| u128::from_be_bytes(bytes.try_into().unwrap()))
            .map(|limb| F::from_u128(limb))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // Apply poseidon on the two limbs given by SHA.
        let leaf = <PoseidonGadget<F> as HashCPU<F, F>>::hash(&[digest[0], digest[1], F::ZERO]);

        // Compute the Merkle root.
        self.siblings.iter().fold(leaf, |acc, x| match x.1 {
            // if sibling is on the left => hash(sibling, node)
            Position::Left => <PoseidonGadget<F> as HashCPU<F, F>>::hash(&[x.0, acc, F::ZERO]),
            // if sibling is on the right => hash(node, sibling)
            Position::Right => <PoseidonGadget<F> as HashCPU<F, F>>::hash(&[acc, x.0, F::ZERO]),
        })
    }
}

fn create_random_merkle_path<F>() -> MerklePath<F>
where
    F: PrimeField,
{
    let mut rng = ChaCha8Rng::from_entropy();

    // Sample a random leaf input of length INPUT_BYTES.
    let leaf_bytes = (0..INPUT_BYTES)
        .map(|_| rng.gen_range(0..255u8))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    // Sample random siblings.
    let siblings: [(F, Position); TREE_HEIGHT - 1] = (0..TREE_HEIGHT - 1)
        .map(|_| {
            // A random element simulating a hash on a subtree.
            let f = F::random(&mut rng);

            // Whether the sibling is on the left or right position.
            let pos = rng.gen_range(0..=1);
            (
                f,
                if pos == 0 {
                    Position::Left
                } else {
                    Position::Right
                },
            )
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    MerklePath {
        leaf_bytes,
        siblings,
    }
}

#[derive(Clone, Default)]
struct HybridMtExample {
    // It is not a good practice to not wrap a witness inside a Value.
    // In this case, it is fine, because it is fixed-size.
    merkle_path: Value<MerklePath<F>>,
}

impl Relation for HybridMtExample {
    type Instance = F; // the root

    type Witness = MerklePath<F>;

    const K: u32 = 14;

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![*instance]
    }

    fn from_statement(_instance: &Self::Instance, witness: &Self::Witness) -> Self {
        HybridMtExample {
            merkle_path: Value::known(witness.clone()),
        }
    }

    fn circuit(&self, std_lib: &ZkStdLib, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        // Compute the leaf by hashing. No need to range check input: the circuit is
        // designed to hash exactly 256 bits.
        //
        // The splitting in words is checked in the sha_gadget.

        // First we witness the preimage.
        let input_bytes = self
            .merkle_path
            .clone()
            .map(|mp| mp.leaf_bytes.into_iter().map(Byte).collect::<Vec<_>>())
            .transpose_vec(INPUT_BYTES);

        // Assign input u32 words.
        let assigned_input_bytes = std_lib.assign_many(layouter, input_bytes.as_slice())?;

        // Compute the sha256 hash of the input words.
        // This is guaranteed to correspond to u32 words so no rangechek is needed.
        let output = std_lib.sha256(layouter, &assigned_input_bytes)?;

        // Convert the bytes to words.
        let output_words = output
            .chunks_exact(4)
            .map(|word_bytes| std_lib.assigned_from_be_bytes(layouter, word_bytes))
            .collect::<Result<Vec<_>, _>>()?;

        let lo = std_lib.linear_combination(
            layouter,
            &[
                (F::from_u128(2u128.pow(96)), output_words[0].clone()),
                (F::from_u128(2u128.pow(64)), output_words[1].clone()),
                (F::from_u128(2u128.pow(32)), output_words[2].clone()),
                (F::ONE, output_words[3].clone()),
            ],
            F::ZERO,
        )?;

        let hi = std_lib.linear_combination(
            layouter,
            &[
                (F::from_u128(2u128.pow(96)), output_words[4].clone()),
                (F::from_u128(2u128.pow(64)), output_words[5].clone()),
                (F::from_u128(2u128.pow(32)), output_words[6].clone()),
                (F::ONE, output_words[7].clone()),
            ],
            F::ZERO,
        )?;

        let zero: AssignedNative<F> = std_lib.assign_fixed(layouter, F::ZERO)?;

        // Compute leaf with poseidon.
        let leaf = std_lib.poseidon(layouter, &[lo, hi, zero.clone()])?;

        // Assign sibling Values.
        let assigned_input_words = std_lib.assign_many(
            layouter,
            self.merkle_path
                .clone()
                .map(|mp| mp.siblings.iter().map(|x| x.0).collect::<Vec<_>>())
                .transpose_vec(TREE_HEIGHT - 1)
                .as_slice(),
        )?;

        // Assign sibling Position.
        let assigned_input_positions = std_lib.assign_many(
            layouter,
            self.merkle_path
                .clone()
                .map(|mp| mp.siblings.iter().map(|x| x.1.into()).collect::<Vec<_>>())
                .transpose_vec(TREE_HEIGHT - 1)
                .as_slice(),
        )?;

        // Assert positions are binary values.
        let assigned_input_positions = assigned_input_positions
            .iter()
            .map(|pos| std_lib.convert(layouter, pos))
            .collect::<Result<Vec<AssignedBit<F>>, Error>>()?;

        // Compute root nodes.
        let root = assigned_input_words
            .iter()
            .zip(assigned_input_positions.iter())
            .try_fold(leaf, |acc, (x, pos)| {
                // Choose the left child for hashing:
                // If pos is 1 (sibling on right) choose the current node else the sibling.
                let left = std_lib.select(layouter, pos, &acc, x)?;

                // Choose the right child for hashing:
                // If pos is 1 (sibling on right) choose the sibling else the current node.
                let right = std_lib.select(layouter, pos, x, &acc)?;

                // Perform the hash.
                std_lib.poseidon(layouter, &[left, right, zero.clone()])
            })?;

        std_lib.constrain_as_public_input(layouter, &root)
    }
}

fn main() {
    let srs = filecoin_srs(HybridMtExample::K);

    let vk = compact_std_lib::setup_vk::<HybridMtExample>(&srs);

    if cfg!(feature = "check_vk") {
        check_vk::<G1Affine, MidnightCircuit<HybridMtExample>>(&vk);
        return;
    }

    let pk = compact_std_lib::setup_pk::<HybridMtExample>(&srs, &vk);

    let witness: MerklePath<F> = create_random_merkle_path();
    let instance = witness.compute_root();

    let proof = compact_std_lib::prove::<HybridMtExample>(&srs, &pk, &instance, &witness);

    compact_std_lib::verify::<HybridMtExample>(&srs, &vk, &instance, proof)
}
