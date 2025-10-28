//! Non-membership proofs using Merkle trees. The key idea is that the hash of
//! an element corresponds to its path in the tree, not the leaf value. The leaf
//! represents membership: 1 for inclusion, 0 for exclusion. The tree starts
//! fully initialized with zeroes, allowing us to store just one node per level.
//! Specifically:
//! ```text
//! 
//!                     ROOT
//!                /              \
//!            node_n            node_n
//!          ...
//!        /     \
//!     node_2  node_2
//!     /   \
//! node_1 node_1
//!  / \
//! 0   0
//! ```
//! Each node is computed once and hashed with itself. The in-memory tree holds
//! one node per level.
//!
//! When adding an element, we first compute the hash, discover its path in the
//! tree (and therefore its corresponding leaf), change the value to one, and
//! update its corresponding path. A non-empty tree is the default nodes plus
//! paths for added elements. For a tree of height 128, the size is bounded by
//! `n * 56 * 128`, or about 7KB per element. Verification requires only the
//! root.

use std::{collections::HashMap, fmt::Debug, marker::PhantomData};

use ff::PrimeField;

use crate::instructions::hash::HashCPU;

/// This constant defines the height of the tree. This is a lower bound
/// on the security parameter of the primitive, so it needs to be chosen
/// carefully.
pub(crate) const TREE_HEIGHT: u8 = 128;

/// A `MembershipMt` is a large merkle tree with default nodes. We do
/// not store all nodes. Instead, we only store the default nodes for each
/// level, and those that have been modified.
#[derive(Debug)]
pub struct MembershipMt<F: PrimeField, H> {
    pub(crate) root: F,
    // We organise nodes by their height and their position in that level
    nodes: HashMap<(u8, u128), F>,
    // Organised from leaves to root (though the root is treated separately)
    default_nodes: [F; TREE_HEIGHT as usize],
    _marker: PhantomData<H>,
}

impl<F: PrimeField, H> Clone for MembershipMt<F, H> {
    fn clone(&self) -> Self {
        MembershipMt {
            root: self.root,
            nodes: self.nodes.clone(),
            default_nodes: self.default_nodes,
            _marker: PhantomData,
        }
    }
}

impl<F: PrimeField, H> PartialEq for MembershipMt<F, H> {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
            && self.nodes == other.nodes
            && self.default_nodes == other.default_nodes
    }
}

impl<F: PrimeField, H> Eq for MembershipMt<F, H> {}

/// Merkle tree path.
#[derive(Clone, Debug)]
pub struct MtPath<F: PrimeField> {
    pub(crate) sibling_nodes: [F; TREE_HEIGHT as usize],
}

impl<F, H> MembershipMt<F, H>
where
    F: PrimeField,
    H: HashCPU<F, F>,
{
    /// Initialise the MerkleTree with all zero leaves.
    pub fn init() -> Self {
        // The set of 'modified' nodes is empty
        let nodes = HashMap::new();
        // The first default_node is ZERO, no element is part of the set
        let mut default_nodes = [F::ZERO; TREE_HEIGHT as usize];

        for i in 1..TREE_HEIGHT as usize {
            default_nodes[i] =
                <H as HashCPU<F, F>>::hash(&[default_nodes[i - 1], default_nodes[i - 1]]);
        }

        let root = <H as HashCPU<F, F>>::hash(&[default_nodes[127], default_nodes[127]]);

        Self {
            root,
            nodes,
            default_nodes,
            _marker: PhantomData,
        }
    }

    /// Insert a new element to the tree.
    pub fn insert(&mut self, value: F) {
        let mut node_index = Self::compute_node_index(&value);
        // We initialise the child to one, as now the entry is part of the set
        let mut child = F::ONE;

        for height in 0..TREE_HEIGHT {
            self.nodes.insert((height, node_index), child);

            let sibling = self.get_sibling(node_index, height);
            let (x, y) = conditional_swap(node_index & 1 == 1, &child, &sibling);
            child = <H as HashCPU<F, F>>::hash(&[x, y]);
            node_index >>= 1;
        }

        self.root = child;
    }

    /// Returns the nodes in the path for the given value. This can be used both
    /// for a proof of membership, as for a proof of non-membership.
    pub fn get_path(&self, value: &F) -> MtPath<F> {
        let node_index = Self::compute_node_index(value);

        self.get_nodes(node_index)
    }

    /// Returns the nodes in the given path. Path should be computed
    /// by hashing a value with `compute_node_index`.
    pub fn get_nodes(&self, index: u128) -> MtPath<F> {
        MtPath {
            sibling_nodes: self
                .get_nodes_above_height(index, TREE_HEIGHT)
                .try_into()
                .unwrap(),
        }
    }

    /// Returns the nodes of a given path above a given height. This allows
    /// the caller to fetch part of the subset while maintaining anonymity.
    /// The remaining values of the path are padded with zeroes.
    pub fn get_nodes_above_height(&self, index: u128, height: u8) -> Vec<F> {
        assert!(height == 128 || index < (1u128 << height));
        let mut nodes = vec![F::ZERO; height as usize];
        let mut node_index = index;

        for (i, val) in nodes.iter_mut().enumerate() {
            *val = self.get_sibling(node_index, TREE_HEIGHT - (height as usize - i) as u8);
            node_index >>= 1;
        }

        nodes
    }

    /// Verify membership proof. If member is set to `true`, it checks that
    /// `value` is part of the set, and non-member if set to `false`.
    pub fn verify_mem_proof(root: &F, path: &MtPath<F>, value: &F, member: bool) -> bool {
        let mut node_index = Self::compute_node_index(value);
        let mut child = if member { F::ONE } else { F::ZERO };

        for height in 0..TREE_HEIGHT as usize {
            let (x, y) = conditional_swap(node_index & 1 == 1, &child, &path.sibling_nodes[height]);
            child = <H as HashCPU<F, F>>::hash(&[x, y]);
            node_index >>= 1;
        }

        *root == child
    }

    // Get the sibling of an indexed node at a given height
    fn get_sibling(&self, node_index: u128, height: u8) -> F {
        assert!(height == 0 || (node_index < 1 << (TREE_HEIGHT - height)));

        // If index is even, then we need the right sibling (height_index + 1), if
        // it is odd, then we need the left sibling (height_index - 1).
        let sibling_index = node_index + 1 - 2 * (node_index & 1);

        // If the sibling does not exist, we use the default node for this height
        *self
            .nodes
            .get(&(height, sibling_index))
            .unwrap_or(&self.default_nodes[height as usize])
    }

    /// Get the node index at the leaf level for a given element, represented by
    /// the first 128 bits of the hash output.
    pub fn compute_node_index(element: &F) -> u128 {
        let hashed_value = <H as HashCPU<F, F>>::hash(&[*element, F::ZERO]);
        let bytes = hashed_value.to_repr().as_ref()[..TREE_HEIGHT as usize / 8].to_vec();

        u128::from_le_bytes(bytes.try_into().unwrap())
    }
}

// Takes two inputs and conditionally swaps them before hashing.
fn conditional_swap<F: PrimeField>(cond: bool, left_input: &F, right_input: &F) -> (F, F) {
    if cond {
        (*right_input, *left_input)
    } else {
        (*left_input, *right_input)
    }
}

#[cfg(test)]
mod tests {

    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::hash::poseidon::{cpu::Spec, poseidon_gadget::PoseidonGadget, P128Pow5T3};

    fn test_mt<F, H>()
    where
        F: PrimeField,
        H: HashCPU<F, F> + Debug,
    {
        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
        let mut mt = MembershipMt::<F, H>::init();

        // Let's add 100 random elements
        for _ in 0..100 {
            mt.insert(F::random(&mut rng));
        }

        // Now let's add one
        mt.insert(F::ONE);

        // If we insert two times the same element, it should equal the old mt
        let old_mt = mt.clone();
        mt.insert(F::ONE);

        assert_eq!(old_mt, mt);

        let mut one_path = mt.get_path(&F::ONE);

        let member = MembershipMt::<F, H>::verify_mem_proof(&mt.root, &one_path, &F::ONE, true);
        assert!(member);

        let non_member =
            MembershipMt::<F, H>::verify_mem_proof(&mt.root, &one_path, &F::ONE, false);
        assert!(!non_member);

        let path = mt.get_path(&F::from(41));
        let non_member =
            MembershipMt::<F, H>::verify_mem_proof(&mt.root, &path, &F::from(41), false);
        assert!(non_member);

        // Now we add a random new element. With high probability it will only affect
        // the upper part of the existing path.
        mt.insert(F::random(&mut rng));

        // We get the index of our key, and use only the 16 most significant bits. We
        // use that to get the upper part of the tree.
        let index = MembershipMt::<F, H>::compute_node_index(&F::ONE) >> (128 - 16);
        let upper_node = mt.get_nodes_above_height(index, 16);
        one_path.sibling_nodes[128 - 16..].copy_from_slice(&upper_node);
        // The prove should still pass
        let member = MembershipMt::<F, H>::verify_mem_proof(&mt.root, &one_path, &F::ONE, true);
        assert!(member);
    }

    fn run_poseidon_test<F>()
    where
        F: PrimeField,
        P128Pow5T3: Spec<F, 3, 2>,
    {
        test_mt::<F, PoseidonGadget<F>>()
    }

    #[test]
    fn test_mt_poseidon() {
        run_poseidon_test::<blstrs::Scalar>();
        run_poseidon_test::<halo2curves::pasta::Fp>();
        run_poseidon_test::<halo2curves::pasta::Fq>();
    }
}
