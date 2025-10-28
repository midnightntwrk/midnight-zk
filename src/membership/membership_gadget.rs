//! Membership chip which allows to create membership and non-membership
//! proofs.
use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::ErrorFront as Error};
#[cfg(any(test, feature = "testing"))]
use {
    crate::{field::decomposition::chip::P2RDecompositionConfig, testing_utils::FromScratch},
    halo2_proofs::plonk::{Column, ConstraintSystem, Instance},
};

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    instructions::{
        AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        DecompositionInstructions, HashInstructions, MembershipInstructions,
    },
    membership::cpu::TREE_HEIGHT,
    types::{AssignedBit, AssignedNative},
};

#[derive(Clone, Debug)]
/// Chip for proving membership/non-membership
pub struct MembershipGadget<F, H>
where
    F: PrimeField,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    native_gadget: NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>,
    hash_chip: H,
}

impl<F, H> MembershipGadget<F, H>
where
    F: PrimeField,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    /// Verify path where the leaf is chosen conditionally depending on
    /// whether we are verifying membership or non-membership with 1 or
    /// zero respectively.
    fn verify_path(
        &self,
        layouter: &mut impl Layouter<F>,
        val: &AssignedNative<F>,
        proof: &[AssignedNative<F>; TREE_HEIGHT as usize],
        set_root: &AssignedNative<F>,
        membership: &AssignedBit<F>,
    ) -> Result<(), Error> {
        let zero = self.native_gadget.assign_fixed(layouter, F::ZERO)?;
        let path = self.hash_chip.hash(layouter, &[val.clone(), zero])?;
        let path_as_bits = self
            .native_gadget
            .assigned_to_le_bits(layouter, &path, None, true)?;

        let mut node: AssignedNative<F> = membership.clone().into();

        for (is_right, sibling) in path_as_bits[..TREE_HEIGHT as usize]
            .iter()
            .zip(proof.iter())
        {
            let (left_sibling, right_sibling) = self
                .native_gadget
                .cond_swap(layouter, is_right, &node, sibling)?;

            node = self
                .hash_chip
                .hash(layouter, &[left_sibling, right_sibling])?;
        }

        self.native_gadget.assert_equal(layouter, &node, set_root)?;

        Ok(())
    }
}

impl<F, H> MembershipInstructions<F> for MembershipGadget<F, H>
where
    F: PrimeField,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    type AssignedElement = AssignedNative<F>;
    type AssignedMemProof = [AssignedNative<F>; TREE_HEIGHT as usize];
    type AssignedSet = AssignedNative<F>;

    fn is_in_set(
        &self,
        layouter: &mut impl Layouter<F>,
        val: &Self::AssignedElement,
        proof: &Self::AssignedMemProof,
        set: &Self::AssignedSet,
        in_set: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.verify_path(layouter, val, proof, set, in_set)?;
        Ok(in_set.clone())
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, H> FromScratch<F> for MembershipGadget<F, H>
where
    F: PrimeField,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
{
    type Config = (P2RDecompositionConfig, <H as FromScratch<F>>::Config);

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            native_gadget: NativeGadget::new_from_scratch(&config.0),
            hash_chip: H::new_from_scratch(&config.1),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_column: &Column<Instance>,
    ) -> Self::Config {
        (
            NativeGadget::configure_from_scratch(meta, instance_column),
            H::configure_from_scratch(meta, instance_column),
        )
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        NativeGadget::load_from_scratch(layouter, &config.0);
        H::load_from_scratch(layouter, &config.1);
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use halo2_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::Circuit,
    };
    use rand::rngs::OsRng;

    use super::*;
    use crate::{
        hash::poseidon::{cpu::Spec, poseidon_gadget::PoseidonGadget, P128Pow5T3},
        membership::cpu::{MembershipMt, MtPath},
        types::Bit,
        utils::circuit_modeling::circuit_to_json,
    };

    struct TestCircuit<F: PrimeField, H> {
        element: F,
        path: MtPath<F>,
        root: F,
        member: bool,
        _marker: PhantomData<H>,
    }

    impl<F, H> Circuit<F> for TestCircuit<F, H>
    where
        F: PrimeField,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        type Config = <MembershipGadget<F, H> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                element: F::default(),
                path: MtPath {
                    sibling_nodes: [F::ZERO; TREE_HEIGHT as usize],
                },
                root: F::default(),
                member: false,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance_column = meta.instance_column();
            MembershipGadget::<F, H>::configure_from_scratch(meta, &instance_column)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let membership_proof = MembershipGadget::<F, H>::new_from_scratch(&config);
            MembershipGadget::<F, H>::load_from_scratch(&mut layouter, &config);

            let assigned_element = membership_proof
                .native_gadget
                .assign(&mut layouter, Value::known(self.element))?;
            let assigned_path = membership_proof.native_gadget.assign_many(
                &mut layouter,
                &self
                    .path
                    .sibling_nodes
                    .into_iter()
                    .map(Value::known)
                    .collect::<Vec<_>>(),
            )?;
            let assigned_root = membership_proof
                .native_gadget
                .assign(&mut layouter, Value::known(self.root))?;

            let is_in_set = membership_proof
                .native_gadget
                .assign(&mut layouter, Value::known(Bit(self.member)))?;

            let in_set = membership_proof.is_in_set(
                &mut layouter,
                &assigned_element,
                &(assigned_path.try_into().unwrap()),
                &assigned_root,
                &is_in_set,
            )?;

            membership_proof
                .native_gadget
                .assert_equal(&mut layouter, &is_in_set, &in_set)?;
            Ok(())
        }
    }

    fn test_mt<F, H>(cost_model: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        let k: u32 = 14;

        let mut mt = MembershipMt::<F, H>::init();

        // Let's add 100 random elements
        for _ in 0..100 {
            mt.insert(F::random(OsRng));
        }

        mt.insert(F::ONE);

        [
            (F::ZERO, false, true, cost_model),
            (F::ZERO, true, false, false),
            (F::ONE, true, true, false),
            (F::ONE, false, false, false),
        ]
        .into_iter()
        .for_each(|(element, member, test_passes, cost_model)| {
            let circuit = TestCircuit {
                path: mt.get_path(&element),
                element,
                root: mt.root,
                member,
                _marker: PhantomData::<H>,
            };

            let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
            if test_passes {
                assert!(prover.verify().is_ok());
            } else {
                assert!(prover.verify().is_err());
            }

            if cost_model {
                circuit_to_json::<F>(k, "Membership chip", "verify set proof", &[&[]], circuit);
            }
        });
    }

    fn run_poseidon_test<F>(cost_model: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        P128Pow5T3: Spec<F, 3, 2>,
    {
        test_mt::<F, PoseidonGadget<F>>(cost_model)
    }

    #[test]
    fn test_mt_poseidon() {
        run_poseidon_test::<blstrs::Scalar>(true);
        run_poseidon_test::<halo2curves::pasta::Fp>(false);
        run_poseidon_test::<halo2curves::pasta::Fq>(false);
    }
}
