// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! In-circuit implementation of Succinct Key-Value Map Representation Using
//! Merkle Trees
use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    midnight_proofs::plonk::{Column, ConstraintSystem, Instance},
};

use crate::{
    instructions::{
        map::{MapCPU, MapInstructions},
        HashInstructions, NativeInstructions,
    },
    map::cpu::{MapMt, TREE_HEIGHT},
    types::AssignedNative,
};

#[derive(Clone, Debug)]
/// State of [MapGadget], containing the assigned succinct representation and
/// the unassigned map.
struct State<F, H>
where
    F: PrimeField,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    succinct_repr: AssignedNative<F>,
    map: Box<MapMt<F, H>>,
}

#[derive(Clone, Debug)]
/// Gadget for proving `insert` and `get` instructions in a map.
pub struct MapGadget<F, N, H>
where
    F: PrimeField,
    N: NativeInstructions<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    native_gadget: N,
    hash_chip: H,
    state: Option<State<F, H>>,
}

impl<F, N, H> MapInstructions<F, AssignedNative<F>, AssignedNative<F>> for MapGadget<F, N, H>
where
    F: PrimeField,
    N: NativeInstructions<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    type MapCPU = MapMt<F, H>;

    fn init(
        &mut self,
        layouter: &mut impl Layouter<F>,
        map: Value<MapMt<F, H>>,
    ) -> Result<(), Error> {
        let mut init_map = MapMt::new(&F::ZERO);
        let succinct_repr_value = map.map(|v| {
            let repr = v.succinct_repr();
            init_map = v;
            repr
        });

        self.state = Some(State {
            succinct_repr: self.native_gadget.assign(layouter, succinct_repr_value)?,
            map: Box::new(init_map),
        });

        Ok(())
    }

    fn succinct_repr(&self) -> AssignedNative<F> {
        self.state().succinct_repr.clone()
    }

    fn insert(
        &mut self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedNative<F>,
        value: &AssignedNative<F>,
    ) -> Result<(), Error> {
        // First we get the path for the current value of `key`, and prove its
        // correctness.
        let current_value = key.value().map(|key| self.state().map.get(key));
        let assigned_current_value = self.native_gadget.assign(layouter, current_value)?;

        let path = self.get_path(layouter, key)?;
        self.verify_path(layouter, key, &assigned_current_value, &path)?;

        // Next, we update the state (succinct_repr and map), and verify that the same
        // path is valid with the inserted value.
        self.update_state(layouter, key, value)?;
        self.verify_path(layouter, key, value, &path)?;

        Ok(())
    }

    fn get(
        &self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        let value = key.value().map(|key| self.state().map.get(key));
        let assigned_value = self.native_gadget.assign(layouter, value)?;

        let path = self.get_path(layouter, key)?;
        self.verify_path(layouter, key, &assigned_value, &path)?;

        Ok(assigned_value)
    }
}

impl<F, N, H> MapGadget<F, N, H>
where
    F: PrimeField,
    N: NativeInstructions<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>>,
{
    /// Create a map gadget
    pub fn new(native_gadget: &N, hash_chip: &H) -> Self {
        Self {
            native_gadget: native_gadget.clone(),
            hash_chip: hash_chip.clone(),
            state: None::<State<F, H>>,
        }
    }

    /// Returns a reference to the state.
    ///
    /// # Panics
    /// This function panics if the [MapGadget] has not been initialised.
    fn state(&self) -> &State<F, H> {
        self.state
            .as_ref()
            .expect("Map gadget must be initialised before usage.")
    }

    /// Update the state by inserting a new value `(value, key)` pair into the
    /// map and update the assigned succinct_repr accordingly.
    ///
    /// # Panics
    /// This function panics if the [MapGadget] has not been initialised.
    fn update_state(
        &mut self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedNative<F>,
        value: &AssignedNative<F>,
    ) -> Result<(), Error> {
        let state = self
            .state
            .as_mut()
            .expect("Map gadget must be initialised before usage.");

        let new_root = key.value().zip(value.value()).map(|(key, value)| {
            state.map.insert(key, value);
            state.map.succinct_repr()
        });

        let assigned_new_root: AssignedNative<F> = self.native_gadget.assign(layouter, new_root)?;
        state.succinct_repr = assigned_new_root.clone();

        self.state = Some(state.clone());

        Ok(())
    }

    /// Returns the assigned path for the given `key` pair.
    ///
    /// # Warning
    /// This function does not prove that the path is correct. To guarantee its
    /// correctness, one should call [Self::verify_path].
    fn get_path(
        &self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedNative<F>,
    ) -> Result<[AssignedNative<F>; TREE_HEIGHT as usize], Error> {
        // First we assign the MT path.
        let path = key
            .value()
            .map(|key| self.state().map.get_path(key))
            .transpose_array();
        Ok(self
            .native_gadget
            .assign_many(layouter, &path)?
            .try_into()
            .unwrap())
    }

    /// Verify a `proof` is correct w.r.t. the `(key, value)` pair.
    fn verify_path(
        &self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedNative<F>,
        value: &AssignedNative<F>,
        proof: &[AssignedNative<F>; TREE_HEIGHT as usize],
    ) -> Result<(), Error> {
        let zero = self.native_gadget.assign_fixed(layouter, F::ZERO)?;
        let path = self.hash_chip.hash(layouter, &[key.clone(), zero])?;
        let path_as_bits = self
            .native_gadget
            .assigned_to_le_bits(layouter, &path, None, true)?;

        let mut node: AssignedNative<F> = value.clone();

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

        self.native_gadget
            .assert_equal(layouter, &node, &self.state().succinct_repr)?;

        Ok(())
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, N, H> FromScratch<F> for MapGadget<F, N, H>
where
    F: PrimeField,
    N: NativeInstructions<F> + FromScratch<F>,
    H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
{
    type Config = (<N as FromScratch<F>>::Config, <H as FromScratch<F>>::Config);

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            native_gadget: N::new_from_scratch(&config.0),
            hash_chip: H::new_from_scratch(&config.1),
            state: None::<State<F, H>>,
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        (
            N::configure_from_scratch(meta, instance_columns),
            H::configure_from_scratch(meta, instance_columns),
        )
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        N::load_from_scratch(layouter, &config.0);
        H::load_from_scratch(layouter, &config.1);
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use ff::FromUniformBytes;
    use midnight_proofs::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::Circuit,
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
        hash::poseidon::{constants::PoseidonField, PoseidonChip},
        map::cpu::MapMt,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Debug)]
    enum MapTests {
        Get,
        Insert,
    }

    struct TestCircuit<F, N, H>
    where
        F: PrimeField,
        N: NativeInstructions<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        map: Value<MapMt<F, H>>,
        key: Value<F>,
        value: Value<F>,
        mode: MapTests,
        _marker: PhantomData<N>,
    }

    impl<F, N, H> Circuit<F> for TestCircuit<F, N, H>
    where
        F: PrimeField,
        N: NativeInstructions<F> + FromScratch<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        type Config = <MapGadget<F, N, H> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                key: Value::unknown(),
                value: Value::unknown(),
                map: Value::unknown(),
                mode: MapTests::Get,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            MapGadget::<F, N, H>::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = N::new_from_scratch(&config.0);
            let poseidon_gadget = H::new_from_scratch(&config.1);
            let mut map_gadget = MapGadget::<F, N, H>::new(&native_gadget, &poseidon_gadget);
            MapGadget::<F, N, H>::load_from_scratch(&mut layouter, &config);

            map_gadget.init(&mut layouter, self.map.clone())?;

            let assigned_key: AssignedNative<F> = native_gadget.assign(&mut layouter, self.key)?;
            let assigned_value: AssignedNative<F> =
                native_gadget.assign(&mut layouter, self.value)?;

            native_gadget.constrain_as_public_input(&mut layouter, &map_gadget.succinct_repr())?;

            match self.mode {
                MapTests::Get => {
                    let value = map_gadget.get(&mut layouter, &assigned_key)?;
                    map_gadget.native_gadget.assert_equal(
                        &mut layouter,
                        &value,
                        &assigned_value,
                    )?;
                }
                MapTests::Insert => {
                    map_gadget.insert(&mut layouter, &assigned_key, &assigned_value)?;

                    native_gadget
                        .constrain_as_public_input(&mut layouter, &map_gadget.succinct_repr())?;
                }
            }

            Ok(())
        }
    }

    fn test_map<F, N, H>(cost_model: bool)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        N: NativeInstructions<F> + FromScratch<F>,
        H: HashInstructions<F, AssignedNative<F>, AssignedNative<F>> + FromScratch<F>,
    {
        let k: u32 = 15;
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);

        let mut mt = MapMt::<F, H>::new(&F::ZERO);

        // Let's add 100 random elements
        for _ in 0..100 {
            mt.insert(&F::random(&mut rng), &F::random(&mut rng));
        }

        mt.insert(&F::ONE, &F::ONE);

        [
            (F::ZERO, F::ZERO, true, MapTests::Get, cost_model),
            (F::ZERO, F::ONE, false, MapTests::Get, false),
            (F::ONE, F::ONE, true, MapTests::Get, false),
            (F::random(&mut rng), F::ZERO, true, MapTests::Get, false),
            (F::ONE, F::ZERO, false, MapTests::Get, false),
            (
                F::ONE,
                F::random(&mut rng),
                true,
                MapTests::Insert,
                cost_model,
            ),
            (
                F::ONE,
                F::random(&mut rng),
                false,
                MapTests::Insert,
                cost_model,
            ),
        ]
        .into_iter()
        .for_each(|(key, value, test_passes, mode, cost_model)| {
            let updated_map = if test_passes {
                let mut map = mt.clone();
                map.insert(&key, &value);
                map
            } else {
                mt.clone()
            };

            let mut pi = vec![mt.root];
            pi.push(updated_map.root);

            let circuit = TestCircuit {
                map: Value::known(mt.clone()),
                key: Value::known(key),
                value: Value::known(value),
                mode: mode.clone(),
                _marker: PhantomData::<N>,
            };

            let prover = MockProver::run(k, &circuit, vec![vec![], pi.clone()]).unwrap();
            if test_passes {
                assert!(prover.verify().is_ok());
            } else {
                assert!(prover.verify().is_err());
            }

            if cost_model {
                circuit_to_json::<F>(k, "Map gadget", &format!("{:?}", mode), pi.len(), circuit);
            }
        });
    }

    fn run_poseidon_test<F: PoseidonField + ff::FromUniformBytes<64> + Ord>(cost_model: bool) {
        test_map::<F, NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>, PoseidonChip<F>>(
            cost_model,
        )
    }

    #[test]
    fn test_map_poseidon() {
        run_poseidon_test::<midnight_curves::Fq>(true);
    }
}
