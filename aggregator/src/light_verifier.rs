//! This file will not be merged. It is just a simple example to make sure
//! everything works so far.
//!
//! The actual aggregator examples will subsume this test.

#[cfg(test)]
pub(crate) mod tests {

    use std::{cmp::max, collections::BTreeMap};

    use ff::Field;
    use group::Group;
    use midnight_circuits::{
        field::{native::NB_ARITH_COLS, NativeChip, NativeConfig},
        hash::poseidon::{
            PoseidonChip, PoseidonConfig, NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS,
        },
        instructions::{
            hash::{HashCPU, HashInstructions},
            AssignmentInstructions, PublicInputInstructions,
        },
        testing_utils::FromScratch,
        types::{ComposableChip, Instantiable},
        verifier::{Accumulator, AssignedAccumulator, AssignedVk, SelfEmulation, VerifierGadget},
    };
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{
            create_proof, keygen_pk, keygen_vk_with_k, prepare, Circuit, ConstraintSystem, Error,
        },
        poly::{
            kzg::{params::ParamsKZG, KZGCommitmentScheme},
            EvaluationDomain,
        },
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use crate::{
        light_fiat_shamir::LightPoseidonFS,
        light_self_emulation::{FakeCurveChip, LightBlstrsEmulation},
    };

    type S = LightBlstrsEmulation;

    type F = <S as SelfEmulation>::F;
    type C = <S as SelfEmulation>::C;

    type E = <S as SelfEmulation>::Engine;

    const NB_INNER_INSTANCES: usize = 1;

    #[derive(Clone, Debug, Default)]
    pub struct InnerCircuit {
        poseidon_preimage: Value<[F; 2]>,
    }

    impl InnerCircuit {
        pub fn from_witness(witness: [F; 2]) -> Self {
            Self {
                poseidon_preimage: Value::known(witness),
            }
        }
    }

    impl Circuit<F> for InnerCircuit {
        type Config = <PoseidonChip<F> as FromScratch<F>>::Config;

        type FloorPlanner = SimpleFloorPlanner;

        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            PoseidonChip::configure_from_scratch(
                meta,
                &[committed_instance_column, instance_column],
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = NativeChip::new_from_scratch(&config.0);
            let poseidon_chip = PoseidonChip::new_from_scratch(&config);
            PoseidonChip::load_from_scratch(&mut layouter, &config);

            let inputs = native_gadget
                .assign_many(&mut layouter, &self.poseidon_preimage.transpose_array())?;
            let output = poseidon_chip.hash(&mut layouter, &inputs)?;

            native_gadget.constrain_as_public_input(&mut layouter, &output)
        }
    }

    #[derive(Clone, Debug)]
    pub struct TestCircuit {
        inner_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>), // (domain, cs, vk_repr)
        inner_committed_instance: C,
        inner_instances: Value<[F; NB_INNER_INSTANCES]>,
        inner_proof: Value<Vec<u8>>,
    }

    impl Circuit<F> for TestCircuit {
        type Config = (NativeConfig, PoseidonConfig<F>);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let nb_advice_cols = max(NB_ARITH_COLS, NB_POSEIDON_ADVICE_COLS);
            let nb_fixed_cols = max(NB_ARITH_COLS + 4, NB_POSEIDON_FIXED_COLS);

            let advice_columns: Vec<_> =
                (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
            let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();

            let native_config = NativeChip::configure(
                meta,
                &(
                    advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                    fixed_columns[..NB_ARITH_COLS + 4].try_into().unwrap(),
                    [committed_instance_column, instance_column],
                ),
            );

            let poseidon_config = PoseidonChip::configure(
                meta,
                &(
                    advice_columns[..NB_POSEIDON_ADVICE_COLS]
                        .try_into()
                        .unwrap(),
                    fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
                ),
            );

            (native_config, poseidon_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
            let poseidon_chip = PoseidonChip::new(&config.1, &native_chip);
            let fake_curve_chip = FakeCurveChip::<C>::new(&native_chip);

            let verifier_chip =
                VerifierGadget::<S>::new(&fake_curve_chip, &native_chip, &poseidon_chip);

            let assigned_inner_vk: AssignedVk<S> = verifier_chip.assign_vk_as_public_input(
                &mut layouter,
                "inner_vk",
                &self.inner_vk.0,
                &self.inner_vk.1,
                self.inner_vk.2,
            )?;

            let assigned_committed_instance =
                fake_curve_chip.assign_fixed(&mut layouter, self.inner_committed_instance)?;

            let assigned_inner_pi =
                native_chip.assign_many(&mut layouter, &self.inner_instances.transpose_array())?;

            let inner_proof_acc = verifier_chip.prepare(
                &mut layouter,
                &assigned_inner_vk,
                &[("com_instance", assigned_committed_instance)],
                &[&assigned_inner_pi],
                self.inner_proof.clone(),
            )?;

            verifier_chip.constrain_as_public_input(&mut layouter, &inner_proof_acc)?;

            fake_curve_chip.finalize()
        }
    }

    #[test]
    fn test_verify_proof() {
        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

        let inner_k = 10;
        let inner_params = ParamsKZG::unsafe_setup(inner_k, &mut rng);
        let inner_vk = keygen_vk_with_k(&inner_params, &InnerCircuit::default(), inner_k).unwrap();
        let inner_pk = keygen_pk(inner_vk.clone(), &InnerCircuit::default()).unwrap();

        let preimage = [F::random(&mut rng), F::random(&mut rng)];
        let output = <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage);
        let inner_public_inputs = vec![output];

        let inner_proof = {
            let mut transcript = CircuitTranscript::<LightPoseidonFS<F>>::init();
            create_proof::<
                F,
                KZGCommitmentScheme<E>,
                CircuitTranscript<LightPoseidonFS<F>>,
                InnerCircuit,
            >(
                &inner_params,
                &inner_pk,
                &[InnerCircuit::from_witness(preimage)],
                1,
                &[&[&[], &inner_public_inputs]],
                &mut rng,
                &mut transcript,
            )
            .unwrap_or_else(|_| panic!("Problem creating the inner proof"));
            transcript.finalize()
        };

        let inner_dual_msm = {
            let mut transcript =
                CircuitTranscript::<LightPoseidonFS<F>>::init_from_bytes(&inner_proof);
            prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<LightPoseidonFS<F>>>(
                &inner_vk,
                &[&[C::identity()]],
                &[&[&inner_public_inputs]],
                &mut transcript,
            )
            .expect("Problem preparing the inner proof")
        };

        let mut fixed_bases = BTreeMap::new();
        fixed_bases.insert(String::from("com_instance"), C::identity());
        fixed_bases.extend(midnight_circuits::verifier::fixed_bases::<S>(
            "inner_vk", &inner_vk,
        ));

        let mut inner_acc: Accumulator<S> = inner_dual_msm.clone().into();
        inner_acc.extract_fixed_bases(&fixed_bases);

        assert!(inner_dual_msm.check(&inner_params.verifier_params()));
        assert!(inner_acc.check(&inner_params.s_g2().into(), &fixed_bases));

        // The inner proof is ready.
        // Now, let us make a proof that we know an inner proof.

        const K: u32 = 11;

        let mut public_inputs = AssignedVk::<S>::as_public_input(&inner_vk);
        public_inputs.extend(AssignedAccumulator::as_public_input(&inner_acc));

        let circuit = TestCircuit {
            inner_vk: (
                inner_vk.get_domain().clone(),
                inner_vk.cs().clone(),
                Value::known(inner_vk.transcript_repr()),
            ),
            inner_committed_instance: C::identity(),
            inner_instances: Value::known([output]),
            inner_proof: Value::known(inner_proof),
        };

        dbg!(
            midnight_proofs::dev::cost_model::from_circuit_to_circuit_model::<F, _, 48, 32>(
                None, &circuit, 0
            )
        );

        let prover =
            MockProver::run(K, &circuit, vec![vec![], public_inputs]).expect("MockProver failed");
        prover.assert_satisfied();
    }
}
