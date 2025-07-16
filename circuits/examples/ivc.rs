//! Incrementally Verifiable Computation (IVC) of a simple function that
//! increments a counter.
//!
//! DO NOT add this example to the CI as it is slow.

use std::{collections::BTreeMap, time::Instant};

use halo2curves::{ff::Field, group::Group};
use midnight_circuits::{
    ecc::{
        curves::CircuitCurve,
        foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
    },
    field::{
        decomposition::{
            chip::{P2RDecompositionChip, P2RDecompositionConfig},
            pow2range::Pow2RangeChip,
        },
        foreign::FieldChip,
        native::NB_ARITH_COLS,
        NativeChip, NativeConfig, NativeGadget,
    },
    hash::poseidon::{
        PoseidonChip, PoseidonConfig, PoseidonState, NB_POSEIDON_ADVICE_COLS,
        NB_POSEIDON_FIXED_COLS,
    },
    instructions::*,
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedNative, ComposableChip, Instantiable},
    verifier::{
        self, Accumulator, AssignedAccumulator, AssignedVk, BlstrsEmulation, Msm, SelfEmulation,
        VerifierGadget,
    },
};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{create_proof, keygen_pk, keygen_vk_with_k, prepare, Circuit, ConstraintSystem, Error},
    poly::{kzg::KZGCommitmentScheme, EvaluationDomain},
    transcript::{CircuitTranscript, Transcript},
};
use rand::rngs::OsRng;

type S = BlstrsEmulation;

type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;

type E = <S as SelfEmulation>::Engine;
type CBase = <C as CircuitCurve>::Base;

type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

#[derive(Clone, Debug)]
pub struct IvcCircuit {
    self_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>), // (domain, cs, vk_repr)
    // We use a simple application function that increases a counter.
    prev_state: Value<F>,
    prev_proof: Value<Vec<u8>>,
    prev_acc: Value<Accumulator<S>>,
}

fn configure_ivc_circuit(
    meta: &mut ConstraintSystem<F>,
) -> (
    NativeConfig,
    P2RDecompositionConfig,
    ForeignEccConfig<C>,
    PoseidonConfig<F>,
) {
    let nb_advice_cols = nb_foreign_ecc_chip_columns::<F, C, C, NG>();
    let nb_fixed_cols = NB_ARITH_COLS + 4;

    let advice_columns: Vec<_> = (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
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
    let core_decomp_config = {
        let pow2_config = Pow2RangeChip::configure(meta, &advice_columns[1..NB_ARITH_COLS]);
        P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2_config))
    };

    let base_config = FieldChip::<F, CBase, C, NG>::configure(meta, &advice_columns);
    let curve_config =
        ForeignEccChip::<F, C, C, NG, NG>::configure(meta, &base_config, &advice_columns);

    let poseidon_config = PoseidonChip::configure(
        meta,
        &(
            advice_columns[..NB_POSEIDON_ADVICE_COLS]
                .try_into()
                .unwrap(),
            fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
        ),
    );

    (
        native_config,
        core_decomp_config,
        curve_config,
        poseidon_config,
    )
}

impl Circuit<F> for IvcCircuit {
    type Config = (
        NativeConfig,
        P2RDecompositionConfig,
        ForeignEccConfig<C>,
        PoseidonConfig<F>,
    );
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        configure_ivc_circuit(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
        let core_decomp_chip = P2RDecompositionChip::new(&config.1, &16);
        let scalar_chip = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
        let curve_chip = { ForeignEccChip::new(&config.2, &scalar_chip, &scalar_chip) };
        let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

        let verifier_chip = VerifierGadget::new(&curve_chip, &scalar_chip, &poseidon_chip);

        core_decomp_chip.load(&mut layouter)?;

        let self_vk_name = "self_vk";
        let (self_domain, self_cs, self_vk_value) = &self.self_vk;
        let assigned_self_vk: AssignedVk<S> = verifier_chip.assign_vk_as_public_input(
            &mut layouter,
            self_vk_name,
            self_domain,
            self_cs,
            *self_vk_value,
        )?;

        // Witness a previous state and update it in-circuit.
        // Then, constrain the new state as a public input.
        let prev_state = scalar_chip.assign(&mut layouter, self.prev_state)?;
        let next_state = scalar_chip.add_constant(&mut layouter, &prev_state, F::ONE)?;
        scalar_chip.constrain_as_public_input(&mut layouter, &next_state)?;

        // Witness a proof and an accumulator that ensure the validity of `prev_state`.
        let prev_acc = {
            let mut fixed_base_names = vec![String::from("com_instance")];
            fixed_base_names.extend(verifier::fixed_base_names::<S>(
                self_vk_name,
                self_cs.num_fixed_columns() + self_cs.num_selectors(),
                self_cs.permutation().columns.len(),
            ));
            AssignedAccumulator::assign(
                &mut layouter,
                &curve_chip,
                &scalar_chip,
                1,
                1,
                &[],
                &fixed_base_names,
                self.prev_acc.clone(),
            )?
        };

        let id_point = curve_chip.assign_fixed(&mut layouter, C::identity())?;

        let assigned_pi = [
            verifier_chip.as_public_input(&mut layouter, &assigned_self_vk)?,
            vec![prev_state.clone()],
            verifier_chip.as_public_input(&mut layouter, &prev_acc)?,
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

        // Verify a witnessed proof that ensures the validity of `prev_state`.
        // The proof is valid iff `proof_acc` satisfies the invariant.
        let mut proof_acc = verifier_chip.prepare(
            &mut layouter,
            &assigned_self_vk,
            &[("com_instance", id_point)],
            &[&assigned_pi],
            self.prev_proof.clone(),
        )?;

        // If `prev_state` is genesis, we allow the prover to change the (probably
        // invalid) accumulator by a default accumulator that satisfies the invariant.
        let is_genesis = scalar_chip.is_zero(&mut layouter, &prev_state)?;
        let is_not_genesis = scalar_chip.not(&mut layouter, &is_genesis)?;

        AssignedAccumulator::scale_by_bit(
            &mut layouter,
            &scalar_chip,
            &is_not_genesis,
            &mut proof_acc,
        )?;

        proof_acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;

        // Accumulate the `proof_acc` with the previous witnessed accumulator.
        // `next_acc` will satisfy the invariant iff both `proof_acc` and `prev_acc` do.
        let mut next_acc = proof_acc.accumulate(
            &mut layouter,
            &verifier_chip,
            &scalar_chip,
            &poseidon_chip,
            &prev_acc,
        )?;

        // Finally, collapse the resulting accumulator and constraint it as public.
        next_acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;

        verifier_chip.constrain_as_public_input(&mut layouter, &next_acc)
    }
}

fn main() {
    #[cfg(feature = "truncated-challenges")]
    let self_k = 18;

    #[cfg(not(feature = "truncated-challenges"))]
    let self_k = 19;

    let mut self_cs = ConstraintSystem::default();
    configure_ivc_circuit(&mut self_cs);
    let self_domain = EvaluationDomain::new(self_cs.degree() as u32, self_k);

    let default_ivc_circuit = IvcCircuit {
        self_vk: (self_domain.clone(), self_cs.clone(), Value::unknown()),
        prev_state: Value::unknown(),
        prev_proof: Value::unknown(),
        prev_acc: Value::unknown(),
    };

    let srs = filecoin_srs(self_k);

    let start = Instant::now();
    let vk = keygen_vk_with_k(&srs, &default_ivc_circuit, self_k).unwrap();
    let pk = keygen_pk(vk.clone(), &default_ivc_circuit).unwrap();
    println!("Computed vk and pk in {:?} s", start.elapsed());

    let mut fixed_bases = BTreeMap::new();
    fixed_bases.insert(String::from("com_instance"), C::identity());
    fixed_bases.extend(midnight_circuits::verifier::fixed_bases::<S>(
        "self_vk", &vk,
    ));
    let fixed_base_names = fixed_bases.keys().cloned().collect::<Vec<_>>();

    // This trivial accumulator must have a single base and scalar of F::ONE, and
    // the base has to be the default point of C. This is because when parsing
    // an empty proof, our transcript gadget places a default point on every
    // `read_point`. Note that the `base` is left untouched on during the
    // handling of genesis, because `scale_by_bit` only modifies the scalars.
    //
    // On the other hand, the scalar has to be F::ONE because it is the value
    // obtained after a `collapse` (the last step before constraining the acc as
    // a public input).
    let trivial_acc = Accumulator::<S>::new(
        Msm::new(&[C::default()], &[F::ONE], &BTreeMap::new()),
        Msm::new(
            &[C::default()],
            &[F::ONE],
            &fixed_base_names
                .iter()
                .map(|name| (name.clone(), F::ZERO))
                .collect(),
        ),
    );

    // Set the previous values for state (to genesis), proof and acc.
    let mut prev_state = F::ZERO;
    let mut prev_proof = vec![];
    let mut prev_acc = trivial_acc.clone();

    // Set the state (and acc) that we will prove (they are PI to the proof).
    let mut state = prev_state + F::ONE;
    let mut acc = trivial_acc;

    // Run the IVC loop.
    for i in 0..3 {
        let circuit = IvcCircuit {
            self_vk: (
                self_domain.clone(),
                self_cs.clone(),
                Value::known(vk.transcript_repr()),
            ),
            prev_state: Value::known(prev_state),
            prev_proof: Value::known(prev_proof.clone()),
            prev_acc: Value::known(prev_acc.clone()),
        };

        let mut public_inputs = AssignedVk::<S>::as_public_input(&vk);
        public_inputs.extend(AssignedNative::<F>::as_public_input(&state));
        public_inputs.extend(AssignedAccumulator::as_public_input(&acc));

        let start = Instant::now();
        let proof = {
            let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
            create_proof::<
                F,
                KZGCommitmentScheme<E>,
                CircuitTranscript<PoseidonState<F>>,
                IvcCircuit,
            >(
                &srs,
                &pk,
                &[circuit.clone()],
                1,
                &[&[&[], &public_inputs]],
                OsRng,
                &mut transcript,
            )
            .unwrap_or_else(|_| panic!("Problem creating the {i}-th IVC proof"));
            transcript.finalize()
        };
        println!("{i}-th IVC proof created in {:?}", start.elapsed());

        let proof_acc: Accumulator<S> = {
            let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&proof);
            let dual_msm =
                prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                    &vk,
                    &[&[C::identity()]],
                    &[&[&public_inputs]],
                    &mut transcript,
                )
                .expect("Verification failed");

            assert!(dual_msm.clone().check(&srs.verifier_params()));

            let mut proof_acc: Accumulator<S> = dual_msm.into();
            proof_acc.extract_fixed_bases(&fixed_bases);
            proof_acc.collapse();
            proof_acc
        };

        // Prepare the witnesses of the next iteration.
        prev_state = state;
        prev_proof = proof;
        prev_acc = acc.clone();

        // If `acc` satisfies the invariant and `proof` is valid, we know that `state`
        // must be valid. We can asset the validity of both at the same time by
        // accumulating them first.
        let mut accumulated = proof_acc.accumulate(&acc);
        accumulated.collapse();

        assert!(
            accumulated.check(&srs.s_g2().into(), &fixed_bases),
            "IVC acc verification failed"
        );

        println!("Asserted validity of state {:?}", state);

        // Set the new goals (public inputs) for the next iteration.
        state += F::ONE;
        acc = accumulated;
    }
}
