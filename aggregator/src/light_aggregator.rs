//! A light aggregator that can take k finished PLONK proofs and produce a
//! meta proof that only includes the commitments of the k proofs (all the
//! scalars are optimized away). This is achieved by in-circuit verifying the
//! native part of every proof.
//!
//! More concretely, a PLONK proof consists of a bunch of scalars and group
//! elements. The proof is valid iff:
//!
//!  1. The scalars and group elements are consistent with the Fiat-Shamir
//!     schedule (some of the scalars are the result of hashing other scalars
//!     and group elements).
//!
//!  2. The scalars satisfy a system of polynomial equations.
//!
//!  3. The evaluation of a Dual MSM (whose bases involve the group elements in
//!     the proof and the group elements in the verifying key and whose scalars
//!     are derived from the proof) satisfies the pairing invariant w.r.t. the
//!     SRS element \[𝜏\]₂.
//!
//! Notably, conditions 1 and 2 can be expressed "natively" in a PLONK circuit
//! with the same base curve as the original proof (the "inner" proof), if a
//! SNARK-friendly hash function like Poseidon is used for the Fiat-Shamir of
//! the inner proof.
//!
//! Our light aggregator verifies steps 1 and 2 in-circuit for all the k inner
//! proofs and computes in-circuit the scalars of the combined Dual MSM of
//! step 3 (yes, all k inner proofs can be combined into a single Dual MSM).
//! These Dual MSM scalars are then committed into a single group element σ
//! with [midnight_proofs::plonk::commit_to_instances]. Therefore, the light
//! aggregator circuit guarantees that steps 1 and 2 are performed correctly and
//! that σ (passed as a committed instance) is the correct commitment (with
//! Lagrange bases) to the Dual MSM scalars.
//!
//! This allows us to remove all the scalars from all the k inner proofs. We
//! are left with the group elements of every proof (and an extra PLONK proof
//! for the above circuit). What remains is to check step 3 (for all inner
//! proofs at once) by verifying that the Dual MSM evaluates to something that
//! satisfies the pairing invariant. However, since the Dual MSM scalars are in
//! committed form (in σ), the verifier cannot do this by themself. Instead,
//! the prover will provide the evaluation C of the Dual MSM (actually, of the
//! RHS of the Dual MSM, as the LHS part can be directly evaluated by the
//! verifier). After checking that evaluated Dual MSM satisfies the invariant
//! (trusting C as the evaluation of its RHS), the only thing that remains is to
//! verify the validity of C. This is done via an IPA proof for relation
//! PoK { s in F^l : <s, LAGRANGE_BASES> = σ /\ <s, DUAL_MSM_RHS_BASES> = C }.

use std::{collections::BTreeMap, io};

use blake2b_simd::State as Blake2bState;
use group::{prime::PrimeCurveAffine, Group};
use halo2curves::{pairing::Engine, serde::SerdeObject};
use midnight_circuits::{
    field::{
        native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
        AssignedNative, NativeChip, NativeConfig,
    },
    hash::poseidon::{
        PoseidonChip, PoseidonConfig, NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS,
    },
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{ComposableChip, Instantiable},
    verifier::{
        Accumulator, AssignedAccumulator, AssignedMsm, AssignedVk, Msm, SelfEmulation,
        VerifierGadget,
    },
};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        self, commit_to_instances, create_proof, keygen_pk, keygen_vk, prepare, Circuit,
        ConstraintSystem, Error,
    },
    poly::{
        commitment::Params,
        kzg::{
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
    utils::{helpers::ProcessedSerdeObject, SerdeFormat},
};
use rand::{CryptoRng, RngCore};

use crate::{
    inner_product_argument::{ipa_prove, ipa_verify, IpaProof},
    light_fiat_shamir::LightPoseidonFS,
    light_self_emulation::{FakeCurveChip, LightBlstrsEmulation},
};

// BLS12-381 is hard-coded here as the underlying curve of the PLONK proofs.
// This is for the sake of simplicity, since we need to configure and
// instantiate a chip, which would require extra traits that do not exist in
// order to do it generically.

type S = LightBlstrsEmulation;

// type F = <S as SelfEmulation>::F;
// type C = <S as SelfEmulation>::C;
// type E = <S as SelfEmulation>::Engine;
type F = midnight_curves::Fq;
type C = midnight_curves::G1Projective;
type E = midnight_curves::Bls12;

type VerifyingKey = plonk::VerifyingKey<F, KZGCommitmentScheme<E>>;
type ProvingKey = plonk::ProvingKey<F, KZGCommitmentScheme<E>>;

/// A light aggregator of KZG-based proofs over BLS12-381.
/// The internal Fiat-Shamir of proofs must have been performed with Poseidon.
///
/// This first version can only aggregate circuits with the same vk,
/// described by (domain, cs, vk_repr).
#[derive(Clone, Debug)]
pub struct LightAggregator<const NB_PROOFS: usize> {
    inner_vk: VerifyingKey,
    aggregator_vk: VerifyingKey,
    aggregator_pk: ProvingKey,
    lagrange_commitments: Vec<C>,
}

/// The type of an aggregated proof (of NB_PROOFS statements).
#[derive(Clone, Debug)]
pub struct MetaProof<const NB_PROOFS: usize> {
    proof: Vec<u8>,
    acc_lhs: Msm<S>,
    acc_rhs_evaluated: C, // The validity of this will be guaranteed by an IPA proof
    acc_rhs_bases: Vec<C>,
    acc_rhs_scalars_committed: C,
    ipa_proof: IpaProof<C>,
}

impl<const NB_PROOFS: usize> MetaProof<NB_PROOFS> {
    /// Writes the meta proof to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_all(&(self.proof.len() as u64).to_le_bytes())?;
        writer.write_all(&self.proof)?;

        writer.write_all(&(self.acc_lhs.bases().len() as u64).to_le_bytes())?;
        (self.acc_lhs.bases().iter()).try_for_each(|p| p.write(writer, format))?;
        (self.acc_lhs.scalars().iter()).try_for_each(|s| s.write_raw(writer))?;
        assert!(self.acc_lhs.fixed_base_scalars().is_empty());

        self.acc_rhs_evaluated.write(writer, format)?;

        writer.write_all(&(self.acc_rhs_bases.len() as u64).to_le_bytes())?;
        (self.acc_rhs_bases.iter()).try_for_each(|p| p.write(writer, format))?;

        self.acc_rhs_scalars_committed.write(writer, format)?;

        self.ipa_proof.write(writer, format)
    }

    /// Reads a meta proof from a buffer.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut bytes = [0u8; 8];

        reader.read_exact(&mut bytes)?;
        let mut proof = vec![0u8; u64::from_le_bytes(bytes) as usize];
        reader.read_exact(&mut proof)?;

        reader.read_exact(&mut bytes)?;
        let n = u64::from_le_bytes(bytes);
        let bases = ((0..n).map(|_| C::read(reader, format))).collect::<io::Result<Vec<_>>>()?;
        let scalars = ((0..n).map(|_| F::read_raw(reader))).collect::<io::Result<Vec<_>>>()?;
        let acc_lhs = Msm::new(&bases, &scalars, &BTreeMap::new());

        let acc_rhs_evaluated = C::read(reader, format)?;

        reader.read_exact(&mut bytes)?;
        let n = u64::from_le_bytes(bytes);
        let acc_rhs_bases =
            ((0..n).map(|_| C::read(reader, format))).collect::<io::Result<Vec<_>>>()?;

        let acc_rhs_scalars_committed = C::read(reader, format)?;

        let ipa_proof = IpaProof::read(reader, format)?;

        Ok(Self {
            proof,
            acc_lhs,
            acc_rhs_evaluated,
            acc_rhs_bases,
            acc_rhs_scalars_committed,
            ipa_proof,
        })
    }
}

#[derive(Clone, Debug)]
struct AggregatorCircuit<const NB_PROOFS: usize> {
    // This first version can only aggregate circuits with the same vk,
    // described by (domain, cs, vk_repr).
    #[allow(clippy::type_complexity)]
    inner_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>),
    // TODO: This version is limited to circuits with exactly 2 public inputs.
    // This will be generalized in subsequent PRs.
    instances: Value<[[F; 2]; NB_PROOFS]>,
    proofs: [Value<Vec<u8>>; NB_PROOFS],
}

impl<const NB_PROOFS: usize> Circuit<F> for AggregatorCircuit<NB_PROOFS> {
    type Config = (NativeConfig, PoseidonConfig<F>);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let nb_advice_cols = std::cmp::max(NB_ARITH_COLS, NB_POSEIDON_ADVICE_COLS);
        let nb_fixed_cols = std::cmp::max(NB_ARITH_FIXED_COLS, NB_POSEIDON_FIXED_COLS);

        let advice_columns: Vec<_> = (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
        let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_columns[..NB_ARITH_FIXED_COLS].try_into().unwrap(),
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
        let scalar_chip = NativeChip::new(&config.0, &());
        let sponge_chip = PoseidonChip::new(&config.1, &scalar_chip);
        let fake_curve_chip = FakeCurveChip::<C>::new(&scalar_chip);

        let verifier_chip = VerifierGadget::new(&fake_curve_chip, &scalar_chip, &sponge_chip);

        let assigned_inner_vk: AssignedVk<S> = verifier_chip.assign_vk_as_public_input(
            &mut layouter,
            "inner_vk",
            &self.inner_vk.0,
            &self.inner_vk.1,
            self.inner_vk.2,
        )?;

        let identity_point = fake_curve_chip.assign_fixed(&mut layouter, C::identity())?;

        let proof_accs = (self.instances.transpose_array().iter())
            .zip(self.proofs.iter())
            .enumerate()
            .map(|(i, (instances, proof))| {
                let assigned_instances: Vec<AssignedNative<F>> = instances
                    .transpose_array()
                    .iter()
                    .map(|instance| scalar_chip.assign_as_public_input(&mut layouter, *instance))
                    .collect::<Result<Vec<_>, Error>>()?;

                verifier_chip.prepare(
                    &mut layouter,
                    &assigned_inner_vk,
                    &[(&com_instance_name::<NB_PROOFS>(i), identity_point.clone())],
                    &[&assigned_instances],
                    proof.clone(),
                )
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let acc = AssignedAccumulator::<S>::accumulate(
            &mut layouter,
            &verifier_chip,
            &scalar_chip,
            &sponge_chip,
            &proof_accs,
        )?;

        verifier_chip.constrain_acc_as_public_input_with_committed_scalars(&mut layouter, &acc)?;

        // It is very important to call finalize in order to make sure all witnessed
        // points were at some point constrained as public inputs.
        fake_curve_chip.finalize()
    }
}

impl<const NB_PROOFS: usize> LightAggregator<NB_PROOFS> {
    /// Initializes a new proof light aggregator for circuits of the given inner
    /// vk.
    ///
    /// # Warning
    ///
    /// This function may downgrade the provided `srs` to adjust it to the
    /// aggregator circuit size.
    pub fn init(srs: &mut ParamsKZG<E>, inner_vk: &VerifyingKey) -> Result<Self, Error> {
        let default_aggregator_circuit = AggregatorCircuit::<NB_PROOFS> {
            inner_vk: (
                inner_vk.get_domain().clone(),
                inner_vk.cs().clone(),
                Value::unknown(),
            ),
            instances: Value::unknown(),
            proofs: vec![Value::unknown(); NB_PROOFS].try_into().unwrap(),
        };

        // TODO: Remove, we are hardcoding BLS constants here.
        dbg!(
            midnight_proofs::dev::cost_model::from_circuit_to_circuit_model::<_, _, 48, 32>(
                None,
                &default_aggregator_circuit,
                0,
            )
        );

        srs.downsize_from_circuit(&default_aggregator_circuit);

        let nb_coms_per_proof = {
            let cs = inner_vk.cs();
            cs.num_fixed_columns()
                + cs.num_advice_columns()
                + cs.num_instance_columns()
                + cs.permutation().get_columns().len()
                + 3 * cs.lookups().len()
        };

        let aggregator_vk = keygen_vk(srs, &default_aggregator_circuit)?;
        let aggregator_pk = keygen_pk(aggregator_vk.clone(), &default_aggregator_circuit)?;

        Ok(Self {
            inner_vk: inner_vk.clone(),
            aggregator_vk,
            aggregator_pk,
            lagrange_commitments: srs.g_lagrange()[..(nb_coms_per_proof * NB_PROOFS)].to_vec(),
        })
    }

    /// Aggregates the given proofs (supposedly valid w.r.t the aggregator's
    /// inner vk and their corresponding public inputs).
    ///
    /// The provided srs must be the one used for the generation of all proofs.
    /// (Not necessarily in size, but must share the same toxic waste.)
    //  (This assumption is not strictly necessary, but simplifies the API.)
    ///
    /// # Errors
    ///
    /// If some of the provided proofs are invalid.
    pub fn aggregate_proofs(
        &self,
        srs: &ParamsKZG<E>,
        instances: &[Vec<F>; NB_PROOFS],
        proofs: &[Vec<u8>; NB_PROOFS],
        mut rng: impl RngCore + CryptoRng,
    ) -> Result<MetaProof<NB_PROOFS>, Error> {
        // We first verify all proofs off-circuit, to get the final batched accumulator,
        // which must be a public input of the aggregator circuit.
        let proof_accs: Vec<Accumulator<S>> = (proofs.iter())
            .zip(instances.iter())
            .enumerate()
            .map(|(i, (proof, proof_instances))| {
                let mut transcript =
                    CircuitTranscript::<LightPoseidonFS<F>>::init_from_bytes(proof);
                let dual_msm = plonk::prepare::<
                    F,
                    KZGCommitmentScheme<E>,
                    CircuitTranscript<LightPoseidonFS<F>>,
                >(
                    &self.inner_vk,
                    &[&[C::identity()]],
                    &[&[proof_instances]],
                    &mut transcript,
                )?;

                assert!(dual_msm.clone().check(&srs.verifier_params()));

                let mut fixed_bases = BTreeMap::new();
                fixed_bases.insert(com_instance_name::<NB_PROOFS>(i), C::identity());
                fixed_bases.extend(midnight_circuits::verifier::fixed_bases::<S>(
                    "inner_vk",
                    &self.inner_vk,
                ));

                let mut proof_acc: Accumulator<S> = dual_msm.into();
                proof_acc.extract_fixed_bases(&fixed_bases);
                Ok(proof_acc)
            })
            .collect::<Result<_, Error>>()?;

        let acc = Accumulator::<S>::accumulate(&proof_accs);

        let mut fixed_bases = BTreeMap::new();
        for i in 0..NB_PROOFS {
            fixed_bases.insert(com_instance_name::<NB_PROOFS>(i), C::identity());
        }
        fixed_bases.extend(midnight_circuits::verifier::fixed_bases::<S>(
            "inner_vk",
            &self.inner_vk,
        ));
        assert!(acc.check(&srs.s_g2().into(), &fixed_bases)); // sanity check

        // We now proceed to aggregating all proofs.
        let aggregator_circuit = AggregatorCircuit::<NB_PROOFS> {
            inner_vk: (
                self.inner_vk.get_domain().clone(),
                self.inner_vk.cs().clone(),
                Value::known(self.inner_vk.transcript_repr()),
            ),
            instances: Value::known(instances.clone().map(|v| v.try_into().unwrap())),
            proofs: proofs.clone().map(Value::known),
        };

        let mut aggregator_instances = AssignedVk::<S>::as_public_input(&self.inner_vk);
        (instances.iter()).for_each(|inner_instances| aggregator_instances.extend(inner_instances));
        let (acc_normal_instances, acc_committed_instances) =
            AssignedAccumulator::as_public_input_with_committed_scalars(&acc);
        aggregator_instances.extend(acc_normal_instances);

        let meta_proof = {
            let mut transcript = CircuitTranscript::<Blake2bState>::init();
            create_proof::<
                F,
                KZGCommitmentScheme<E>,
                CircuitTranscript<Blake2bState>,
                AggregatorCircuit<NB_PROOFS>,
            >(
                srs,
                &self.aggregator_pk,
                &[aggregator_circuit],
                1,
                &[&[&acc_committed_instances, &aggregator_instances]],
                &mut rng,
                &mut transcript,
            )?;
            transcript.finalize()
        };

        let acc_rhs_scalars_committed = commit_to_instances::<F, KZGCommitmentScheme<E>>(
            srs,
            self.aggregator_vk.get_domain(),
            &acc_committed_instances,
        );

        let acc_rhs_evaluated = acc.rhs().eval(&fixed_bases);

        let ipa_proof = {
            let mut scalars = acc_committed_instances.clone();
            let mut bases1 = [acc.rhs().bases(), fixed_bases.values().cloned().collect()].concat();
            let mut bases2 = self.lagrange_commitments[..bases1.len()].to_vec();

            let k = bases1.len().next_power_of_two();
            bases1.resize(k, C::identity());
            bases2.resize(k, C::identity());
            scalars.resize(k, F::default());
            ipa_prove::<Blake2bState, _>(
                &scalars,
                &bases1,
                &bases2,
                &acc_rhs_evaluated,
                &acc_rhs_scalars_committed,
            )
        }?;

        Ok(MetaProof {
            proof: meta_proof,
            acc_lhs: acc.lhs(),
            acc_rhs_evaluated,
            acc_rhs_bases: acc.rhs().bases(),
            acc_rhs_scalars_committed,
            ipa_proof,
        })
    }

    /// Verifies an aggregation proof.
    pub fn verify(
        &self,
        srs_verifier: &ParamsVerifierKZG<E>,
        s_g2: &<S as SelfEmulation>::G2Affine,
        instances: &[Vec<F>; NB_PROOFS],
        meta_proof: &MetaProof<NB_PROOFS>,
    ) -> Result<(), Error> {
        // Verify the meta_proof.
        let mut aggregator_instances = AssignedVk::<S>::as_public_input(&self.inner_vk);
        (instances.iter()).for_each(|inner_instances| aggregator_instances.extend(inner_instances));
        aggregator_instances.extend(AssignedMsm::as_public_input(&meta_proof.acc_lhs));
        aggregator_instances.extend(
            meta_proof
                .acc_rhs_bases
                .iter()
                .flat_map(<S as SelfEmulation>::AssignedPoint::as_public_input)
                .collect::<Vec<_>>(),
        );

        let dual_msm = {
            let mut transcript =
                CircuitTranscript::<Blake2bState>::init_from_bytes(&meta_proof.proof);
            prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<Blake2bState>>(
                &self.aggregator_vk,
                &[&[meta_proof.acc_rhs_scalars_committed]],
                &[&[&aggregator_instances]],
                &mut transcript,
            )?
        };

        if !dual_msm.check(srs_verifier) {
            return Err(Error::Opening);
        };

        // Now verify that the final accumulator satisfies the invariant.
        let mut fixed_bases = BTreeMap::new();
        for i in 0..NB_PROOFS {
            fixed_bases.insert(com_instance_name::<NB_PROOFS>(i), C::identity());
        }
        fixed_bases.extend(midnight_circuits::verifier::fixed_bases::<S>(
            "inner_vk",
            &self.inner_vk,
        ));

        let lhs = meta_proof.acc_lhs.eval(&fixed_bases).into();
        let rhs = meta_proof.acc_rhs_evaluated.into();

        if E::pairing(&lhs, s_g2) != E::pairing(&rhs, &<S as SelfEmulation>::G2Affine::generator())
        {
            return Err(Error::Opening);
        };

        // We conclude by checking the IPA proof which guarantess the validity of
        // acc_rhs_evaluated.
        let mut bases1 = [
            meta_proof.acc_rhs_bases.clone(),
            fixed_bases.values().cloned().collect(),
        ]
        .concat();
        let mut bases2 = self.lagrange_commitments[..bases1.len()].to_vec();

        let k = bases1.len().next_power_of_two();
        bases1.resize(k, C::identity());
        bases2.resize(k, C::identity());

        ipa_verify::<Blake2bState, _>(
            &bases1,
            &bases2,
            &meta_proof.acc_rhs_evaluated,
            &meta_proof.acc_rhs_scalars_committed,
            &meta_proof.ipa_proof,
        )
    }
}

fn com_instance_name<const NB_PROOFS: usize>(i: usize) -> String {
    let nb_digits = (NB_PROOFS - 1).to_string().len();
    format!("com_instance_{:0>nb_digits$}", i)
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use ff::Field;
    use group::Group;
    use midnight_circuits::{
        compact_std_lib,
        compact_std_lib::{Relation, ZkStdLib, ZkStdLibArch},
        hash::poseidon::PoseidonChip,
        instructions::{hash::HashCPU, AssignmentInstructions},
    };
    use rand::{rngs::OsRng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[derive(Clone, Default)]
    pub struct InnerCircuit;

    impl Relation for InnerCircuit {
        type Instance = [F; 2];

        type Witness = [F; 2];

        fn format_instance(instance: &Self::Instance) -> Vec<F> {
            instance.to_vec()
        }

        fn circuit(
            &self,
            std_lib: &ZkStdLib,
            layouter: &mut impl Layouter<F>,
            _instance: Value<Self::Instance>,
            witness: Value<Self::Witness>,
        ) -> Result<(), Error> {
            let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
            let output1 = std_lib.poseidon(layouter, &assigned_message)?;
            let output2 = std_lib.poseidon(layouter, &assigned_message[1..])?;
            std_lib.constrain_as_public_input(layouter, &output1)?;
            std_lib.constrain_as_public_input(layouter, &output2)
        }

        fn used_chips(&self) -> ZkStdLibArch {
            ZkStdLibArch {
                jubjub: true,
                poseidon: true,
                sha256: Some(compact_std_lib::ShaTableSize::Table11),
                secp256k1: false,
                bls12_381: false,
                base64: false,
            }
        }

        fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
            Ok(())
        }

        fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
            Ok(InnerCircuit)
        }
    }

    #[test]
    fn test_aggregate_proofs() {
        const NB_PROOFS: usize = 3;

        let mut srs = ParamsKZG::unsafe_setup(15, OsRng);

        let mut inner_srs = srs.clone();

        compact_std_lib::downsize_srs_for_relation(&mut inner_srs, &InnerCircuit);
        let inner_vk = compact_std_lib::setup_vk(&inner_srs, &InnerCircuit);
        let inner_pk = compact_std_lib::setup_pk(&InnerCircuit, &inner_vk);

        let aggregator = LightAggregator::<NB_PROOFS>::init(&mut srs, inner_vk.vk())
            .expect("Failed to init the aggregator");

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]);

        let witnesses: [_; NB_PROOFS] =
            core::array::from_fn(|_| [F::random(&mut rng), F::random(&mut rng)]);

        let instances: [_; NB_PROOFS] = witnesses.map(|preimage| {
            [
                <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage),
                <PoseidonChip<F> as HashCPU<F, F>>::hash(&preimage[1..]),
            ]
        });

        let t = std::time::Instant::now();
        let proofs: [Vec<u8>; NB_PROOFS] = core::array::from_fn(|i| {
            compact_std_lib::prove::<InnerCircuit, LightPoseidonFS<F>>(
                &inner_srs,
                &inner_pk,
                &InnerCircuit,
                &instances[i],
                witnesses[i],
                &mut rng,
            )
            .expect("Problem creating an inner proof")
        });
        println!(
            "{} inner proofs generated in {:?} s",
            NB_PROOFS,
            t.elapsed().as_secs()
        );

        let inner_verifier_params = inner_srs.verifier_params();

        let t = std::time::Instant::now();
        for i in 0..NB_PROOFS {
            let mut transcript =
                CircuitTranscript::<LightPoseidonFS<F>>::init_from_bytes(&proofs[i]);
            let dual_msm =
                prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<LightPoseidonFS<F>>>(
                    inner_vk.vk(),
                    &[&[C::identity()]],
                    &[&[&InnerCircuit::format_instance(&instances[i])]],
                    &mut transcript,
                )
                .unwrap();

            assert!(dual_msm.check(&inner_verifier_params));
        }
        println!(
            "{} inner proofs verified in {:?} ms",
            NB_PROOFS,
            t.elapsed().as_millis()
        );

        let all_instances: [Vec<F>; NB_PROOFS] = instances
            .iter()
            .map(InnerCircuit::format_instance)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let t = std::time::Instant::now();
        let meta_proof = aggregator
            .aggregate_proofs(&srs, &all_instances, &proofs, &mut rng)
            .unwrap();
        println!(
            "Aggregation proof generated in {:?} s",
            t.elapsed().as_secs()
        );

        let t = std::time::Instant::now();
        assert!(aggregator
            .verify(
                &srs.verifier_params(),
                &srs.s_g2().into(),
                &all_instances,
                &meta_proof
            )
            .is_ok());
        println!(
            "Aggregation proof verified in {:?} ms",
            t.elapsed().as_millis()
        );

        let mut buffer = Vec::new();
        meta_proof
            .write(&mut buffer, SerdeFormat::Processed)
            .expect("Meta proof serialization failed");

        println!("Size of meta proof in bytes: {}", buffer.len());

        // Read the meta proof from the buffer and verify it again.

        let mut cursor = Cursor::new(&buffer);
        let meta_proof = MetaProof::read(&mut cursor, SerdeFormat::Processed)
            .expect("Meta proof deserialization failed");

        let t = std::time::Instant::now();
        assert!(aggregator
            .verify(
                &srs.verifier_params(),
                &srs.s_g2().into(),
                &all_instances,
                &meta_proof
            )
            .is_ok());
        println!(
            "Deserialized aggregation proof verified in {:?} ms",
            t.elapsed().as_millis()
        );
    }
}
