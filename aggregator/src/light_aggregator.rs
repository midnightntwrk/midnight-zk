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

use std::{cell::RefCell, collections::BTreeMap, io};

use group::Group;
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
        Accumulator, AssignedAccumulator, AssignedMsm, AssignedVk, Base as MsmBase, Msm,
        SelfEmulation, VerifierGadget,
    },
};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        self, commit_to_instances, create_proof, keygen_pk, keygen_vk, prepare, Circuit,
        ConstraintSystem, Error,
    },
    poly::{
        commitment::{Guard, Params},
        kzg::{
            msm::{DualMSM, MSMKZG},
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
};
use rand::{CryptoRng, RngCore};

use crate::{
    inner_product_argument::{ipa_prove, ipa_verify},
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
    fixed_bases_schemes: Vec<Vec<Option<String>>>,
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
    fixed_bases_scheme: RefCell<Vec<Vec<Option<String>>>>,
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
                advice_columns[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
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

        *self.fixed_bases_scheme.borrow_mut() =
            proof_accs.iter().map(|acc| acc.name_scheme()).collect();

        let acc = AssignedAccumulator::<S>::accumulate(
            &mut layouter,
            &verifier_chip,
            &scalar_chip,
            &sponge_chip,
            &proof_accs,
        )?;

        verifier_chip.constrain_acc_as_public_input_with_committed_scalars(&mut layouter, &acc)?;

        scalar_chip.load(&mut layouter)?;
        sponge_chip.load(&mut layouter)?;

        // It is very important to call finalize in order to make sure all witnessed
        // points were at some point constrained as public inputs.
        fake_curve_chip.finalize()
    }
}

impl<const NB_PROOFS: usize> LightAggregator<NB_PROOFS> {
    /// Reconstructs the fixed bases map from the fixed_bases_schemes and inner_vk.
    /// This is used by both the prover and verifier.
    fn reconstruct_fixed_bases(&self) -> BTreeMap<String, C> {
        let mut all_fixed_bases = BTreeMap::new();

        // Process each proof's fixed_bases_scheme to extract fixed base names and values
        for (i, _name_scheme) in self.fixed_bases_schemes.iter().enumerate() {
            // We need to simulate what from_dual_msm would return by matching the structure
            // of a real prepare call. Since we don't have the actual MSM bases here,
            // we need to reconstruct them from the inner_vk and known constants.

            // For now, add the com_instance base for this proof
            all_fixed_bases.insert(com_instance_name::<NB_PROOFS>(i), C::identity());

            // The name_scheme tells us which bases are fixed, but to get their values
            // we need to match them against the inner_vk structure.
            // Fixed bases from the inner_vk include:
            // - ~G (the generator)
            // - ~inner_vk_fixed_com_XX (fixed commitments from the vk)
            // - ~inner_vk_perm_com_XX (permutation commitments from the vk)
        }

        // Add the generator
        all_fixed_bases.insert("~G".to_string(), -C::generator());

        // Add fixed commitments from inner_vk
        let nb_fixed_commitments = self.inner_vk.fixed_commitments().len();
        if nb_fixed_commitments > 0 {
            let nb_digits = (nb_fixed_commitments - 1).to_string().len();
            for (i, commitment) in self.inner_vk.fixed_commitments().iter().enumerate() {
                let name = format!("~inner_vk_fixed_com_{:0>nb_digits$}", i);
                all_fixed_bases.insert(name, *commitment);
            }
        }

        // Add permutation commitments from inner_vk
        let nb_perm_commitments = self.inner_vk.permutation().commitments().len();
        if nb_perm_commitments > 0 {
            let nb_digits = (nb_perm_commitments - 1).to_string().len();
            for (i, commitment) in self.inner_vk.permutation().commitments().iter().enumerate() {
                let name = format!("~inner_vk_perm_com_{:0>nb_digits$}", i);
                all_fixed_bases.insert(name, *commitment);
            }
        }

        all_fixed_bases
    }

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
            fixed_bases_scheme: RefCell::new(vec![]),
        };

        // TODO: Remove, we are hardcoding BLS constants here.
        dbg!(
            midnight_proofs::dev::cost_model::circuit_model::<_, 48, 32>(
                &default_aggregator_circuit,
            )
        );

        srs.downsize_from_circuit(&default_aggregator_circuit);

        let aggregator_vk = keygen_vk(srs, &default_aggregator_circuit)?;
        let aggregator_pk = keygen_pk(aggregator_vk.clone(), &default_aggregator_circuit)?;

        // Capture the fixed_bases_scheme that was populated during keygen
        let fixed_bases_schemes = default_aggregator_circuit.fixed_bases_scheme.borrow().clone();

        // Calculate the actual number of lagrange commitments needed based on the fixed_bases_schemes
        let nb_lagrange_coms = fixed_bases_schemes
            .iter()
            .map(|scheme| scheme.len())
            .sum::<usize>();

        Ok(Self {
            inner_vk: inner_vk.clone(),
            aggregator_vk,
            aggregator_pk,
            lagrange_commitments: srs.g_lagrange()[..nb_lagrange_coms].to_vec(),
            fixed_bases_schemes,
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
    pub fn aggregate_proofs<T>(
        &self,
        srs: &ParamsKZG<E>,
        instances: &[Vec<F>; NB_PROOFS],
        proofs: &[Vec<u8>; NB_PROOFS],
        mut rng: impl RngCore + CryptoRng,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        T: Transcript,
        C: Hashable<T::Hash>,
        F: Sampleable<T::Hash> + Hashable<T::Hash>,
        u32: Hashable<T::Hash>,
    {
        // We first verify all proofs off-circuit, to get the final batched accumulator,
        // which must be a public input of the aggregator circuit.
        let proof_accs_with_bases: Vec<(Accumulator<S>, BTreeMap<String, C>)> = (proofs.iter())
            .zip(instances.iter())
            .zip(self.fixed_bases_schemes.iter())
            .map(|((proof, proof_instances), name_scheme)| {
                let mut inner_transcript =
                    CircuitTranscript::<LightPoseidonFS<F>>::init_from_bytes(proof);
                let dual_msm = plonk::prepare::<
                    F,
                    KZGCommitmentScheme<E>,
                    CircuitTranscript<LightPoseidonFS<F>>,
                >(
                    &self.inner_vk,
                    &[&[C::identity()]],
                    &[&[proof_instances]],
                    &mut inner_transcript,
                )?;

                assert!(dual_msm.clone().check(&srs.verifier_params()));

                let (proof_acc, fixed_bases) = Accumulator::<S>::from_dual_msm(&dual_msm, name_scheme);
                Ok((proof_acc, fixed_bases))
            })
            .collect::<Result<_, Error>>()?;

        let proof_accs: Vec<Accumulator<S>> = proof_accs_with_bases.iter().map(|(acc, _)| acc.clone()).collect();
        let acc = Accumulator::<S>::accumulate(&proof_accs);

        // Collect all fixed bases from all proofs
        let mut fixed_bases = BTreeMap::new();
        for (_acc, bases) in proof_accs_with_bases.iter() {
            fixed_bases.extend(bases.clone());
        }
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
            fixed_bases_scheme: RefCell::new(vec![]),
        };

        let mut aggregator_instances = AssignedVk::<S>::as_public_input(&self.inner_vk);
        (instances.iter()).for_each(|inner_instances| aggregator_instances.extend(inner_instances));
        let (acc_normal_instances, acc_committed_instances) =
            AssignedAccumulator::as_public_input_with_committed_scalars(&acc);
        aggregator_instances.extend(acc_normal_instances);

        let acc_rhs_scalars_committed = commit_to_instances::<F, KZGCommitmentScheme<E>>(
            srs,
            self.aggregator_vk.get_domain(),
            &acc_committed_instances,
        );
        let acc_rhs_evaluated = acc.rhs().eval(&fixed_bases);

        // Add the LHS of acc to the transcript.
        // All bases should be variable at this point
        assert!(acc.lhs().bases().iter().all(|b| matches!(b, MsmBase::Variable(_))));
        transcript.write(&(acc.lhs().bases().len() as u32))?;
        acc.lhs().bases().iter().try_for_each(|base| match base {
            MsmBase::Variable(p) => transcript.write(p),
            _ => unreachable!(),
        })?;
        acc.lhs().scalars().iter().try_for_each(|s| transcript.write(s))?;

        // Add the RHS of the acc to the transcript (with scalars in committed form).
        let rhs_num_bases =
            acc.rhs().bases().iter().filter(|b| matches!(b, MsmBase::Variable(_))).count();
        transcript.write(&(rhs_num_bases as u32))?;
        acc.rhs().bases().iter().try_for_each(|base| {
            if let MsmBase::Variable(p) = base {
                transcript.write(p)
            } else {
                Ok(())
            }
        })?;
        transcript.write(&acc_rhs_scalars_committed)?;
        transcript.write(&acc_rhs_evaluated)?;

        // Create a proof of having verified the native part of all inner proofs.
        create_proof::<F, KZGCommitmentScheme<E>, T, AggregatorCircuit<NB_PROOFS>>(
            srs,
            &self.aggregator_pk,
            &[aggregator_circuit],
            1,
            &[&[&acc_committed_instances, &aggregator_instances]],
            &mut rng,
            transcript,
        )?;

        // Create the IPA proof
        let mut scalars = acc_committed_instances.clone();
        let mut bases1: Vec<C> = acc
            .rhs()
            .bases()
            .iter()
            .map(|base| match base {
                MsmBase::Variable(b) => *b,
                MsmBase::Fixed(name) => *fixed_bases.get(name).expect("Fixed base not found"),
            })
            .collect();
        let mut bases2 = self.lagrange_commitments[..bases1.len()].to_vec();

        let k = bases1.len().next_power_of_two();
        bases1.resize(k, C::identity());
        bases2.resize(k, C::identity());
        scalars.resize(k, F::default());

        ipa_prove(
            &scalars,
            &bases1,
            &bases2,
            &acc_rhs_evaluated,
            &acc_rhs_scalars_committed,
            transcript,
        )
    }

    /// Verifies an aggregation proof.
    pub fn verify<T>(
        &self,
        srs_verifier: &ParamsVerifierKZG<E>,
        instances: &[Vec<F>; NB_PROOFS],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        T: Transcript,
        C: Hashable<T::Hash>,
        F: Sampleable<T::Hash> + Hashable<T::Hash>,
        u32: Hashable<T::Hash>,
    {
        // Read the LHS of the acc from the transcript.
        let acc_lhs: Msm<S> = {
            let n: u32 = transcript.read()?;
            let lhs_bases: Result<Vec<C>, io::Error> = (0..n).map(|_| transcript.read()).collect();
            let lhs_scalars: Result<Vec<F>, io::Error> =
                (0..n).map(|_| transcript.read()).collect();
            let wrapped_bases: Vec<_> = lhs_bases?.iter().map(|&b| MsmBase::Variable(b)).collect();
            Msm::new(&wrapped_bases, &lhs_scalars?)
        };

        // Read the RHS of the acc from the transcript (with scalars in committed form).
        let acc_rhs_bases = {
            let n: u32 = transcript.read()?;
            (0..n).map(|_| transcript.read()).collect::<Result<Vec<C>, io::Error>>()?
        };
        let acc_rhs_scalars_committed: C = transcript.read()?;
        let acc_rhs_evaluated: C = transcript.read()?;

        // Verify the proof of validity of the native verification of all inner proofs.
        let mut aggregator_instances = AssignedVk::<S>::as_public_input(&self.inner_vk);
        (instances.iter()).for_each(|inner_instances| aggregator_instances.extend(inner_instances));
        aggregator_instances.extend(AssignedMsm::as_public_input(&acc_lhs));
        aggregator_instances.extend(
            acc_rhs_bases
                .clone()
                .iter()
                .flat_map(<S as SelfEmulation>::AssignedPoint::as_public_input)
                .collect::<Vec<_>>(),
        );

        let proof_dual_msm = {
            prepare::<F, KZGCommitmentScheme<E>, T>(
                &self.aggregator_vk,
                &[&[acc_rhs_scalars_committed]],
                &[&[&aggregator_instances]],
                transcript,
            )?
        };

        // Now verify that the final accumulator satisfies the invariant.
        let fixed_bases = self.reconstruct_fixed_bases();

        let acc_dual_msm = DualMSM::new(
            MSMKZG::<E>::from_base(&acc_lhs.eval(&fixed_bases)),
            MSMKZG::<E>::from_base(&acc_rhs_evaluated),
        );

        // We conclude by checking the IPA proof which guarantess the validity of
        // acc_rhs_evaluated.
        // We need to reconstruct bases1 in the same order as the prover did, which means
        // interleaving Variable and Fixed bases according to the accumulated MSM structure.
        // The accumulated RHS MSM has bases from all proofs concatenated.
        let mut bases1 = Vec::new();
        let mut var_base_idx = 0;

        for name_scheme in self.fixed_bases_schemes.iter() {
            for base_name_opt in name_scheme.iter() {
                match base_name_opt {
                    Some(name) => {
                        // This is a Fixed base
                        bases1.push(*fixed_bases.get(name).expect("Fixed base not found"));
                    }
                    None => {
                        // This is a Variable base
                        bases1.push(acc_rhs_bases[var_base_idx]);
                        var_base_idx += 1;
                    }
                }
            }
        }

        let mut bases2 = self.lagrange_commitments[..bases1.len()].to_vec();

        let k = bases1.len().next_power_of_two();
        bases1.resize(k, C::identity());
        bases2.resize(k, C::identity());

        ipa_verify(
            &bases1,
            &bases2,
            &acc_rhs_evaluated,
            &acc_rhs_scalars_committed,
            transcript,
        )?;

        let mut dual_msm = DualMSM::init();
        let r: F = transcript.squeeze_challenge();
        dual_msm.add_msm(acc_dual_msm);
        dual_msm.scale(r);
        dual_msm.add_msm(proof_dual_msm);
        dual_msm.verify(srs_verifier).map_err(|_| Error::Opening)
    }
}

fn com_instance_name<const NB_PROOFS: usize>(i: usize) -> String {
    let nb_digits = (NB_PROOFS - 1).to_string().len();
    format!("com_instance_{:0>nb_digits$}", i)
}

#[cfg(test)]
mod tests {

    use blake2b_simd::State as Blake2bState;
    use ff::Field;
    use group::Group;
    use midnight_circuits::{
        hash::poseidon::PoseidonChip,
        instructions::{hash::HashCPU, AssignmentInstructions},
    };
    use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
    use rand::{rngs::OsRng, SeedableRng};
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[derive(Clone, Default)]
    pub struct InnerCircuit;

    impl Relation for InnerCircuit {
        type Instance = [F; 2];

        type Witness = [F; 2];

        fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
            Ok(instance.to_vec())
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
                sha2_256: true,
                nr_pow2range_cols: 4,
                ..ZkStdLibArch::default()
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

        midnight_zk_stdlib::downsize_srs_for_relation(&mut inner_srs, &InnerCircuit);
        let inner_vk = midnight_zk_stdlib::setup_vk(&inner_srs, &InnerCircuit);
        let inner_pk = midnight_zk_stdlib::setup_pk(&InnerCircuit, &inner_vk);

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
            midnight_zk_stdlib::prove::<InnerCircuit, LightPoseidonFS<F>>(
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
                    &[&[&InnerCircuit::format_instance(&instances[i]).unwrap()]],
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
            .map(|instance| InnerCircuit::format_instance(instance).unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let t = std::time::Instant::now();
        let mut transcript = CircuitTranscript::<Blake2bState>::init();
        aggregator
            .aggregate_proofs(&srs, &all_instances, &proofs, &mut rng, &mut transcript)
            .unwrap();
        println!(
            "Aggregation proof generated in {:?} s",
            t.elapsed().as_secs()
        );

        let meta_proof = transcript.finalize();
        println!("Size of meta proof in bytes: {}", meta_proof.len());

        let t = std::time::Instant::now();
        let mut transcript = CircuitTranscript::<Blake2bState>::init_from_bytes(&meta_proof);
        assert!(aggregator
            .verify(&srs.verifier_params(), &all_instances, &mut transcript)
            .is_ok());
        println!(
            "Aggregation proof verified in {:?} ms",
            t.elapsed().as_millis()
        );
    }
}
