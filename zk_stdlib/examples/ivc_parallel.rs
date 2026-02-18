//! Parallelizable Incrementally Verifiable Computation (IVC).
//!
//! Unlike the standard IVC (see `ivc.rs`), this variant allows the proving
//! work to be distributed across multiple machines. The off-circuit
//! computation still runs sequentially, but the expensive proving steps
//! can be performed in parallel, enabling arbitrary speed-up by adding
//! more machines.
//!
//! DO NOT add this example to the CI as it is slow.

use std::{collections::BTreeMap, time::Instant};

use ff::Field;
use group::Group;
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
    instructions::{hash::HashCPU, *},
    types::{AssignedBit, AssignedForeignPoint, AssignedNative, ComposableChip, Instantiable},
    verifier::{
        self, Accumulator, AssignedAccumulator, AssignedVk, BlstrsEmulation, Msm, SelfEmulation,
        VerifierGadget,
    },
};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        self, create_proof, keygen_pk, keygen_vk_with_k, Circuit, ConstraintSystem, Error,
        ProvingKey, VerifyingKey,
    },
    poly::{
        kzg::{
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::utils::plonk_api::filecoin_srs;
use rand::rngs::OsRng;

type S = BlstrsEmulation;

type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;

type E = <S as SelfEmulation>::Engine;
type CBase = <C as CircuitCurve>::Base;

type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

const K: u32 = 19;

// Number of hash iterations in the state transition function.
const N: usize = 2000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct State {
    cnt: F,
    val: F,
}

pub struct AssignedState {
    cnt: AssignedNative<F>,
    val: AssignedNative<F>,
}

impl State {
    fn new(val: F) -> Self {
        Self { cnt: F::ZERO, val }
    }

    fn assign(
        layouter: &mut impl Layouter<F>,
        scalar_chip: &NG,
        state: Value<Self>,
    ) -> Result<AssignedState, Error> {
        Ok(AssignedState {
            cnt: scalar_chip.assign(layouter, state.as_ref().map(|s| s.cnt))?,
            val: scalar_chip.assign(layouter, state.as_ref().map(|s| s.val))?,
        })
    }

    fn as_public_input(&self) -> Vec<F> {
        vec![self.cnt, self.val]
    }

    // This could get an additional witness as input.
    fn transition(&self) -> Self {
        let mut val = self.val;
        for _ in 0..N {
            val = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[val])
        }
        Self {
            cnt: self.cnt + F::from(N as u64),
            val,
        }
    }
}

impl AssignedState {
    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar_chip: &NG,
    ) -> Result<(), Error> {
        scalar_chip.constrain_as_public_input(layouter, &self.cnt)?;
        scalar_chip.constrain_as_public_input(layouter, &self.val)
    }

    fn as_public_input(&self) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![self.cnt.clone(), self.val.clone()])
    }

    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar_chip: &NG,
        other: &Self,
    ) -> Result<AssignedBit<F>, Error> {
        let eq_cnt = scalar_chip.is_equal(layouter, &self.cnt, &other.cnt)?;
        let eq_val = scalar_chip.is_equal(layouter, &self.val, &other.val)?;
        scalar_chip.and(layouter, &[eq_cnt, eq_val])
    }

    fn transition(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar_chip: &NG,
        poseidon_chip: &PoseidonChip<F>,
    ) -> Result<Self, Error> {
        let mut val = self.val.clone();
        for _ in 0..N {
            val = poseidon_chip.hash(layouter, &[val])?;
        }
        Ok(Self {
            cnt: scalar_chip.add_constant(layouter, &self.cnt, F::from(N as u64))?,
            val,
        })
    }
}

#[derive(Clone, Debug)]
pub struct ParallelIvcCircuit {
    self_vk: (EvaluationDomain<F>, ConstraintSystem<F>, Value<F>), // (domain, cs, vk_repr)

    lhs_state: Value<State>,
    mid_state: Value<State>,
    rhs_state: Value<State>,

    lhs_proof: Value<Vec<u8>>,
    rhs_proof: Value<Vec<u8>>,

    lhs_prev_acc: Value<Accumulator<S>>,
    rhs_prev_acc: Value<Accumulator<S>>,
}

fn configure(
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
            advice_columns[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
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

impl Circuit<F> for ParallelIvcCircuit {
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
        configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
        let core_decomp_chip = P2RDecompositionChip::new(&config.1, &(K as usize - 1));
        let scalar_chip = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
        let curve_chip = { ForeignEccChip::new(&config.2, &scalar_chip, &scalar_chip) };
        let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

        let verifier_chip = VerifierGadget::new(&curve_chip, &scalar_chip, &poseidon_chip);

        let (self_domain, self_cs, self_vk_value) = &self.self_vk;
        let assigned_self_vk: AssignedVk<S> = verifier_chip.assign_vk_as_public_input(
            &mut layouter,
            "self_vk",
            self_domain,
            self_cs,
            *self_vk_value,
        )?;

        let assigned_lhs_state = State::assign(&mut layouter, &scalar_chip, self.lhs_state)?;
        let assigned_mid_state = State::assign(&mut layouter, &scalar_chip, self.mid_state)?;
        let assigned_rhs_state = State::assign(&mut layouter, &scalar_chip, self.rhs_state)?;

        assigned_lhs_state.constrain_as_public_input(&mut layouter, &scalar_chip)?;
        assigned_rhs_state.constrain_as_public_input(&mut layouter, &scalar_chip)?;

        let fixed_base_names = verifier::fixed_base_names::<S>(
            "self_vk",
            self_cs.num_fixed_columns() + self_cs.num_selectors(),
            self_cs.permutation().columns.len(),
        );

        let [assigned_lhs_prev_acc, assigned_rhs_prev_acc] =
            [self.lhs_prev_acc.clone(), self.rhs_prev_acc.clone()].map(|acc| {
                AssignedAccumulator::assign(
                    &mut layouter,
                    &curve_chip,
                    &scalar_chip,
                    1,
                    1,
                    &[],
                    &fixed_base_names,
                    acc,
                )
            });
        let assigned_lhs_prev_acc = assigned_lhs_prev_acc?;
        let assigned_rhs_prev_acc = assigned_rhs_prev_acc?;

        let id_point: AssignedForeignPoint<F, C, _> =
            curve_chip.assign_fixed(&mut layouter, C::identity())?;

        let assigned_lhs_pi = [
            verifier_chip.as_public_input(&mut layouter, &assigned_self_vk)?,
            assigned_lhs_state.as_public_input()?,
            assigned_mid_state.as_public_input()?,
            verifier_chip.as_public_input(&mut layouter, &assigned_lhs_prev_acc)?,
        ]
        .concat();

        let mut lhs_proof_acc = verifier_chip.prepare(
            &mut layouter,
            &assigned_self_vk,
            std::slice::from_ref(&id_point),
            &[&assigned_lhs_pi],
            self.lhs_proof.clone(),
        )?;

        let assigned_rhs_pi = [
            verifier_chip.as_public_input(&mut layouter, &assigned_self_vk)?,
            assigned_mid_state.as_public_input()?,
            assigned_rhs_state.as_public_input()?,
            verifier_chip.as_public_input(&mut layouter, &assigned_rhs_prev_acc)?,
        ]
        .concat();

        let mut rhs_proof_acc = verifier_chip.prepare(
            &mut layouter,
            &assigned_self_vk,
            std::slice::from_ref(&id_point),
            &[&assigned_rhs_pi],
            self.rhs_proof.clone(),
        )?;

        lhs_proof_acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;
        rhs_proof_acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;

        let supposedly_mid_state =
            assigned_lhs_state.transition(&mut layouter, &scalar_chip, &poseidon_chip)?;

        let b = assigned_mid_state.is_equal(&mut layouter, &scalar_chip, &supposedly_mid_state)?;
        let not_b = scalar_chip.not(&mut layouter, &b)?;
        AssignedAccumulator::scale_by_bit(&mut layouter, &scalar_chip, &not_b, &mut lhs_proof_acc)?;

        let supposedly_rhs_state =
            assigned_mid_state.transition(&mut layouter, &scalar_chip, &poseidon_chip)?;
        let b = assigned_rhs_state.is_equal(&mut layouter, &scalar_chip, &supposedly_rhs_state)?;
        let not_b = scalar_chip.not(&mut layouter, &b)?;
        AssignedAccumulator::scale_by_bit(&mut layouter, &scalar_chip, &not_b, &mut rhs_proof_acc)?;

        let mut acc = AssignedAccumulator::<S>::accumulate(
            &mut layouter,
            &verifier_chip,
            &scalar_chip,
            &poseidon_chip,
            &[
                assigned_lhs_prev_acc,
                assigned_rhs_prev_acc,
                lhs_proof_acc,
                rhs_proof_acc,
            ],
        )?;

        acc.collapse(&mut layouter, &curve_chip, &scalar_chip)?;
        verifier_chip.constrain_as_public_input(&mut layouter, &acc)?;

        core_decomp_chip.load(&mut layouter)
    }
}

#[derive(Clone, Debug)]
pub struct Circuit1 {
    preimage: Value<[F; 3]>,
}

impl Circuit<F> for Circuit1 {
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
        configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let native_chip = <NativeChip<F> as ComposableChip<F>>::new(&config.0, &());
        let poseidon_chip = PoseidonChip::new(&config.3, &native_chip);

        let preimage = native_chip.assign_many(&mut layouter, &self.preimage.transpose_array())?;
        let output = poseidon_chip.hash(&mut layouter, &preimage)?;
        native_chip.constrain_as_public_input(&mut layouter, &output)
    }
}

fn main() {
    let self_k = K;

    let mut self_cs = ConstraintSystem::default();
    configure(&mut self_cs);
    let self_domain = EvaluationDomain::new(self_cs.degree() as u32, self_k);

    let default_parallel_ivc_circuit = ParallelIvcCircuit {
        self_vk: (self_domain.clone(), self_cs.clone(), Value::unknown()),
        lhs_state: Value::unknown(),
        mid_state: Value::unknown(),
        rhs_state: Value::unknown(),

        lhs_proof: Value::unknown(),
        rhs_proof: Value::unknown(),

        lhs_prev_acc: Value::unknown(),
        rhs_prev_acc: Value::unknown(),
    };

    dbg!(
        midnight_proofs::dev::cost_model::circuit_model::<_, 48, 32>(&default_parallel_ivc_circuit)
    );

    let srs = filecoin_srs(K);

    let start = Instant::now();
    let vk = keygen_vk_with_k(&srs, &default_parallel_ivc_circuit, K).unwrap();
    let pk = keygen_pk(vk.clone(), &default_parallel_ivc_circuit).unwrap();
    println!("Computed vk and pk in {:?} s", start.elapsed());

    let fixed_bases = midnight_circuits::verifier::fixed_bases::<S>("self_vk", &vk);
    let fixed_base_names = fixed_bases.keys().cloned().collect::<Vec<_>>();

    let state0 = State::new(F::from(0xdeadbeef));
    let state1 = state0.transition();
    let state2 = state1.transition();
    let state3 = state2.transition();
    let state4 = state3.transition();
    let state5 = state4.transition();

    // We can merge transitions in any order!
    //
    // Let's prove:
    //   0->2
    //   3->5
    //   2->5 as 2->(3->5)
    //   0->5 as (0->2)->(2->5)
    //
    // Proofs 0->2 and 3->5 could be done in parallel!
    // For maximizing parallelization, one could adopt a binary tree structure.
    let start = Instant::now();
    let (proof_02, acc_02) = prove(
        &srs,
        &self_domain,
        &self_cs,
        &pk,
        state0,
        state1,
        state2,
        &[],
        &[],
        trivial_acc(&fixed_base_names),
        trivial_acc(&fixed_base_names),
    )
    .expect("Prover failed");
    println!("Proof 0->2 computed in {:?} s", start.elapsed());

    let start = Instant::now();
    let (proof_35, acc_35) = prove(
        &srs,
        &self_domain,
        &self_cs,
        &pk,
        state3,
        state4,
        state5,
        &[],
        &[],
        trivial_acc(&fixed_base_names),
        trivial_acc(&fixed_base_names),
    )
    .expect("Prover failed");
    println!("Proof 3->5 computed in {:?} s", start.elapsed());

    let start = Instant::now();
    let (proof_25, acc_25) = prove(
        &srs,
        &self_domain,
        &self_cs,
        &pk,
        state2,
        state3,
        state5,
        &[],
        &proof_35,
        trivial_acc(&fixed_base_names),
        acc_35,
    )
    .expect("Prover failed");
    println!("Proof 2->5 computed in {:?} s", start.elapsed());

    let start = Instant::now();
    let (proof_05, acc_05) = prove(
        &srs,
        &self_domain,
        &self_cs,
        &pk,
        state0,
        state2,
        state5,
        &proof_02,
        &proof_25,
        acc_02,
        acc_25,
    )
    .expect("Prover failed");
    println!("Proof 0->5 computed in {:?} s", start.elapsed());

    let final_acc = prepare(
        &srs.verifier_params(),
        &fixed_bases,
        &vk,
        state0,
        state5,
        &acc_05,
        &proof_05,
    )
    .expect("Verification failed");

    // The final check is making sure both final_acc and acc_05 satisfy the
    // invariant. We can check both at the same time.
    let accumulated = Accumulator::accumulate(&[acc_05, final_acc]);
    assert!(
        accumulated.check(&srs.s_g2().into(), &fixed_bases),
        "Verification of transition 0->5 failed"
    );

    println!("Proof of transition 0->5 passed!")
}

fn prepare(
    verifier_params: &ParamsVerifierKZG<E>,
    fixed_bases: &BTreeMap<String, C>,
    vk: &VerifyingKey<F, KZGCommitmentScheme<E>>,
    lhs_state: State,
    rhs_state: State,
    acc: &Accumulator<S>,
    proof: &[u8],
) -> Result<Accumulator<S>, Error> {
    let mut public_inputs = AssignedVk::<S>::as_public_input(vk);
    public_inputs.extend(lhs_state.as_public_input());
    public_inputs.extend(rhs_state.as_public_input());
    public_inputs.extend(AssignedAccumulator::as_public_input(acc));

    let mut transcript = CircuitTranscript::<PoseidonState<F>>::init_from_bytes(proof);
    let dual_msm = plonk::prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
        vk,
        &[&[C::identity()]],
        &[&[&public_inputs]],
        &mut transcript,
    )?;

    assert!(dual_msm.clone().check(verifier_params));

    let mut proof_acc = Accumulator::from_dual_msm(dual_msm, "self_vk", fixed_bases);
    proof_acc.collapse();

    Ok(proof_acc)
}

#[allow(clippy::too_many_arguments)]
fn prove(
    srs: &ParamsKZG<E>,
    self_domain: &EvaluationDomain<F>,
    self_cs: &ConstraintSystem<F>,
    pk: &ProvingKey<F, KZGCommitmentScheme<E>>,
    lhs_state: State,
    mid_state: State,
    rhs_state: State,
    lhs_proof: &[u8],
    rhs_proof: &[u8],
    lhs_prev_acc: Accumulator<S>,
    rhs_prev_acc: Accumulator<S>,
) -> Result<(Vec<u8>, Accumulator<S>), Error> {
    let vk = pk.get_vk();

    let circuit = ParallelIvcCircuit {
        self_vk: (
            self_domain.clone(),
            self_cs.clone(),
            Value::known(vk.transcript_repr()),
        ),

        lhs_state: Value::known(lhs_state),
        mid_state: Value::known(mid_state),
        rhs_state: Value::known(rhs_state),

        lhs_proof: Value::known(lhs_proof.to_vec()),
        rhs_proof: Value::known(rhs_proof.to_vec()),

        lhs_prev_acc: Value::known(lhs_prev_acc.clone()),
        rhs_prev_acc: Value::known(rhs_prev_acc.clone()),
    };

    let fixed_bases = midnight_circuits::verifier::fixed_bases::<S>("self_vk", vk);
    let fixed_base_names = fixed_bases.keys().cloned().collect::<Vec<_>>();

    let lhs_proof_acc = if lhs_state.transition() == mid_state {
        trivial_acc(&fixed_base_names)
    } else {
        prepare(
            &srs.verifier_params(),
            &fixed_bases,
            vk,
            lhs_state,
            mid_state,
            &lhs_prev_acc,
            lhs_proof,
        )?
    };

    let rhs_proof_acc = if mid_state.transition() == rhs_state {
        trivial_acc(&fixed_base_names)
    } else {
        prepare(
            &srs.verifier_params(),
            &fixed_bases,
            vk,
            mid_state,
            rhs_state,
            &rhs_prev_acc,
            rhs_proof,
        )?
    };

    let mut acc =
        Accumulator::accumulate(&[lhs_prev_acc, rhs_prev_acc, lhs_proof_acc, rhs_proof_acc]);
    acc.collapse();

    let mut public_inputs = AssignedVk::<S>::as_public_input(vk);
    public_inputs.extend(lhs_state.as_public_input());
    public_inputs.extend(rhs_state.as_public_input());
    public_inputs.extend(AssignedAccumulator::as_public_input(&acc));

    let proof = {
        let mut transcript = CircuitTranscript::<PoseidonState<F>>::init();
        create_proof::<
            F,
            KZGCommitmentScheme<E>,
            CircuitTranscript<PoseidonState<F>>,
            ParallelIvcCircuit,
        >(
            srs,
            pk,
            std::slice::from_ref(&circuit),
            1,
            &[&[&[], &public_inputs]],
            OsRng,
            &mut transcript,
        )?;
        transcript.finalize()
    };

    Ok((proof, acc))
}

/// Returns a trivial accumulator that satisfies the invariant.
/// This is the result of scale_by_bit with a 0 bit on any collapsed
/// accumulator.
fn trivial_acc(fixed_base_names: &[String]) -> Accumulator<S> {
    Accumulator::<S>::new(
        Msm::new(&[C::default()], &[F::ZERO], &BTreeMap::new()),
        Msm::new(
            &[C::default()],
            &[F::ZERO],
            &fixed_base_names.iter().map(|name| (name.clone(), F::ZERO)).collect(),
        ),
    )
}
