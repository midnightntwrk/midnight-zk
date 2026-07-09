//! Verifies a complete IVC proof **in-circuit** and compresses the whole chain
//! into a single accumulator, following the "final IVC circuit" design:
//!
//! 1. Partially verify the IVC proof with the IVC decider ([`IvcDecider`]) —
//!    prepare only, fixed bases kept symbolic.
//! 2. Merge the resulting accumulator with the one carried in the IVC proof's
//!    public inputs (known non-genesis, so no scaling).
//! 3. Collapse and resolve the fixed bases once.
//!
//! The single collapsed accumulator is exposed as a public input; its pairing
//! (the decider) is discharged off-circuit at the end — the same check
//! [`IvcVerifier::verify`] performs.
//!
//! DO NOT add this example to the CI as it is slow.

use std::collections::BTreeMap;

use ff::Field;
use group::Group;
use midnight_aggregation::ivc::{
    self, IvcAssignedFinalVk, IvcCircuit, IvcContext, IvcFinalVk, IvcIO, IvcState, IvcTransition, circuit::IvcFinalDecider,
};
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{hash::HashCPU, *},
    types::{AssignedNative, Instantiable},
    verifier::{
        fixed_base_labels, fixed_bases, Accumulator, AssignedAccumulator, AssignedKZGCommitment,
        BlstrsEmulation, SelfEmulation,
    },
};
use midnight_curves::G1Projective as C;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::{kzg::commitment::KZGCommitment, PolynomialLabel},
};
use midnight_zk_stdlib::{
    decidable::Decidable,
    prove, setup_pk, setup_vk,
    utils::plonk_api::{load_srs, SrsSource},
    MidnightVK, Relation, ZkStdLib, ZkStdLibArch,
};
use rand::rngs::OsRng;

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;

// ---------------------------------------------------------------------------
// A minimal IVC transition: a Poseidon hash-chain with a step counter.
// (Copied from the `ivc` example.)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct State {
    cnt: F,
    val: F,
}

#[derive(Clone, Debug)]
pub struct AssignedState {
    cnt: AssignedNative<F>,
    val: AssignedNative<F>,
}

#[derive(Clone, Debug)]
pub struct PoseidonChain<const N: usize> {
    std_lib: ZkStdLib,
}

impl<const N: usize> IvcContext for PoseidonChain<N> {
    type Context = ();
    fn new(std_lib: ZkStdLib, _ctx: &()) -> Self {
        PoseidonChain { std_lib }
    }
    fn write_context<W: std::io::Write>(_ctx: &(), _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }
    fn read_context<R: std::io::Read>(_reader: &mut R) -> std::io::Result<()> {
        Ok(())
    }
}

impl<const N: usize> IvcState for PoseidonChain<N> {
    type State = State;
    type AssignedState = AssignedState;
    fn genesis(_ctx: &()) -> Self::State {
        State { cnt: F::ZERO, val: F::ZERO }
    }
    fn decider(_ctx: &Self::Context, _state: &Self::State) -> bool {
        true
    }
}

impl<const N: usize> IvcIO for PoseidonChain<N> {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381().scalar_field_chip();
        Ok(AssignedState {
            cnt: scalar_chip.assign(layouter, value.as_ref().map(|s| s.cnt))?,
            val: scalar_chip.assign(layouter, value.as_ref().map(|s| s.val))?,
        })
    }
    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        let scalar_chip = self.std_lib.bls12_381().scalar_field_chip();
        scalar_chip.constrain_as_public_input(layouter, &state.cnt)?;
        scalar_chip.constrain_as_public_input(layouter, &state.val)
    }
    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![state.cnt.clone(), state.val.clone()])
    }
    fn format_public_input(state: &State) -> Vec<F> {
        vec![state.cnt, state.val]
    }
}

impl<const N: usize> IvcTransition for PoseidonChain<N> {
    type Witness = ();
    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nb_arith_cols: 9,
            nr_pow2range_cols: 8,
            ..ZkStdLibArch::default()
        }
    }
    fn transition(_ctx: &(), state: &Self::State, _witness: Self::Witness) -> Self::State {
        let mut val = state.val;
        for _ in 0..N {
            val = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[val]);
        }
        State { cnt: state.cnt + F::from(N as u64), val }
    }
    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        _witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381().scalar_field_chip();
        let mut val = state.val.clone();
        for _ in 0..N {
            val = self.std_lib.poseidon(layouter, &[val])?;
        }
        let cnt = scalar_chip.add_constant(layouter, &state.cnt, F::from(N as u64))?;
        Ok(AssignedState { cnt, val })
    }
}


#[derive(Clone, Debug)]
struct FinalIvcWitness {
    state: State,
    carried_acc: Accumulator<S>,
    proof: Vec<u8>,
}

/// Relation that verifies a complete IVC proof for `ivc_vk`. It delegates the
/// verify-fold-collapse to [`IvcCircuit`]'s decider (one final chain step) and
/// then finalizes: resolves the fixed bases and exposes the single accumulator.
#[derive(Clone)]
struct FinalIvcVerifier<const N: usize> {
    ivc_vk: MidnightVK,
}

impl<const N: usize> Relation for FinalIvcVerifier<N> {
    type Instance = Vec<F>;
    type Witness = FinalIvcWitness;
    type Error = Error;

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(instance.clone())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            bls12_381: true,
            nb_arith_cols: 9,
            nr_pow2range_cols: 8,
            ..ZkStdLibArch::default()
        }
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let verifier = std_lib.verifier();
        let scalar_chip = std_lib.bls12_381().scalar_field_chip();
        let plonk_vk = self.ivc_vk.vk();
        let cs = plonk_vk.cs();

        // 1. Assign the (known) IVC verifying key as a constant.
        let assigned_vk = verifier.assign_fixed_vk(
            layouter,
            plonk_vk.get_domain(),
            cs,
            plonk_vk.transcript_repr(),
        )?;

        // 2. Assign the final state.
        let cnt = scalar_chip.assign(layouter, witness.as_ref().map(|w| w.state.cnt))?;
        let val = scalar_chip.assign(layouter, witness.as_ref().map(|w| w.state.val))?;

        // 3. Assign the carried accumulator (collapsed, symbolic fixed bases).
        let fb_labels = fixed_base_labels::<S>(
            cs.num_fixed_columns() + cs.num_selectors(),
            cs.permutation().columns.len(),
        );
        let carried = verifier.assign_collapsed_accumulator(
            layouter,
            &fb_labels,
            witness.as_ref().map(|w| w.carried_acc.clone()),
        )?;

        // 4. Reconstruct the IVC proof's public inputs: vk_repr ++ state ++ acc.
        //    Using the *same* assigned `carried` for both the PI and the fold is
        //    what binds it to the proof.
        let proof_pi = [
            verifier.as_public_input(layouter, &assigned_vk)?,
            vec![cnt, val],
            verifier.as_public_input(layouter, &carried)?,
        ]
        .concat();

        let committed = vec![AssignedKZGCommitment::simple(
            std_lib.bls12_381().assign_fixed(layouter, C::identity())?,
            PolynomialLabel::Instance(0),
        )];

        // 5. Run the final chain step (verify + fold + collapse + resolve) via
        //    IvcCircuit's decider. The `carried` folded here is the *same* assigned
        //    value used in `proof_pi`, which binds it to the proof.
        let assigned_bases = fixed_bases::<S>(plonk_vk)
            .into_iter()
            .map(|(l, p)| Ok((l, std_lib.bls12_381().assign_fixed(layouter, p)?)))
            .collect::<Result<BTreeMap<_, _>, Error>>()?;
        let final_vk = IvcAssignedFinalVk {
            vk: assigned_vk,
            carried_acc: carried,
            fixed_bases: assigned_bases,
        };
        let merged = IvcFinalDecider::in_circuit_decide(
            std_lib,
            layouter,
            &final_vk,
            &committed,
            &[&proof_pi],
            witness.map(|w| w.proof),
        )?
        .expect("IvcCircuit decider yields an accumulator");

        // 6. Expose the fully-resolved accumulator for the (off-circuit) pairing.
        verifier.constrain_as_public_input(layouter, &merged)?;
        Ok(())
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        unimplemented!("not needed for this example")
    }
    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        unimplemented!("not needed for this example")
    }
}

/// Off-circuit mirror of [`FinalIvcVerifier::circuit`]: computes the exposed
/// collapsed-and-resolved accumulator so we can also run the final pairing.
fn final_accumulator<const N: usize>(
    ivc_vk: &MidnightVK,
    state: &State,
    carried_acc: &Accumulator<S>,
    proof: &[u8],
) -> Accumulator<S> {
    let mut full_pi = vec![ivc_vk.vk().transcript_repr(), state.cnt, state.val];
    full_pi.extend(AssignedAccumulator::<S>::as_public_input(carried_acc));

    // Verify + fold + collapse + resolve, via IvcCircuit's decider (final step).
    let final_vk = IvcFinalVk { vk: ivc_vk.vk().clone(), accumulator: carried_acc.clone() };
    IvcFinalDecider::decide(
        &final_vk,
        &[KZGCommitment::Simple(C::identity(), PolynomialLabel::Instance(0))],
        &[&full_pi],
        proof,
    )
    .expect("off-circuit decide should succeed")
    .expect("IvcCircuit decider yields an accumulator")
}

fn main() {
    const K: u32 = 17;
    const N: usize = 1;
    const STEPS: usize = 2;

    // 1. Run a short IVC chain.
    let srs = load_srs(SrsSource::Midnight, K, IvcCircuit::<PoseidonChain<N>>::cs_degree());
    let (mut prover, verifier) = ivc::setup::<PoseidonChain<N>>(srs, K, ());
    let mut ivc_proof = Vec::new();
    for _ in 0..STEPS {
        ivc_proof = prover.prove_step(()).unwrap();
    }
    let ivc_instance = prover.instance();
    verifier.verify(&ivc_instance, &ivc_proof).unwrap();
    println!("IVC chain of {STEPS} steps produced and natively verified.");

    // 2. Assemble the final circuit's inputs (the same triple an IVC step
    //    consumes: the final state, the carried accumulator and the proof).
    let ivc_vk = verifier.vk().clone();
    let state = *ivc_instance.state();
    let carried_acc = ivc_instance.acc().clone();

    // The exposed public input: the collapsed-and-resolved accumulator
    // (off-circuit mirror of the circuit).
    let merged = final_accumulator::<N>(&ivc_vk, &state, &carried_acc, &ivc_proof);
    let exposed_pi = AssignedAccumulator::<S>::as_public_input(&merged);

    // Sanity: the merged accumulator satisfies the pairing (the decider check).
    assert!(
        merged.check(verifier.params_verifier(), &std::collections::BTreeMap::new()),
        "decider pairing on the compressed accumulator failed"
    );
    println!("Off-circuit decider check on the compressed accumulator passed.");

    let witness = FinalIvcWitness { state, carried_acc, proof: ivc_proof };
    let relation = FinalIvcVerifier::<N> { ivc_vk };

    // 3. Prove & verify the final circuit in-circuit.
    let outer_k = 19;
    let outer_srs = load_srs(
        SrsSource::Midnight,
        outer_k,
        midnight_zk_stdlib::cs_degree(relation.used_chips()),
    );
    let outer_vk = setup_vk(&outer_srs, &relation);
    let outer_pk = setup_pk(&relation, &outer_vk);

    let outer_proof = prove::<FinalIvcVerifier<N>, PoseidonState<F>>(
        &outer_srs,
        &outer_pk,
        &relation,
        &exposed_pi,
        witness,
        OsRng,
    )
    .unwrap();

    midnight_zk_stdlib::verify::<FinalIvcVerifier<N>, PoseidonState<F>>(
        &outer_srs.verifier_params(),
        &outer_vk,
        &exposed_pi,
        None,
        &outer_proof,
    )
    .unwrap();

    println!("In-circuit verification of the complete IVC proof succeeded.");
}
