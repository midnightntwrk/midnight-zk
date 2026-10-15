// [DROP] IVC measurement driver (N = 1). Usage: SRS_DIR=... cargo run --release
// -p midnight-aggregation --example ivc_measure --features truncated-challenges
// (ROWS_ONLY=1 to stop after the cost model). The PCS is the one of DefaultPCS
// and BlstrsEmulation::PCS.

//! Incrementally Verifiable Computation (IVC) using the aggregation API.
//!
//! This example demonstrates how to use the [`Ivc`] API with a transition
//! function that iteratively hashes a value using Poseidon.
//!
//! DO NOT add this example to the CI as it is slow.

use std::time::Instant;

use ff::Field;
use midnight_aggregation::ivc::{self, IvcContext, IvcIO, IvcState, IvcTransition};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, *},
    types::AssignedNative,
    verifier::{BlstrsEmulation, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{
    DefaultPCS, ZkStdLib, ZkStdLibArch,
    utils::plonk_api::{SrsSource, load_srs},
};

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;

/// IVC state: a counter and a hash-chain value.
///
/// A valid IVC state is such that `val` is the result of applying `cnt` rounds
/// of Poseidon to the genesis value of 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct State {
    cnt: F,
    val: F,
}

/// In-circuit counterpart of [`State`].
#[derive(Clone, Debug)]
pub struct AssignedState {
    cnt: AssignedNative<F>,
    val: AssignedNative<F>,
}

/// IVC transition that applies N rounds of Poseidon hashing to the value, and
/// increments the counter by N.
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
        State {
            cnt: F::ZERO,
            val: F::ZERO,
        }
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
    // This transition function is deterministic, it does not depend on a witness.
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
        State {
            cnt: state.cnt + F::from(N as u64),
            val,
        }
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

// ---- Measurement driver (appended to the PoseidonChain definitions of ivc.rs)
// ----
fn main() {
    use std::{fs::File, io::BufWriter, path::Path};

    use midnight_aggregation::ivc::IvcCircuit;
    use midnight_proofs::{
        plonk::ConstraintSystem,
        poly::{EvaluationDomain, kzg::params::ParamsKZG},
        utils::SerdeFormat,
    };
    use midnight_zk_stdlib::MidnightPCS;

    type T = PoseidonChain<1>;

    let relation = |k: u32| {
        let mut cs = ConstraintSystem::default();
        ZkStdLib::configure(&mut cs, (IvcCircuit::<T>::arch(), (k - 1) as u8));
        let domain = EvaluationDomain::new(cs.degree() as u32, k);
        IvcCircuit::<T>::new(domain, cs.into_finalized(), ())
    };

    // The smallest k the circuit fits in, and its number of rows.
    let (k, rows) = (12..=22)
        .find_map(|k| {
            let model = midnight_zk_stdlib::cost_model(&relation(k), Some(k), false);
            (model.k <= k).then_some((k, model.rows))
        })
        .expect("the IVC circuit does not fit in k <= 22");
    println!("RESULT rows={rows} k={k}");
    if std::env::var("ROWS_ONLY").is_ok() {
        return;
    }

    // The SRS: the official file when available, an insecure test one otherwise.
    let j = <DefaultPCS as MidnightPCS>::srs_k(k);
    let srs_dir = std::env::var("SRS_DIR").expect("SRS_DIR must be set");
    let srs_path = format!("{srs_dir}/midnight-srs-2p{j}");
    if !Path::new(&srs_path).exists() {
        eprintln!("generating an insecure test SRS of size 2^{j} at {srs_path}");
        let params = ParamsKZG::<midnight_curves::Bls12>::unsafe_setup(j, rand::rngs::OsRng);
        let mut file = BufWriter::new(File::create(&srs_path).unwrap());
        params.write_custom(&mut file, SerdeFormat::RawBytesUnchecked).unwrap();
        println!("RESULT generated_srs=2p{j}");
    }
    let srs = load_srs::<DefaultPCS>(SrsSource::Midnight, k);

    let start = Instant::now();
    let (mut prover, verifier) = ivc::setup::<T>(srs, k, ());
    println!("RESULT setup_s={:.3}", start.elapsed().as_secs_f64());

    for i in 0..4 {
        let start = Instant::now();
        let proof = prover.prove_step(()).unwrap();
        let prove_s = start.elapsed().as_secs_f64();

        let start = Instant::now();
        verifier.verify(&prover.instance(), &proof).unwrap();
        let verify_s = start.elapsed().as_secs_f64();

        println!(
            "RESULT step={i} prove_s={prove_s:.3} verify_s={verify_s:.3} proof_bytes={}",
            proof.len()
        );
    }
}
