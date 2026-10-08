//! The verifier must reject a malformed proof with an error, never panic: it verifies proofs
//! from untrusted provers. A prover chooses the evaluations it writes after `x`, so it can make
//! any expression of them take a chosen value - here `−β`, which zeroes a logup input `f + β`.

use std::{
    io::{self, Cursor},
    panic::{self, AssertUnwindSafe},
};

use blake2b_simd::State;
use midnight_curves::{Bls12, Fq as Scalar};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Selector, TableColumn,
        VerifyingKey, create_proof, keygen_pk, keygen_vk, prepare,
    },
    poly::{
        PolynomialLabel, Rotation,
        commitment::Guard,
        kzg::{
            KZGCommitmentScheme,
            commitment::KZGMultiCommitment,
            params::{ParamsKZG, ParamsVerifierKZG},
        },
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
};
use rand_core::OsRng;

const K: u32 = 5;

/// One advice column looked up, unselected, in an 8-row table: the logup input is `a(x)`.
#[derive(Clone, Default)]
struct LookupCircuit;

#[derive(Clone)]
struct LookupConfig {
    a: Column<Advice>,
    table: TableColumn,
}

impl Circuit<Scalar> for LookupCircuit {
    type Config = LookupConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> LookupConfig {
        let a = meta.advice_column();
        let table = meta.lookup_table_column();
        meta.lookup("a in table", None, |meta| {
            vec![(meta.query_advice(a, Rotation::cur()), table)]
        });
        LookupConfig { a, table }
    }

    fn synthesize(
        &self,
        config: LookupConfig,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "0..8",
            |mut table| {
                for row in 0..8u64 {
                    table.assign_cell(
                        || "t",
                        config.table,
                        row as usize,
                        || Value::known(Scalar::from(row)),
                    )?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "a",
            |mut region| {
                for row in 0..16u64 {
                    region.assign_advice(
                        || "a",
                        config.a,
                        row as usize,
                        || Value::known(Scalar::from(row % 8)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

/// A transcript over a real proof that replaces its `target`-th read with `−β` (the second
/// challenge squeezed), absorbing the replacement as an honest read would.
#[derive(Clone)]
struct InjectingTranscript {
    inner: CircuitTranscript<State>,
    squeezes: usize,
    reads: usize,
    target: Option<usize>,
    beta: Option<Scalar>,
}

impl Transcript for InjectingTranscript {
    type Hash = State;

    fn init() -> Self {
        unimplemented!("only reads proofs")
    }

    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            inner: CircuitTranscript::init_from_bytes(bytes),
            squeezes: 0,
            reads: 0,
            target: None,
            beta: None,
        }
    }

    fn squeeze_challenge<T: Sampleable<State>>(&mut self) -> T {
        self.squeezes += 1;
        if self.squeezes == 2 {
            self.beta = Some(self.inner.clone().squeeze_challenge());
        }
        self.inner.squeeze_challenge()
    }

    fn common<T: Hashable<State>>(&mut self, input: &T) -> io::Result<()> {
        self.inner.common(input)
    }

    fn read<T: Hashable<State>>(&mut self) -> io::Result<T> {
        let index = self.reads;
        self.reads += 1;
        match (self.target, self.beta) {
            (Some(target), Some(beta)) if target == index => {
                // Skip the honest value, then read and absorb `−β` in its place.
                T::read(self.inner.buffer())?;
                let bytes = <Scalar as Hashable<State>>::to_bytes(&-beta);
                let forged = T::read(&mut Cursor::new(bytes))?;
                self.inner.common(&forged)?;
                Ok(forged)
            }
            _ => self.inner.read(),
        }
    }

    fn write<T: Hashable<State>>(&mut self, _: &T) -> io::Result<()> {
        unimplemented!("only reads proofs")
    }

    fn finalize(self) -> Vec<u8> {
        self.inner.finalize()
    }

    fn assert_empty(&mut self) -> io::Result<()> {
        self.inner.assert_empty()
    }
}

#[test]
fn verifier_rejects_forged_evaluations_without_panicking() {
    type Scheme = KZGCommitmentScheme<Bls12>;
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);
    let vk = keygen_vk::<_, Scheme, _>(&params, &LookupCircuit).expect("keygen_vk");
    let pk = keygen_pk(vk.clone(), &LookupCircuit).expect("keygen_pk");

    let mut transcript = CircuitTranscript::<State>::init();
    create_proof::<Scalar, Scheme, _, _>(
        &params,
        &pk,
        &LookupCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        &[],
        &mut transcript,
        OsRng,
    )
    .expect("proof");
    let proof = transcript.finalize();

    let verify = |target: Option<usize>| {
        let mut t = InjectingTranscript::init_from_bytes(&proof);
        t.target = target;
        let guard = prepare::<Scalar, Scheme, _>(
            &vk,
            #[cfg(feature = "committed-instances")]
            &[],
            &[],
            &mut t,
        )?;
        t.assert_empty().map_err(|_| Error::Opening)?;
        guard.verify(&params.verifier_params()).map_err(|_| Error::Opening)?;
        Ok::<_, Error>(t.reads)
    };

    // Positive control: the honest proof verifies, and tells us how many reads there are.
    let reads = verify(None).expect("honest proof verifies");

    let mut panicked = vec![];
    for target in 0..reads {
        if panic::catch_unwind(AssertUnwindSafe(|| verify(Some(target)))).is_err() {
            panicked.push(target);
        }
    }
    assert!(
        panicked.is_empty(),
        "the verifier panicked (instead of rejecting) when read(s) {panicked:?} of {reads} \
         were replaced by −β"
    );
}

type Scheme = KZGCommitmentScheme<Bls12>;

/// Verifies `proof` as a caller should: `prepare`, an empty transcript, then the pairing check.
fn verify_bytes(
    params: &ParamsVerifierKZG<Bls12>,
    vk: &VerifyingKey<Scalar, Scheme>,
    #[cfg(feature = "committed-instances")] committed: &[KZGMultiCommitment<Bls12>],
    instances: &[&[Scalar]],
    proof: &[u8],
) -> Result<(), Error> {
    let mut t = CircuitTranscript::<State>::init_from_bytes(proof);
    let guard = prepare::<Scalar, Scheme, _>(
        vk,
        #[cfg(feature = "committed-instances")]
        committed,
        instances,
        &mut t,
    )?;
    t.assert_empty().map_err(|_| Error::Opening)?;
    guard.verify(params).map_err(|_| Error::Opening)
}

/// Corrupting any byte of a proof - group counts, point encodings, field encodings - must make
/// the verifier reject, never panic. Also truncated and extended proofs.
#[test]
fn verifier_survives_every_corrupted_byte() {
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);
    let vk = keygen_vk::<_, Scheme, _>(&params, &LookupCircuit).expect("keygen_vk");
    let pk = keygen_pk(vk.clone(), &LookupCircuit).expect("keygen_pk");
    let mut transcript = CircuitTranscript::<State>::init();
    create_proof::<Scalar, Scheme, _, _>(
        &params,
        &pk,
        &LookupCircuit,
        #[cfg(feature = "committed-instances")]
        0,
        &[],
        &mut transcript,
        OsRng,
    )
    .expect("proof");
    let proof = transcript.finalize();
    let vparams = params.verifier_params();
    let run = |bytes: &[u8]| {
        panic::catch_unwind(AssertUnwindSafe(|| {
            verify_bytes(
                &vparams,
                &vk,
                #[cfg(feature = "committed-instances")]
                &[],
                &[],
                bytes,
            )
        }))
    };
    assert!(matches!(run(&proof), Ok(Ok(()))), "honest proof verifies");

    let mut panicked = vec![];
    let mut accepted = vec![];
    for i in 0..proof.len() {
        for mask in [0x01u8, 0x80, 0xff] {
            let mut bytes = proof.clone();
            bytes[i] ^= mask;
            match run(&bytes) {
                Err(_) => panicked.push((i, mask)),
                Ok(Ok(())) => accepted.push((i, mask)),
                Ok(Err(_)) => {}
            }
        }
    }
    for cut in [1, 32, 48, proof.len() / 2] {
        if run(&proof[..proof.len() - cut]).is_err() {
            panicked.push((proof.len() - cut, 0));
        }
    }
    let mut longer = proof.clone();
    longer.push(0);
    if run(&longer).is_err() {
        panicked.push((proof.len(), 0));
    }
    assert!(
        accepted.is_empty(),
        "corrupted proofs accepted at (byte, mask) {accepted:?}"
    );
    assert!(
        panicked.is_empty(),
        "the verifier panicked at (byte, mask) {panicked:?}"
    );
}

/// The lookup circuit plus a committed instance column, constrained to equal `a` on row 0.
#[derive(Clone, Default)]
struct CommittedCircuit;

#[derive(Clone)]
struct CommittedConfig {
    lookup: LookupConfig,
    q: Selector,
}

impl Circuit<Scalar> for CommittedCircuit {
    type Config = CommittedConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> CommittedConfig {
        let lookup = LookupCircuit::configure(meta);
        let p = meta.instance_column();
        let q = meta.selector();
        meta.create_gate("a = p", |meta| {
            let a = meta.query_advice(lookup.a, Rotation::cur());
            let p = meta.query_instance(p, Rotation::cur());
            Constraints::with_selector(q, vec![a - p])
        });
        CommittedConfig { lookup, q }
    }

    fn synthesize(
        &self,
        config: CommittedConfig,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_region(|| "q", |mut region| config.q.enable(&mut region, 0))?;
        LookupCircuit.synthesize(config.lookup, layouter)
    }
}

/// A committed instance whose label is not `CommittedInstance(i)` is a caller error: the
/// verifier should reject it rather than panic. (The ledger always passes a correctly
/// labelled zero commitment, so this is an API contract, not reachable from proof bytes.)
#[cfg(feature = "committed-instances")]
#[test]
fn verifier_rejects_mislabelled_committed_instance() {
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, OsRng);
    let vk = keygen_vk::<_, Scheme, _>(&params, &CommittedCircuit).expect("keygen_vk");
    let pk = keygen_pk(vk.clone(), &CommittedCircuit).expect("keygen_pk");
    let mut transcript = CircuitTranscript::<State>::init();
    create_proof::<Scalar, Scheme, _, _>(
        &params,
        &pk,
        &CommittedCircuit,
        1,
        &[&[]],
        &mut transcript,
        OsRng,
    )
    .expect("proof");
    let proof = transcript.finalize();
    let vparams = params.verifier_params();
    let run = |label: PolynomialLabel| {
        let committed = [KZGMultiCommitment::commitment_to_zero(label)];
        panic::catch_unwind(AssertUnwindSafe(|| {
            verify_bytes(&vparams, &vk, &committed, &[], &proof)
        }))
    };
    assert!(
        matches!(run(PolynomialLabel::CommittedInstance(0)), Ok(Ok(()))),
        "honest proof verifies with a correctly labelled committed instance"
    );
    for label in [
        PolynomialLabel::NoLabel,
        PolynomialLabel::CommittedInstance(1),
    ] {
        assert!(
            matches!(run(label.clone()), Ok(Err(_))),
            "the verifier panicked (or accepted) with committed instance label {label:?}"
        );
    }
}
