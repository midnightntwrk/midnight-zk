//! Benchmark sweep over `T_MAX_LOG` for the fflonk PCS.
//!
//! Builds a synthetic PLONK circuit (chain of `a^2 + a` mul/add gates,
//! mirroring `benches/plonk.rs`) at a configurable `k`, then runs the full
//! keygen + prove + verify pipeline for each `T_MAX_LOG` in
//! `{0, 1, 2, 3, 4}`, reporting prover time, verifier time, and proof size.
//!
//! `T_MAX_LOG = 0` is byte-identical to baseline KZG, so it doubles as the
//! reference row in the output table.
//!
//! Run with:
//! ```
//! cargo bench -p midnight-proofs --bench fflonk_sweep -- [k_values...]
//! # e.g. cargo bench -p midnight-proofs --bench fflonk_sweep -- 10 12 14
//! ```
//! Defaults to `k = [10, 12, 14]` if no arguments are passed.

use std::{marker::PhantomData, time::Instant};

use blake2b_simd::State as Blake2bState;
use group::ff::Field;
use midnight_curves::{Bls12, Fq as Scalar};
use midnight_proofs::{
    circuit::{Cell, Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk_with_k, prepare, Circuit, Column, ConstraintSystem,
        Constraints, Error, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::{Guard, Params, PolynomialCommitmentScheme},
        fflonk::{FflonkScheme, FflonkVerificationGuard},
        kzg::params::ParamsKZG,
        Rotation,
    },
    transcript::{CircuitTranscript, Transcript},
    utils::rational::Rational,
};
use rand_core::OsRng;

// ---------------------- The benchmark circuit ----------------------
//
// Same shape as `benches/plonk.rs::MyCircuit`: a chain of `a^2 + a` gates
// scaled to fill `~2^(k-1) - 3` rows. Each iteration uses one multiply
// gate + one add gate + two copy constraints. Not zk_stdlib-realistic, but
// has the same shape as a real PLONK proof (advice columns + fixed
// columns + permutation argument), so prover/verifier timing scales like a
// real workload.

#[derive(Clone)]
struct PlonkConfig {
    a: Column<midnight_proofs::plonk::Advice>,
    b: Column<midnight_proofs::plonk::Advice>,
    c: Column<midnight_proofs::plonk::Advice>,
    sa: Column<midnight_proofs::plonk::Fixed>,
    sb: Column<midnight_proofs::plonk::Fixed>,
    sc: Column<midnight_proofs::plonk::Fixed>,
    sm: Column<midnight_proofs::plonk::Fixed>,
}

trait StandardCs<FF: Field> {
    fn raw_multiply<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Value<(Rational<FF>, Rational<FF>, Rational<FF>)>;
    fn raw_add<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Value<(Rational<FF>, Rational<FF>, Rational<FF>)>;
    fn copy(&self, layouter: &mut impl Layouter<FF>, a: Cell, b: Cell) -> Result<(), Error>;
}

#[derive(Clone)]
struct MyCircuit<F: Field> {
    a: Value<F>,
    k: u32,
}

struct StandardPlonk<F: Field> {
    config: PlonkConfig,
    _marker: PhantomData<F>,
}

impl<FF: Field> StandardCs<FF> for StandardPlonk<FF> {
    fn raw_multiply<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        mut f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Value<(Rational<FF>, Rational<FF>, Rational<FF>)>,
    {
        layouter.assign_region(
            || "raw_multiply",
            |mut region| {
                let mut value = None;
                let lhs = region.assign_advice(
                    || "lhs",
                    self.config.a,
                    0,
                    || {
                        value = Some(f());
                        value.unwrap().map(|v| v.0)
                    },
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    self.config.b,
                    0,
                    || value.unwrap().map(|v| v.1),
                )?;
                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value.unwrap().map(|v| v.2),
                )?;
                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(FF::ZERO))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(FF::ZERO))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(FF::ONE))?;
                Ok((lhs.cell(), rhs.cell(), out.cell()))
            },
        )
    }
    fn raw_add<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        mut f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Value<(Rational<FF>, Rational<FF>, Rational<FF>)>,
    {
        layouter.assign_region(
            || "raw_add",
            |mut region| {
                let mut value = None;
                let lhs = region.assign_advice(
                    || "lhs",
                    self.config.a,
                    0,
                    || {
                        value = Some(f());
                        value.unwrap().map(|v| v.0)
                    },
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    self.config.b,
                    0,
                    || value.unwrap().map(|v| v.1),
                )?;
                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value.unwrap().map(|v| v.2),
                )?;
                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(FF::ZERO))?;
                Ok((lhs.cell(), rhs.cell(), out.cell()))
            },
        )
    }
    fn copy(&self, layouter: &mut impl Layouter<FF>, left: Cell, right: Cell) -> Result<(), Error> {
        layouter.assign_region(|| "copy", |mut region| region.constrain_equal(left, right))
    }
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            a: Value::unknown(),
            k: self.k,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        meta.set_minimum_degree(5);

        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);

        let sm = meta.fixed_column();
        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();

        meta.create_gate("Combined add-mult", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let sm = meta.query_fixed(sm, Rotation::cur());
            Constraints::without_selector(vec![&a * sa + &b * sb + a * b * sm - (c * sc)])
        });

        PlonkConfig {
            a,
            b,
            c,
            sa,
            sb,
            sc,
            sm,
        }
    }

    fn synthesize(&self, config: PlonkConfig, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let cs = StandardPlonk {
            config,
            _marker: PhantomData::<F>,
        };

        // Half-fill the domain: each loop iteration is two regions (a
        // multiply + an add), each one row. Filling exactly to the domain
        // edge trips `NotEnoughRowsAvailable` once blinding/permutation
        // overhead is counted, so we leave headroom.
        let iters = (1usize << self.k) / 4;
        for _ in 0..iters {
            let a: Value<Rational<_>> = self.a.into();
            let mut a_squared = Value::unknown();
            let (a0, _, c0) = cs.raw_multiply(&mut layouter, || {
                a_squared = a.square();
                a.zip(a_squared).map(|(a, a_squared)| (a, a, a_squared))
            })?;
            let (a1, b1, _) = cs.raw_add(&mut layouter, || {
                let fin = a_squared + a;
                a.zip(a_squared).zip(fin).map(|((a, a_squared), fin)| (a, a_squared, fin))
            })?;
            cs.copy(&mut layouter, a0, a1)?;
            cs.copy(&mut layouter, b1, c0)?;
        }
        Ok(())
    }
}

// ---------------------- One sweep entry ----------------------

#[derive(Debug, Clone, Copy)]
struct SweepRow {
    t_max_log: u32,
    k: u32,
    /// Time to materialise the SRS (`unsafe_setup` + `downsize_lagrange` if
    /// the monomial basis is extended). In production this is a one-shot
    /// file load, not a per-circuit cost — shown here for the bench's own
    /// sake. Grows with `T_MAX_LOG`.
    srs_ms: u128,
    /// `keygen_vk_with_k` + `keygen_pk`. Independent of `T_MAX_LOG` —
    /// the protocol's keygen path consults only `params.g_lagrange` (sized
    /// to the circuit `k`, not the monomial extension).
    keygen_ms: u128,
    prove_ms: u128,
    verify_us: u128,
    proof_bytes: usize,
    srs_g_len: usize,
}

/// Builds an SRS large enough for `FflonkScheme<Bls12, T_MAX_LOG>` at
/// circuit size `k`. Uses
/// [`PolynomialCommitmentScheme::srs_monomial_blowup`] to learn the factor
/// (depends on `T_MAX_LOG` and the `single-h-commitment` feature) and
/// extends via [`ParamsKZG::with_extended_monomial`].
///
/// `cs_degree = 5` matches the synthetic circuit above (set via
/// `meta.set_minimum_degree(5)`). For a different test workload, pass the
/// correct degree.
fn build_srs<const T_MAX_LOG: u32>(k: u32, cs_degree: usize) -> ParamsKZG<Bls12> {
    let blowup =
        <FflonkScheme<Bls12, T_MAX_LOG> as PolynomialCommitmentScheme<Scalar>>::srs_monomial_blowup(
            cs_degree,
        );
    if blowup <= 1 {
        return ParamsKZG::unsafe_setup(k, OsRng);
    }
    // `with_extended_monomial` requires the base and extended SRSs to share
    // a `g` prefix — true when both come from a real ceremony, false for
    // two independent `unsafe_setup` calls. So we synthesise the larger
    // SRS in one shot at `extended_k` and downsize its Lagrange basis to
    // the circuit's `k`. One curve-ops pass instead of three.
    let extended_k = k + (blowup as f64).log2().ceil() as u32;
    let mut srs: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(extended_k, OsRng);
    srs.downsize_lagrange(k);
    srs
}

fn bench_one<const T_MAX_LOG: u32>(k: u32, cs_degree: usize) -> SweepRow {
    // ---- SRS materialisation (production-time = file load) ----
    let t_srs = Instant::now();
    let srs = build_srs::<T_MAX_LOG>(k, cs_degree);
    let srs_ms = t_srs.elapsed().as_millis();

    // ---- VK + PK keygen (independent of T_MAX_LOG) ----
    let t_keygen = Instant::now();
    let empty_circuit: MyCircuit<Scalar> = MyCircuit {
        a: Value::unknown(),
        k,
    };
    let vk: VerifyingKey<Scalar, FflonkScheme<Bls12, T_MAX_LOG>> =
        keygen_vk_with_k(&srs, &empty_circuit, k).expect("keygen_vk");
    let pk: ProvingKey<Scalar, FflonkScheme<Bls12, T_MAX_LOG>> =
        keygen_pk(vk.clone(), &empty_circuit).expect("keygen_pk");
    let keygen_ms = t_keygen.elapsed().as_millis();

    // ---- Prove ----
    let circuit: MyCircuit<Scalar> = MyCircuit {
        a: Value::known(Scalar::random(OsRng)),
        k,
    };
    let t1 = Instant::now();
    let mut transcript: CircuitTranscript<Blake2bState> = CircuitTranscript::init();
    create_proof::<Scalar, FflonkScheme<Bls12, T_MAX_LOG>, _, _>(
        &srs,
        &pk,
        &circuit,
        #[cfg(feature = "committed-instances")]
        0,
        &[],
        &mut transcript,
        OsRng,
    )
    .expect("create_proof");
    let proof = transcript.finalize();
    let prove_ms = t1.elapsed().as_millis();
    let proof_bytes = proof.len();

    // ---- Verify ----
    let t2 = Instant::now();
    let mut transcript: CircuitTranscript<Blake2bState> = CircuitTranscript::init_from_bytes(&proof);
    let guard: FflonkVerificationGuard<Bls12, T_MAX_LOG> =
        prepare::<Scalar, FflonkScheme<Bls12, T_MAX_LOG>, _>(
            &vk,
            #[cfg(feature = "committed-instances")]
            &[],
            &[],
            &mut transcript,
        )
        .expect("prepare");
    let verifier_params = srs.verifier_params();
    assert!(
        <FflonkVerificationGuard<Bls12, T_MAX_LOG> as Guard<
            Scalar,
            FflonkScheme<Bls12, T_MAX_LOG>,
        >>::verify(guard, &verifier_params)
        .is_ok(),
        "verification failed for T_MAX_LOG={T_MAX_LOG}, k={k}"
    );
    let verify_us = t2.elapsed().as_micros();

    SweepRow {
        t_max_log: T_MAX_LOG,
        k,
        srs_ms,
        keygen_ms,
        prove_ms,
        verify_us,
        proof_bytes,
        srs_g_len: srs.g_monomial_size(),
    }
}

fn print_row(r: &SweepRow) {
    println!(
        "  T_MAX_LOG={:>2}  k={:>2}  srs={:>6}ms  keygen={:>5}ms  prove={:>6}ms  \
         verify={:>6}μs  proof={:>5}B  SRS|g|=2^{}",
        r.t_max_log,
        r.k,
        r.srs_ms,
        r.keygen_ms,
        r.prove_ms,
        r.verify_us,
        r.proof_bytes,
        (r.srs_g_len as f64).log2().round() as u32,
    );
}

fn main() {
    // Parse k values from CLI args; defaults are small/medium/large.
    let ks: Vec<u32> = std::env::args()
        .skip(1)
        .filter_map(|s| s.parse::<u32>().ok())
        .collect::<Vec<_>>();
    let ks = if ks.is_empty() { vec![10, 12, 14] } else { ks };

    // Synthetic circuit's constraint-system degree comes from
    // `meta.set_minimum_degree(5)` in `MyCircuit::configure`.
    const CS_DEGREE: usize = 5;

    println!("fflonk-sweep (synthetic PLONK circuit, cs_degree = {CS_DEGREE})");
    println!("Each row is a single full keygen + prove + verify run (no statistics).");
    println!();

    for &k in &ks {
        println!("[k = {k}]");
        // Macro-expanded sweep: const generic can't be a runtime value, so
        // we expand by hand. Add a line per new T_MAX_LOG value to sweep.
        print_row(&bench_one::<0>(k, CS_DEGREE));
        print_row(&bench_one::<1>(k, CS_DEGREE));
        print_row(&bench_one::<2>(k, CS_DEGREE));
        print_row(&bench_one::<3>(k, CS_DEGREE));
        print_row(&bench_one::<4>(k, CS_DEGREE));
        println!();
    }
}
