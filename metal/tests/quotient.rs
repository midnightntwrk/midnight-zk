// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

//! The device quotient against the references of midnight-proofs, on the
//! jobs of real proofs seen by a quotient hook installed here.

#![cfg(target_os = "macos")]

mod common;

use std::{
    collections::HashMap,
    ffi::c_void,
    mem::{align_of, offset_of, size_of},
    sync::{Mutex, MutexGuard, atomic::Ordering::Relaxed},
};

use ff::Field;
use midnight_curves::Fq;
use midnight_metal::{
    self as metal, Scalar, field::FR_MODULUS, quotient_abi as ma, quotient_test_support as qt,
};
use midnight_proofs::gpu::{
    self as hooks, DeviceProgram, LookupJob, PermutationJob, QuotientDivide, QuotientJob, TrashJob,
    abi::{self as pa, PackedJob, ProgramAbi},
    adapter::{from_scalar, scalars},
    test_switches::{self, QUOTIENT_CHECK, RandomCircuit},
};

macro_rules! same_layout {
    ($a:ty, $b:ty: $($f:ident),*) => {
        assert_eq!(size_of::<$a>(), size_of::<$b>(), stringify!($a));
        assert_eq!(align_of::<$a>(), align_of::<$b>(), stringify!($a));
        $(assert_eq!(offset_of!($a, $f), offset_of!($b, $f), stringify!($a.$f));)*
    };
}

macro_rules! same_consts {
    ($($c:ident),*) => { $(assert_eq!(ma::$c, hooks::$c, stringify!($c));)* };
}

/// The crate's copy of the job types matches `midnight_proofs::gpu::abi`.
#[test]
fn abi_layout_matches() {
    same_layout! { ma::DeviceOp, hooks::DeviceOp: kind, dst, a, b, c }
    same_layout! { ma::DeviceRead, hooks::DeviceRead: kind, column, rotation }
    same_layout! { ma::ProgramAbi, pa::ProgramAbi:
    ops, nops, reads, nreads, uniforms, nuniforms, outputs, noutputs, nslots, pad }
    same_layout! { ma::LookupAbi, pa::LookupAbi:
    aggregator, multiplicities, helpers, programs, nchunks }
    same_layout! { ma::TrashAbi, pa::TrashAbi: trash, program, selector_column, pad }
    same_layout! { ma::QuotientJobAbi, pa::QuotientJobAbi:
    abi, k, ext_k, nslots, zeta, extended_omega, y, beta, gamma, delta_start, delta,
    advice, nadvice, instance, ninstance, fixed, nfixed, l0, l_last, l_active, gates,
    perm_ncolumns, perm_column_kind, perm_column_index, perm_sigma, perm_products,
    perm_nsets, perm_chunk_len, perm_last_rotation, lookups, nlookups, trash, ntrash,
    t_inv, nt_inv, omega_inv, divisor, zeta_out, len }
    assert_eq!(ma::QUOTIENT_ABI, pa::QUOTIENT_ABI);
    same_consts! { TAG_UNIFORM, TAG_READ, TAG_SLOT, INDEX_MASK }
    same_consts! { OP_ADD, OP_SUB, OP_MUL, OP_SQUARE, OP_DOUBLE, OP_NEGATE, OP_MUL_ADD }
    same_consts! { COLUMN_FIXED, COLUMN_ADVICE, COLUMN_INSTANCE }
}

/// While `Some`, the quotient hook keeps a copy of every job it sees.
static CAPTURED: Mutex<Option<Vec<OwnedJob>>> = Mutex::new(None);

unsafe fn quotient_hook(job: *const c_void, out: &mut [Scalar]) -> bool {
    if let Some(jobs) = CAPTURED.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
        // SAFETY: the prover's job, within its call.
        jobs.push(OwnedJob::of(&unsafe {
            job_of(&*(job as *const pa::QuotientJobAbi))
        }));
    }
    // SAFETY: as above.
    unsafe { metal::quotient(job, out) }
}

fn lock() -> MutexGuard<'static, ()> {
    let g = common::serial();
    common::install_hooks(quotient_hook);
    *CAPTURED.lock().unwrap_or_else(|e| e.into_inner()) = None;
    QUOTIENT_CHECK.store(false, Relaxed);
    metal::set_min_k(1);
    qt::set_memory_limit(None);
    g
}

/// Copies of the quotient jobs of the proofs `prove` makes.
fn capture(prove: impl FnOnce()) -> Vec<OwnedJob> {
    *CAPTURED.lock().unwrap_or_else(|e| e.into_inner()) = Some(Vec::new());
    prove();
    CAPTURED.lock().unwrap_or_else(|e| e.into_inner()).take().unwrap()
}

/// The job of a random circuit, proved once per process.
fn job_of_circuit(seed: u64, k: u32) -> OwnedJob {
    static JOBS: Mutex<Vec<((u64, u32), OwnedJob)>> = Mutex::new(Vec::new());
    let mut jobs = JOBS.lock().unwrap_or_else(|e| e.into_inner());
    if let Some((_, j)) = jobs.iter().find(|(key, _)| *key == (seed, k)) {
        return j.clone();
    }
    let j = capture(|| drop(RandomCircuit::new(seed, false, k).prove())).remove(0);
    jobs.push(((seed, k), j.clone()));
    j
}

/// # Safety
/// For a non-zero count, `p` is valid for `n` reads for `'a`.
unsafe fn sl<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if n == 0 {
        &[]
    } else {
        // SAFETY: the caller's contract.
        unsafe { std::slice::from_raw_parts(p, n) }
    }
}

/// # Safety
/// `p` is a valid program.
unsafe fn program(p: &ProgramAbi) -> DeviceProgram<Fq> {
    // SAFETY: the caller's contract.
    unsafe {
        DeviceProgram {
            uniforms: sl(p.uniforms, p.nuniforms).iter().map(|u| from_scalar(*u)).collect(),
            reads: sl(p.reads, p.nreads).to_vec(),
            ops: sl(p.ops, p.nops).to_vec(),
            nslots: p.nslots,
            outputs: sl(p.outputs, p.noutputs).to_vec(),
        }
    }
}

/// The `QuotientJob` of a packed job.
///
/// # Safety
/// `j` is a valid packed job whose pointers live while the result is used.
unsafe fn job_of<'a>(j: &'a pa::QuotientJobAbi) -> QuotientJob<'a, Fq> {
    let (n, en) = (1usize << j.k, 1usize << j.ext_k);
    // SAFETY (all): the caller's contract; `Fq` is the transparent `blst_fr`
    // of `Scalar`.
    unsafe {
        let poly = |p: *const Scalar, len: usize| sl(p as *const Fq, len);
        let polys = |ps: *const *const Scalar, c: usize, len: usize| -> Vec<&'a [Fq]> {
            sl(ps, c).iter().map(|p| poly(*p, len)).collect()
        };
        QuotientJob {
            k: j.k,
            ext_k: j.ext_k,
            zeta: j.zeta.map(from_scalar),
            extended_omega: from_scalar(j.extended_omega),
            advice: polys(j.advice, j.nadvice, n),
            instance: polys(j.instance, j.ninstance, n),
            fixed: sl(j.fixed, j.nfixed)
                .iter()
                .map(|p| (!p.is_null()).then(|| poly(*p, en)))
                .collect(),
            l0: poly(j.l0, en),
            l_last: poly(j.l_last, en),
            l_active: poly(j.l_active, en),
            y: from_scalar(j.y),
            beta: from_scalar(j.beta),
            gamma: from_scalar(j.gamma),
            delta_start: from_scalar(j.delta_start),
            delta: from_scalar(j.delta),
            gates: program(&j.gates),
            permutation: (j.perm_nsets > 0).then(|| PermutationJob {
                chunk_len: j.perm_chunk_len,
                columns: sl(j.perm_column_kind, j.perm_ncolumns)
                    .iter()
                    .copied()
                    .zip(sl(j.perm_column_index, j.perm_ncolumns).iter().copied())
                    .collect(),
                sigma: polys(j.perm_sigma, j.perm_ncolumns, en),
                products: polys(j.perm_products, j.perm_nsets, n),
                last_rotation: j.perm_last_rotation,
            }),
            lookups: sl(j.lookups, j.nlookups)
                .iter()
                .map(|l| LookupJob {
                    aggregator: poly(l.aggregator, n),
                    multiplicities: poly(l.multiplicities, n),
                    helpers: polys(l.helpers, l.nchunks, n),
                    programs: sl(l.programs, l.nchunks).iter().map(|p| program(p)).collect(),
                })
                .collect(),
            trash: sl(j.trash, j.ntrash)
                .iter()
                .map(|t| TrashJob {
                    trash: poly(t.trash, n),
                    selector_column: t.selector_column,
                    program: program(&t.program),
                })
                .collect(),
            divide: QuotientDivide {
                t_inv: poly(j.t_inv, j.nt_inv).to_vec(),
                omega_inv: from_scalar(j.omega_inv),
                divisor: from_scalar(j.divisor),
                zeta_out: j.zeta_out.map(from_scalar),
                len: j.len,
            },
        }
    }
}

/// `j` with every polynomial replaced by `f` of it, visited in a fixed order.
fn remap<'a, 'b>(
    j: &QuotientJob<'a, Fq>,
    f: &mut dyn FnMut(&'a [Fq]) -> &'b [Fq],
) -> QuotientJob<'b, Fq> {
    QuotientJob {
        advice: j.advice.iter().map(|&p| f(p)).collect(),
        instance: j.instance.iter().map(|&p| f(p)).collect(),
        fixed: j.fixed.iter().map(|p| p.map(&mut *f)).collect(),
        l0: f(j.l0),
        l_last: f(j.l_last),
        l_active: f(j.l_active),
        permutation: j.permutation.as_ref().map(|p| PermutationJob {
            sigma: p.sigma.iter().map(|&s| f(s)).collect(),
            products: p.products.iter().map(|&s| f(s)).collect(),
            columns: p.columns.clone(),
            chunk_len: p.chunk_len,
            last_rotation: p.last_rotation,
        }),
        lookups: j
            .lookups
            .iter()
            .map(|l| LookupJob {
                aggregator: f(l.aggregator),
                multiplicities: f(l.multiplicities),
                helpers: l.helpers.iter().map(|&h| f(h)).collect(),
                programs: l.programs.clone(),
            })
            .collect(),
        trash: j
            .trash
            .iter()
            .map(|t| TrashJob {
                trash: f(t.trash),
                selector_column: t.selector_column,
                program: t.program.clone(),
            })
            .collect(),
        k: j.k,
        ext_k: j.ext_k,
        zeta: j.zeta,
        extended_omega: j.extended_omega,
        y: j.y,
        beta: j.beta,
        gamma: j.gamma,
        delta_start: j.delta_start,
        delta: j.delta,
        gates: j.gates.clone(),
        divide: j.divide.clone(),
    }
}

/// A copy of a job that keeps the aliasing of its polynomials.
#[derive(Clone)]
struct OwnedJob {
    /// Each distinct polynomial once, in first-use order.
    polys: Vec<Vec<Fq>>,
    /// The polynomial of each slice `remap` visits.
    order: Vec<usize>,
    /// The job with every polynomial empty.
    template: QuotientJob<'static, Fq>,
}

impl OwnedJob {
    fn of(j: &QuotientJob<'_, Fq>) -> Self {
        let (mut polys, mut order, mut seen) = (Vec::new(), Vec::new(), HashMap::new());
        let template = remap(j, &mut |p| {
            let i = *seen.entry(p.as_ptr()).or_insert_with(|| {
                polys.push(p.to_vec());
                polys.len() - 1
            });
            order.push(i);
            &[]
        });
        OwnedJob {
            polys,
            order,
            template,
        }
    }

    fn job(&self) -> QuotientJob<'_, Fq> {
        let mut i = self.order.iter();
        remap(&self.template, &mut |_| {
            self.polys[*i.next().unwrap()].as_slice()
        })
    }

    /// The proving-key polynomials (the extended ones), in first-use order.
    fn keys(&self) -> Vec<&[Scalar]> {
        let en = 1 << self.template.ext_k;
        self.polys.iter().filter(|p| p.len() == en).map(|p| scalars(p)).collect()
    }

    fn bump_key(&mut self, key: usize, at: usize, by: Fq) {
        let en = 1 << self.template.ext_k;
        self.polys.iter_mut().filter(|p| p.len() == en).nth(key).unwrap()[at] += by;
    }

    fn need_bytes(&self) -> u64 {
        let job = self.job();
        // SAFETY: the packed job lives for the call.
        unsafe { qt::need_bytes_job(PackedJob::new(&job).as_ptr()) }.expect("checks pass") as u64
    }

    /// The device quotient, asserted served, and the stages of the call.
    fn serve(&self) -> (Vec<Scalar>, metal::QuotientStages) {
        let job = self.job();
        let packed = PackedJob::new(&job);
        let mut out = vec![[0u64; 4]; job.divide.len];
        // SAFETY: the packed job lives for the call.
        let served = unsafe { metal::quotient(packed.as_ptr(), &mut out) };
        assert!(served, "declined: {:?}", metal::declines());
        (out, qt::last_stages().unwrap())
    }

    fn reference(&self) -> Vec<Scalar> {
        let job = self.job();
        scalars(job.divide_reference(job.numerator_reference()).as_slice()).to_vec()
    }
}

fn abi(p: &PackedJob) -> &pa::QuotientJobAbi {
    // SAFETY: a packed job points to its `QuotientJobAbi`.
    unsafe { &*(p.as_ptr() as *const pa::QuotientJobAbi) }
}

/// The device numerator on every row of the extended domain and the device
/// quotient against `numerator_reference` and `divide_reference`.
fn check_reference(j: &OwnedJob) {
    let job = j.job();
    let nu_ref = job.numerator_reference();
    // SAFETY: the packed job lives for the call.
    let nu = unsafe { qt::numerator(PackedJob::new(&job).as_ptr()) }.expect("the device numerator");
    assert!(nu == scalars(nu_ref.as_slice()), "{job:?}: numerator");
    let h = job.divide_reference(nu_ref);
    assert!(j.serve().0 == scalars(h.as_slice()), "{job:?}: quotient");
}

mod range {
    //! `RangeCheckChip` with two groups of four lookup lanes: a lookup of
    //! several chunks.

    use ff::Field;
    use midnight_circuits::{
        field::{NativeChip, NativeConfig, RangeCheckChip, RangeCheckConfig},
        testing_utils::FromScratch,
        types::{AssignedNative, ComposableChip},
    };
    use midnight_curves::{Bls12, Fq};
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        gpu::test_switches::set_quotient_blinding_seed,
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Fixed, Instance,
            ProvingKey, Selector, create_proof, keygen_pk, keygen_vk_with_k, prepare,
        },
        poly::{
            Rotation,
            commitment::Guard,
            kzg::{KZGCommitmentScheme, params::ParamsKZG},
        },
        transcript::{Blake2b256, CircuitTranscript, Transcript},
    };
    use rand_chacha::ChaCha20Rng;
    use rand_core::{RngCore, SeedableRng};

    type Scheme = KZGCommitmentScheme<Bls12>;
    const BITS: usize = 8;
    const GROUPS: usize = 2;

    #[derive(Clone, Debug)]
    pub struct Config {
        range: RangeCheckConfig<Fq>,
        native: NativeConfig,
        src: [Column<Advice>; 2],
        inst: Column<Instance>,
        q: Selector,
    }

    #[derive(Clone, Debug, Default)]
    pub struct RangeCircuit {
        seed: u64,
        rows: usize,
    }

    impl RangeCircuit {
        fn values(&self) -> Vec<Fq> {
            let mut rng = ChaCha20Rng::seed_from_u64(self.seed);
            (0..self.rows).map(|_| Fq::from(rng.next_u64() % (1 << BITS))).collect()
        }
    }

    impl Circuit<Fq> for RangeCircuit {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            self.clone()
        }

        fn configure(meta: &mut ConstraintSystem<Fq>) -> Config {
            let lanes: Vec<Column<Advice>> =
                (0..5 * GROUPS).map(|_| meta.advice_column()).collect();
            let fixed: Vec<Column<Fixed>> = (0..GROUPS + 3).map(|_| meta.fixed_column()).collect();
            let src = [meta.advice_column(), meta.advice_column()];
            meta.enable_equality(src[0]);
            let inst = meta.instance_column();
            meta.enable_equality(inst);
            let q = meta.selector();
            meta.create_gate("square plus", |vc| {
                let a = vc.query_advice(src[0], Rotation::cur());
                let b = vc.query_advice(src[1], Rotation::cur());
                Constraints::with_selector(q, vec![a.clone() * a.clone() + a - b])
            });
            let native =
                NativeChip::configure_from_scratch(meta, &mut vec![], &mut vec![], &[inst, inst]);
            let range = RangeCheckChip::configure(meta, &(lanes, fixed, BITS));
            Config {
                range,
                native,
                src,
                inst,
                q,
            }
        }

        fn synthesize(&self, cfg: Config, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
            let cells = layouter.assign_region(
                || "values",
                |mut region| {
                    let mut cells = Vec::new();
                    for (row, x) in self.values().into_iter().enumerate() {
                        let v = || Value::known(x);
                        cells.push(region.assign_advice(|| "v", cfg.src[0], row, v)?);
                        let w = || Value::known(x.square() + x);
                        region.assign_advice(|| "w", cfg.src[1], row, w)?;
                        cfg.q.enable(&mut region, row)?;
                    }
                    Ok(cells)
                },
            )?;
            layouter.constrain_instance(cells[0].cell(), cfg.inst, 0)?;
            let cells: Vec<AssignedNative<Fq>> =
                cells.into_iter().map(AssignedNative::from_cell).collect();
            let native = NativeChip::new_from_scratch(&cfg.native);
            let chip = RangeCheckChip::<Fq>::new(&cfg.range, &native);
            for x in &cells {
                chip.assert_lower_than_pow2(&mut layouter, x, BITS)?;
            }
            chip.load(&mut layouter)
        }
    }

    pub fn setup(seed: u64, k: u32) -> (ParamsKZG<Bls12>, ProvingKey<Fq, Scheme>, RangeCircuit) {
        let params = ParamsKZG::<Bls12>::unsafe_setup(k, ChaCha20Rng::seed_from_u64(seed));
        let rows = (1 << (k - 1)) - 40;
        let circuit = RangeCircuit { seed, rows };
        let vk = keygen_vk_with_k::<Fq, Scheme, _>(&params, &circuit, k).unwrap();
        let pk = keygen_pk(vk, &circuit).unwrap();
        (params, pk, circuit)
    }

    /// A proof with every random draw seeded, and whether it verifies.
    pub fn prove(
        params: &ParamsKZG<Bls12>,
        pk: &ProvingKey<Fq, Scheme>,
        circuit: &RangeCircuit,
    ) -> (Vec<u8>, bool) {
        set_quotient_blinding_seed(Some(circuit.seed ^ 0xb11d));
        let inst = [circuit.values()[0]];
        let mut transcript = CircuitTranscript::<Blake2b256>::init();
        let rng = ChaCha20Rng::seed_from_u64(circuit.seed ^ 0x9e37);
        create_proof::<Fq, Scheme, _, _>(params, pk, circuit, 0, &[&inst], &mut transcript, rng)
            .unwrap();
        set_quotient_blinding_seed(None);
        let proof = transcript.finalize();
        let mut transcript = CircuitTranscript::<Blake2b256>::init_from_bytes(&proof);
        let ok = prepare::<Fq, Scheme, _>(pk.get_vk(), &[], &[&inst], &mut transcript)
            .is_ok_and(|g| g.verify(&params.verifier_params()).is_ok());
        (proof, ok)
    }
}

/// Random circuits with two permutation sets and one, and the range circuit
/// with a lookup of several chunks at a two-pass transform size; the prover's
/// check mode compares the hook's quotient with the stock CPU quotient.
#[test]
fn numerator_and_quotient_match_references() {
    let _g = lock();
    QUOTIENT_CHECK.store(true, Relaxed);
    let (checks, diffs) = (hooks::quotient_checks(), hooks::quotient_check_diffs());
    let served = metal::stats().quotient.served;
    let (params, pk, c) = range::setup(1, 9);
    let jobs = capture(|| {
        RandomCircuit::new(0, false, 6).prove();
        RandomCircuit::new(3, false, 6).prove();
        assert!(
            range::prove(&params, &pk, &c).1,
            "the range circuit verifies"
        );
    });
    QUOTIENT_CHECK.store(false, Relaxed);
    assert_eq!(jobs.len(), 3);
    assert_eq!(hooks::quotient_checks() - checks, 3);
    assert_eq!(hooks::quotient_check_diffs(), diffs);
    for j in &jobs {
        check_reference(j);
    }
    assert_eq!(metal::stats().quotient.served - served, 6);
    let t: Vec<&QuotientJob<Fq>> = jobs.iter().map(|j| &j.template).collect();
    let sets = |j: &QuotientJob<Fq>| j.permutation.as_ref().map_or(0, |p| p.products.len());
    assert!(t.iter().any(|j| sets(j) >= 2));
    assert!(t.iter().any(|j| sets(j) == 1));
    assert!(t.iter().any(|j| j.lookups.iter().any(|l| l.helpers.len() >= 2)));
    assert!(t.iter().any(|j| !j.trash.is_empty()));
    assert!(t.iter().all(|j| !j.gates.ops.is_empty()));
    assert!(t.iter().any(|j| j.ext_k > 10));
}

/// Several rows per thread, and many command buffers.
#[test]
fn numerator_independent_of_threads() {
    let _g = lock();
    let j = job_of_circuit(10, 9);
    qt::set_threads(Some(256));
    check_reference(&j);
    qt::set_target_nanos(Some(1));
    check_reference(&j);
    let runs = qt::last_stages().unwrap().numerator_runs;
    qt::set_target_nanos(None);
    qt::set_threads(None);
    assert_eq!(
        runs,
        (1 << 11) / 256,
        "one command buffer per dispatch of rows"
    );
}

/// The proof with all four hooks is served, verifies and has the bytes of
/// the proof without hooks.
fn end_to_end(name: &str, prove: impl Fn() -> (Vec<u8>, bool)) {
    let served = metal::stats().quotient.served;
    let (with, ok) = prove();
    assert!(ok, "{name}: the device proof verifies");
    let served = metal::stats().quotient.served - served;
    assert_eq!(served, 1, "{name}: {:?}", metal::declines());
    let (without, ok) = test_switches::without_hooks(&prove);
    assert!(ok && with == without, "{name}: the stock proof");
    let (checks, diffs) = (hooks::quotient_checks(), hooks::quotient_check_diffs());
    QUOTIENT_CHECK.store(true, Relaxed);
    let (checked, _) = prove();
    QUOTIENT_CHECK.store(false, Relaxed);
    assert_eq!(hooks::quotient_checks() - checks, 1);
    assert_eq!(hooks::quotient_check_diffs(), diffs, "{name}");
    assert!(checked == with);
    assert!(metal::end_request());
}

#[test]
fn end_to_end_small() {
    let _g = lock();
    let rc = RandomCircuit::new(8, true, 8);
    end_to_end("random k=8", || rc.prove());
    let (params, pk, c) = range::setup(5, 10);
    end_to_end("range k=10", || range::prove(&params, &pk, &c));
}

/// `ext_k > 16` reads the low twiddle table past its first entry.
#[test]
#[cfg_attr(debug_assertions, ignore)]
fn end_to_end_k16() {
    let _g = lock();
    metal::set_min_k(14);
    let rc = RandomCircuit::new(10, true, 16);
    end_to_end("random k=16", || rc.prove());
}

/// `x + r`, unreduced and equal to `x` mod `r`, if it fits in four limbs.
fn plus_r(x: Scalar) -> Option<Scalar> {
    let mut r = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let s = x[i] as u128 + FR_MODULUS[i] as u128 + carry;
        r[i] = s as u64;
        carry = s >> 64;
    }
    (carry == 0).then_some(r)
}

/// A pattern for `out` that no quotient writes by chance.
fn pattern(len: usize) -> Vec<Scalar> {
    (0..len as u64)
        .map(|i| [0x5eed_0000 + i, !i, i.rotate_left(17) ^ 0xa5a5, 7])
        .collect()
}

/// `j` declines `reason`, counted once, and leaves `out` unchanged.
fn expect_decline(j: &pa::QuotientJobAbi, reason: &str) {
    let before = common::declines("quotient", reason);
    let declines = metal::quotient_counts().1;
    let mut out = pattern(j.len);
    // SAFETY: the job's pointers live for the call.
    let ok = unsafe { metal::quotient(j as *const _ as *const c_void, &mut out) };
    assert!(!ok, "{reason}: served");
    assert!(out == pattern(j.len), "{reason}: out changed");
    let counted = common::declines("quotient", reason) - before;
    assert_eq!(counted, 1, "{reason}: {:?}", metal::declines());
    assert_eq!(metal::quotient_counts().1 - declines, 1);
}

type Edit<'a, T> = &'a dyn Fn(&mut T);

#[test]
fn declines_leave_out_unchanged() {
    let _g = lock();
    let j = job_of_circuit(3, 7);
    let job = j.job();
    let packed = PackedJob::new(&job);
    let a = *abi(&packed);
    // SAFETY (every `unsafe` below): `a` points into `packed` and `j`.

    let mut bad = a;
    bad.abi = pa::QUOTIENT_ABI + 1;
    expect_decline(&bad, "shape");
    metal::set_min_k(a.ext_k + 1);
    expect_decline(&a, "below-min-k");
    metal::set_min_k(1);
    qt::set_memory_limit(Some(metal::need_bytes(a.ext_k, 1, 1, 0) as u64));
    expect_decline(&a, "memory");
    qt::set_memory_limit(None);
    let mut bad = a;
    bad.y = [u64::MAX; 4];
    expect_decline(&bad, "unreduced");
    // a wrong output length, and a null job
    for (ptr, len) in [(packed.as_ptr(), a.len + 1), (std::ptr::null(), a.len)] {
        let before = common::declines("quotient", "shape");
        let mut out = pattern(len);
        // SAFETY: the job lives for the call; a null job is declined before use.
        assert!(!unsafe { metal::quotient(ptr, &mut out) });
        assert!(out == pattern(len), "out unchanged");
        assert_eq!(common::declines("quotient", "shape") - before, 1);
    }

    // tables the program checks reject
    let gates = &job.gates;
    let (nreads, nunis, nslots) = (
        gates.reads.len() as u32,
        gates.uniforms.len() as u32,
        job.nslots(),
    );
    let fixed = gates.reads.iter().find(|r| r.kind == hooks::COLUMN_FIXED).unwrap().column;
    let edits: [Edit<QuotientJob<Fq>>; 7] = [
        &|j| j.gates.ops[0].a = (hooks::TAG_READ << 30) | nreads,
        &|j| j.gates.ops[0].b = (hooks::TAG_UNIFORM << 30) | nunis,
        &|j| j.gates.ops[0].a = (hooks::TAG_SLOT << 30) | nslots,
        &|j| j.gates.ops[0].dst = nslots,
        &|j| j.gates.ops[0].a = 3 << 30,
        &|j| j.gates.outputs[0] = (hooks::TAG_READ << 30) | nreads,
        &|j| j.fixed[fixed as usize] = None,
    ];
    for edit in edits {
        let mut bad = job.clone();
        edit(&mut bad);
        expect_decline(abi(&PackedJob::new(&bad)), "shape");
    }
    let mut lookups = unsafe { sl(a.lookups, a.nlookups) }.to_vec();
    let mut helpers = unsafe { sl(lookups[0].helpers, lookups[0].nchunks) }.to_vec();
    helpers[0] = std::ptr::null();
    lookups[0].helpers = helpers.as_ptr();
    let mut bad = a;
    bad.lookups = lookups.as_ptr();
    expect_decline(&bad, "shape");

    // unreduced scalars passed by value: the shift and its inverse decline
    // `shape`, the divisor and `t_inv` `unreduced`
    for v in [plus_r([0; 4]).unwrap(), [u64::MAX; 4]] {
        let edits: [(&str, Edit<pa::QuotientJobAbi>); 4] = [
            ("shape", &|b| b.zeta[0] = v),
            ("shape", &|b| b.zeta[1] = v),
            ("shape", &|b| b.zeta_out[1] = v),
            ("unreduced", &|b| b.divisor = v),
        ];
        for (reason, edit) in edits {
            let mut bad = a;
            edit(&mut bad);
            expect_decline(&bad, reason);
        }
        for at in [0, a.nt_inv - 1] {
            let mut t_inv = unsafe { sl(a.t_inv, a.nt_inv) }.to_vec();
            t_inv[at] = v;
            let mut bad = a;
            bad.t_inv = t_inv.as_ptr();
            expect_decline(&bad, "unreduced");
        }
    }
    if let Some(z) = plus_r(a.zeta[0]) {
        let mut bad = a;
        bad.zeta[0] = z;
        expect_decline(&bad, "shape");
    }

    // unreduced coefficients: a proof polynomial (found while copying, with
    // the device at work) and a key polynomial
    let advice = unsafe { sl(a.advice, a.nadvice) };
    let mut adv = unsafe { sl(advice[0], 1 << a.k) }.to_vec();
    adv[(1 << a.k) - 1] = plus_r([2, 0, 0, 0]).unwrap();
    let ptrs: Vec<_> =
        advice.iter().map(|p| if *p == advice[0] { adv.as_ptr() } else { *p }).collect();
    let mut bad = a;
    bad.advice = ptrs.as_ptr();
    expect_decline(&bad, "unreduced");
    let mut la = unsafe { sl(a.l_active, 1 << a.ext_k) }.to_vec();
    la[5] = plus_r([3, 0, 0, 0]).unwrap();
    let mut bad = a;
    bad.l_active = la.as_ptr();
    expect_decline(&bad, "unreduced");

    // a memory decline after a registered key was lent
    let handle = metal::register_key(&j.keys());
    let need = j.need_bytes();
    qt::set_memory_limit(Some(need - 1));
    expect_decline(&a, "memory");
    qt::set_memory_limit(Some(need));
    assert_eq!(j.serve().0, j.reference());
    qt::set_memory_limit(None);
    drop(handle);
    assert_eq!(j.serve().0, j.reference());
    assert!(metal::end_request());
}

#[test]
fn registered_key_is_resident() {
    let _g = lock();
    let mut j = job_of_circuit(8, 8);
    let en = 1usize << j.template.ext_k;
    let nkeys = j.keys().len() as u32;
    metal::set_keep_resident(false);
    let handle = metal::register_key(&j.keys());
    assert!(handle.verify(&j.keys()));
    assert_eq!(handle.resident_bytes(), 0);
    let serve = |j: &OwnedJob| {
        let (out, st) = j.serve();
        assert!(out == j.reference(), "quotient");
        (st.resident_polys, st.uploaded_polys, st.key_copies_made)
    };
    assert_eq!(serve(&j), (nkeys, 0, nkeys));
    assert_eq!(handle.resident_bytes(), (nkeys as usize * en * 32) as u64);
    metal::begin_request();
    assert_eq!(serve(&j), (nkeys, 0, 0));
    let stale = metal::key_stale();
    j.bump_key(nkeys as usize - 1, 3, Fq::ONE);
    metal::begin_request();
    let (resident, uploaded, _) = serve(&j);
    assert_eq!(metal::key_stale() - stale, 1);
    assert_eq!((resident, uploaded), (nkeys - 1, 1));
    assert_eq!(metal::keys_registered(), nkeys as usize - 1);
    assert!(metal::end_request());
    assert_eq!(handle.resident_bytes(), 0);
    metal::set_keep_resident(true);
    assert_eq!(serve(&j).2, nkeys - 1);
    assert!(metal::end_request());
    assert!(handle.resident_bytes() > 0);
    assert!(metal::evict_key_copies() > 0);
    assert_eq!(handle.resident_bytes(), 0);
    metal::set_keep_resident(false);
    drop(handle);
    assert_eq!(metal::keys_registered(), 0);
}

/// One handle holding keys of two extended lengths, in both registration
/// orders (which number the slots of a length differently).
#[test]
fn mixed_length_registration_serves_each_length() {
    let _g = lock();
    let a = job_of_circuit(3, 6);
    let b = job_of_circuit(4, 8);
    assert_ne!(a.template.ext_k, b.template.ext_k);
    let (ra, rb) = (a.reference(), b.reference());
    let (na, nb) = (a.keys().len() as u32, b.keys().len() as u32);
    metal::set_keep_resident(true);
    for (a_first, one_request) in [(true, false), (false, true)] {
        let (first, second) = if a_first { (&a, &b) } else { (&b, &a) };
        let handle = metal::register_key(&[first.keys(), second.keys()].concat());
        let what = format!("A first {a_first}, one request {one_request}");
        if one_request {
            metal::begin_request();
        }
        for (i, (j, want, nkeys, copies)) in [
            (&a, &ra, na, na),
            (&b, &rb, nb, nb),
            (&a, &ra, na, 0),
            (&b, &rb, nb, 0),
        ]
        .into_iter()
        .enumerate()
        {
            if !one_request {
                metal::begin_request();
            }
            let (out, st) = j.serve();
            assert!(out == *want, "{what}: quotient {i}");
            let placement = (st.resident_polys, st.uploaded_polys, st.key_copies_made);
            assert_eq!(placement, (nkeys, 0, copies), "{what}: placement {i}");
            if !one_request {
                assert!(metal::end_request());
            }
        }
        if one_request {
            assert!(metal::end_request());
        }
        let (out, st) = a.serve();
        assert!(out == ra, "{what}: outside a request");
        assert_eq!((st.resident_polys, st.key_copies_made), (na, 0));
        let bytes = ((na as u64) << a.template.ext_k) * 32 + ((nb as u64) << b.template.ext_k) * 32;
        assert_eq!(
            handle.resident_bytes(),
            bytes,
            "{what}: one copy per length"
        );
        drop(handle);
        assert_eq!(metal::keys_registered(), 0);
    }
    metal::set_keep_resident(false);
    assert!(metal::end_request());
}

#[test]
fn outside_a_request_every_serve_checks() {
    let _g = lock();
    assert!(metal::end_request());
    let mut j = job_of_circuit(8, 7);
    let nkeys = j.keys().len() as u32;
    let handle = metal::register_key(&j.keys());
    for copies in [nkeys, 0] {
        let (out, st) = j.serve();
        assert!(out == j.reference());
        assert_eq!((st.resident_polys, st.key_copies_made), (nkeys, copies));
    }
    let stale = metal::key_stale();
    let old = j.reference();
    j.bump_key(nkeys as usize - 1, 3, Fq::ONE);
    let new = j.reference();
    assert!(old != new, "the change moves the quotient");
    let (out, st) = j.serve();
    assert!(out == new, "the new contents");
    assert_eq!(metal::key_stale() - stale, 1);
    assert_eq!((st.resident_polys, st.uploaded_polys), (nkeys - 1, 1));
    drop(handle);
    assert!(metal::end_request());
}

/// A change after the first serve of a request is seen at the next request.
#[test]
fn inside_a_request_checks_once() {
    let _g = lock();
    let mut j = job_of_circuit(8, 7);
    metal::set_keep_resident(true);
    metal::begin_request();
    let nkeys = j.keys().len() as u32;
    let handle = metal::register_key(&j.keys());
    let old = j.reference();
    let (out, st) = j.serve();
    assert!(out == old);
    assert_eq!(st.key_copies_made, nkeys);
    let stale = metal::key_stale();
    j.bump_key(0, 9, Fq::from(5));
    let new = j.reference();
    assert!(old != new);
    let (out, st) = j.serve();
    assert!(out == old, "once per request: the copy");
    assert_eq!((st.resident_polys, st.key_copies_made), (nkeys, 0));
    assert_eq!(metal::key_stale(), stale);
    assert!(metal::end_request());
    metal::begin_request();
    let (out, st) = j.serve();
    assert!(out == new, "the next request: the new contents");
    assert_eq!(metal::key_stale() - stale, 1);
    assert_eq!((st.resident_polys, st.uploaded_polys), (nkeys - 1, 1));
    assert!(metal::end_request());
    drop(handle);
    metal::set_keep_resident(false);
}

/// A key changed from C1 to C2 before its slot is filled is not marked
/// present; changed back to C1 later, C1 is served.
#[test]
fn slot_filled_with_changed_contents_is_not_present() {
    let _g = lock();
    let mut j = job_of_circuit(8, 7);
    metal::set_keep_resident(true);
    metal::begin_request();
    let nkeys = j.keys().len() as u32;
    let handle = metal::register_key(&j.keys());
    let c1 = j.reference();
    let stale = metal::key_stale();
    let victim = nkeys as usize / 2;
    j.bump_key(victim, 11, Fq::ONE);
    let c2 = j.reference();
    assert!(c1 != c2);
    let (out, st) = j.serve();
    assert!(out == c2);
    assert_eq!(metal::key_stale() - stale, 1);
    let placement = (st.resident_polys, st.uploaded_polys, st.key_copies_made);
    assert_eq!(
        placement,
        (nkeys - 1, 1, nkeys - 1),
        "the C2 slot is not present"
    );
    assert_eq!(metal::keys_registered(), nkeys as usize - 1);
    assert!(metal::end_request());
    j.bump_key(victim, 11, -Fq::ONE);
    assert!(j.reference() == c1);
    metal::begin_request();
    let (out, st) = j.serve();
    assert!(out == c1);
    assert_eq!(metal::key_stale() - stale, 1);
    let placement = (st.resident_polys, st.uploaded_polys, st.key_copies_made);
    assert_eq!(placement, (nkeys - 1, 1, 0));
    assert!(metal::end_request());
    drop(handle);
    metal::set_keep_resident(false);
}

/// `need_bytes_job` and `need_bytes` bound the device bytes a call adds, for
/// a one-pass and a two-pass transform size.
#[test]
fn need_bytes_bounds_the_measured_peak() {
    let _g = lock();
    let (params, pk, c) = range::setup(1, 9);
    let mut jobs = capture(|| drop(range::prove(&params, &pk, &c)));
    jobs.push(job_of_circuit(3, 6));
    metal::set_keep_resident(true);
    let measure = |j: &OwnedJob, what: &str| {
        assert!(metal::end_request());
        metal::release_pool();
        metal::begin_request();
        let need = j.need_bytes();
        let (now0, _) = metal::device_bytes();
        let want = j.reference();
        assert!(j.serve().0 == want, "{what}: quotient");
        let used = metal::device_bytes().1.saturating_sub(now0);
        let nkeys = j.keys().len();
        let t = &j.template;
        let shape = metal::need_bytes(t.ext_k, j.polys.len() - nkeys, nkeys, t.nslots()) as u64;
        assert!(used > 0, "{what}: measured");
        assert!(
            need >= used,
            "{what}: need_bytes_job {need} < measured {used}"
        );
        assert!(
            shape >= used,
            "{what}: need_bytes {shape} < measured {used}"
        );
    };
    for (i, j) in jobs.iter_mut().enumerate() {
        measure(j, &format!("job {i} unregistered"));
        let handle = metal::register_key(&j.keys());
        measure(j, &format!("job {i} copy made"));
        measure(j, &format!("job {i} resident"));
        drop(handle);
        let handle = metal::register_key(&j.keys());
        j.bump_key(0, 1, Fq::ONE);
        measure(j, &format!("job {i} stale"));
        drop(handle);
    }
    metal::set_keep_resident(false);
    assert!(metal::end_request());
}
