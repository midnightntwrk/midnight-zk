//! Building an `EvaluationDomain`, or reading a verifying key, allocates
//! memory independent of the domain size: the FFT twiddle factors are only
//! computed on the prover side.
//!
//! This file holds a single test, as the allocation counter is global.

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
};

use ff::PrimeField;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, VerifyingKey,
        keygen_vk_with_k,
    },
    poly::{
        EvaluationDomain, Rotation,
        kzg::{KZGCommitmentScheme, params::ParamsKZG},
    },
    utils::SerdeFormat,
};
use rand::{SeedableRng, rngs::StdRng};

/// Counts the bytes allocated by the whole process.
struct CountingAlloc;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

/// Larger requests fail, so that a regression aborts instead of exhausting
/// the machine's memory.
const MAX_ALLOC: usize = 1 << 30;

unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() > MAX_ALLOC {
            return std::ptr::null_mut();
        }
        ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: CountingAlloc = CountingAlloc;

/// Bytes allocated while running `f`.
fn allocated_by<T>(f: impl FnOnce() -> T) -> usize {
    let before = ALLOCATED.load(Ordering::SeqCst);
    std::hint::black_box(f());
    ALLOCATED.load(Ordering::SeqCst) - before
}

/// Bound on the bytes allocated by the operations below. A single table of
/// twiddle factors at these sizes would take several GiB.
const BOUND: usize = 1 << 20;

#[derive(Default)]
struct TestCircuit;

impl Circuit<Fq> for TestCircuit {
    type Config = Column<Advice>;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        TestCircuit
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Column<Advice> {
        let a = meta.advice_column();
        let s = meta.selector();
        meta.create_gate("a^2 = a", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            Constraints::with_selector(s, vec![a.clone() * a.clone() - a])
        });
        a
    }

    fn synthesize(&self, _: Column<Advice>, _: impl Layouter<Fq>) -> Result<(), Error> {
        Ok(())
    }
}

#[test]
fn large_domains_allocate_little() {
    // A domain of size 2^(S - 1), extended to 2^S.
    let bytes = allocated_by(|| EvaluationDomain::<Fq>::new(3, Fq::S - 1));
    assert!(
        bytes < BOUND,
        "EvaluationDomain::new allocated {bytes} bytes"
    );

    // A verifying key of a small circuit, with its `k` (the byte after the
    // version byte) replaced by the largest one the reader accepts.
    const K: u32 = 4;
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, StdRng::seed_from_u64(0));
    let vk = keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &TestCircuit, K)
        .expect("vk should not fail");
    let max_k = Fq::S - (vk.cs().degree() as u32 - 1).next_power_of_two().ilog2();
    let mut bytes = vk.to_bytes(SerdeFormat::RawBytes);
    assert_eq!(bytes[1], K as u8);
    bytes[1] = max_k as u8;

    let read = |bytes: &[u8]| {
        VerifyingKey::<Fq, KZGCommitmentScheme<Bls12>>::from_bytes::<TestCircuit>(
            bytes,
            SerdeFormat::RawBytes,
            #[cfg(feature = "circuit-params")]
            (),
        )
        .expect("vk should deserialize")
    };
    let read_bytes = allocated_by(|| read(&bytes));
    assert!(
        read_bytes < BOUND,
        "VerifyingKey::read allocated {read_bytes} bytes"
    );
    assert_eq!(read(&bytes).get_domain().k(), max_k);
}
