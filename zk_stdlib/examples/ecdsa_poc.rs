//! Proof of possession for a secp256r1 (NIST P-256) key pair.
//!
//! Proves knowledge of points Q, R on P-256 such that
//!
//!   T = R + c·Q
//!
//! where T is the only public input.  The challenge scalar c is embedded in
//! the relation struct, so the circuit structure — and the verifying key —
//! is specific to this value of c.
//!
//! Two scalar-multiplication strategies are compiled and compared:
//!
//! * **Windowed (WS=4)** — `msm_by_fixed_le_bits`: packs bits into 4-bit
//!   windows, always processes all windows.  Cost: n doublings + ~40 adds
//!   for n = 100 bits.
//!
//! * **Double-and-add** — `mul_by_u128`: processes one bit at a time,
//!   adding `base` only for set bits.  Cost: n doublings + popcount(c) adds.
//!   Competitive when popcount(c) < ~40.
//!
//! Instance:  T: P256
//! Witness:   (Q: P256,  R: P256)

use std::time::Instant;

use group::Group;
use midnight_circuits::{
    field::foreign::params::MultiEmulationParams,
    instructions::{
        AssertionInstructions, AssignmentInstructions, DecompositionInstructions,
        EccInstructions, PublicInputInstructions,
    },
    types::{AssignedForeignPoint, Instantiable},
    CircuitField,
};
use ff::PrimeField;
use midnight_curves::p256::{Fq as P256Scalar, P256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{cost_model, utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::{rngs::OsRng, Rng};

type F = midnight_curves::Fq;

/// Number of bits in the challenge scalar c.
const NB_BITS_C: usize = 100;

// ── Windowed relation (WS=4, c as public input) ───────────────────────────────

/// Parameterless relation: c is a public input, so a single VK covers all
/// challenge values.  Instance = (T, c) where c is a bounded u128 scalar.
#[derive(Clone)]
pub struct EcdsaPoPP256;

impl Relation for EcdsaPoPP256 {
    type Error = Error;
    /// Public inputs: the target point T and the challenge scalar c.
    type Instance = (P256, u128);
    type Witness = (P256, P256);

    fn format_instance((t, c): &Self::Instance) -> Result<Vec<F>, Error> {
        let mut pi = AssignedForeignPoint::<F, P256, MultiEmulationParams>::as_public_input(t);
        pi.push(F::from_u128(*c));
        Ok(pi)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let curve = std_lib.p256();

        // ── Public inputs ─────────────────────────────────────────────────────
        let t = curve.assign_as_public_input(layouter, instance.map(|(t, _)| t))?;
        let c_native =
            std_lib.assign_as_public_input(layouter, instance.map(|(_, c)| F::from_u128(c)))?;

        // ── Witnesses ─────────────────────────────────────────────────────────
        let (q_val, r_val) = witness.map(|(q, r)| (q, r)).unzip();
        let q = curve.assign(layouter, q_val)?;
        let r = curve.assign(layouter, r_val)?;

        // ── Relation: T = R + c·Q ─────────────────────────────────────────────
        // Decompose c into NB_BITS_C little-endian bits (range-checked).
        let c_bits = std_lib.assigned_to_le_bits(layouter, &c_native, Some(NB_BITS_C), false)?;
        let cq = curve.msm_by_le_bits(layouter, &[c_bits], &[q])?;
        let result = curve.add(layouter, &cq, &r)?;
        curve.assert_equal(layouter, &result, &t)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch { p256: true, nb_arith_cols: 5, nr_pow2range_cols: 4, ..ZkStdLibArch::default() }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(()) // no fixed parameters
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(EcdsaPoPP256)
    }
}

// ── Double-and-add relation ───────────────────────────────────────────────────

#[derive(Clone)]
pub struct EcdsaPoPP256Daa {
    c_bits: u128,
}

impl EcdsaPoPP256Daa {
    pub fn new(c_bits: u128) -> Self {
        Self { c_bits }
    }
}

impl Relation for EcdsaPoPP256Daa {
    type Error = Error;
    type Instance = P256;
    type Witness = (P256, P256);

    fn format_instance(t: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(AssignedForeignPoint::<F, P256, MultiEmulationParams>::as_public_input(t))
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let curve = std_lib.p256();
        let t = curve.assign_as_public_input(layouter, instance)?;
        let (q_val, r_val) = witness.map(|(q, r)| (q, r)).unzip();
        let q = curve.assign(layouter, q_val)?;
        let r = curve.assign(layouter, r_val)?;
        let cq = curve.mul_by_u128(layouter, self.c_bits, &q)?;
        let result = curve.add(layouter, &cq, &r)?;
        curve.assert_equal(layouter, &result, &t)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch { p256: true, nb_arith_cols: 7, nr_pow2range_cols: 6, ..ZkStdLibArch::default() }
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.c_bits.to_le_bytes())
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut buf = [0u8; 16];
        reader.read_exact(&mut buf)?;
        Ok(EcdsaPoPP256Daa { c_bits: u128::from_le_bytes(buf) })
    }
}

// ── main ─────────────────────────────────────────────────────────────────────

fn main() {
    let mut rng = OsRng;

    // ── Generate a valid witness ─────────────────────────────────────────────
    let q = P256::random(&mut rng);
    let r = P256::random(&mut rng);

    let c_u128: u128 = rng.gen::<u128>() & ((1u128 << NB_BITS_C) - 1);
    let c_bits: Vec<bool> = (0..NB_BITS_C).map(|i| (c_u128 >> i) & 1 == 1).collect();
    let popcount = c_bits.iter().filter(|&&b| b).count();

    let mut c_be = [0u8; 32];
    c_be[16..].copy_from_slice(&c_u128.to_be_bytes());
    let c_scalar = P256Scalar::from_bytes_be(&c_be).expect("valid bounded scalar");
    let t = r + q * c_scalar;

    println!("c: {NB_BITS_C}-bit scalar, popcount = {popcount}");

    // ── Compare circuit sizes ─────────────────────────────────────────────────
    let rel_windowed = EcdsaPoPP256;
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);

    let m_w = cost_model(&rel_windowed, None);
    let m_d = cost_model(&rel_daa, None);

    println!(
        "Windowed WS=4:  k={}, {} / {} rows  ({} advice, {} fixed, {} lookups)",
        m_w.k, m_w.rows, 1u64 << m_w.k,
        m_w.advice_columns, m_w.fixed_columns, m_w.lookups,
    );
    println!(
        "Double-and-add: k={}, {} / {} rows  ({} advice, {} fixed, {} lookups)",
        m_d.k, m_d.rows, 1u64 << m_d.k,
        m_d.advice_columns, m_d.fixed_columns, m_d.lookups,
    );

    // ── Full proof flow for the smaller circuit ───────────────────────────────
    let instance_windowed = (t.clone(), c_u128);
    if m_w.rows <= m_d.rows {
        println!("\nRunning full proof with windowed WS=4 (fewer rows).");
        run_proof(rel_windowed, m_w.k, &instance_windowed, (q, r), rng);
    } else {
        println!("\nRunning full proof with double-and-add (fewer rows).");
        run_proof(rel_daa, m_d.k, &t, (q, r), rng);
    }
}

fn run_proof<Rel>(relation: Rel, k: u32, instance: &Rel::Instance, witness: Rel::Witness, rng: OsRng)
where
    Rel: Relation,
    Rel::Error: std::fmt::Debug,
{
    let srs = srs_for_test(&relation, Some(k));

    let t_vk = Instant::now();
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    println!("VK generation:      {:?}", t_vk.elapsed());

    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let t_prove = Instant::now();
    let proof = midnight_zk_stdlib::prove::<Rel, blake2b_simd::State>(
        &srs, &pk, &relation, instance, witness, rng,
    )
    .expect("proof generation should not fail");
    println!("Proof generation:   {:?}  ({} bytes)", t_prove.elapsed(), proof.len());

    let t_verify = Instant::now();
    assert!(
        midnight_zk_stdlib::verify::<Rel, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            instance,
            None,
            &proof,
        )
        .is_ok(),
        "proof verification failed"
    );
    println!("Proof verification: {:?}", t_verify.elapsed());
}
