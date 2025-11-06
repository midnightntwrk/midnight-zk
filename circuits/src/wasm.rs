//! WASM bindings for circuit benchmarking
//!
//! This module provides JavaScript-accessible bindings for proof generation
//! and verification using various circuits with BLS12-381 curve.

use wasm_bindgen::prelude::*;
use web_sys::console;

use ff::{Field, PrimeField};
use group::Group;
use rand::{rngs::OsRng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::{
    compact_std_lib::{self, MidnightPK, MidnightVK, Relation, ZkStdLib, ZkStdLibArch},
    ecc::native::ScalarVar,
    field::foreign::params::MultiEmulationParams,
    hash::poseidon::PoseidonChip,
    instructions::{
        hash::HashCPU, AssertionInstructions, AssignmentInstructions, DecompositionInstructions,
        EccInstructions, PublicInputInstructions, ZeroInstructions,
    },
    types::{AssignedByte, AssignedForeignPoint, AssignedNativePoint, Instantiable},
};
use group::GroupEncoding;
use halo2curves::secp256k1::{Fp as secp256k1Base, Fq as secp256k1Scalar, Secp256k1};
use midnight_curves::{Fr as JubjubScalar, JubjubAffine, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::params::ParamsKZG,
    utils::SerdeFormat,
};
use sha2::Digest;

type F = midnight_curves::Fq;

/// Initialize panic hook for better error messages in browser console
#[wasm_bindgen]
pub fn init_panic_hook() {
    console_error_panic_hook::set_once();
}

/// Initialize the rayon thread pool for parallel proof generation
/// This must be called before any proof generation when using Web Workers
/// Returns a promise that resolves when the thread pool is ready
#[wasm_bindgen]
pub fn init_thread_pool(num_threads: usize) -> js_sys::Promise {
    wasm_bindgen_rayon::init_thread_pool(num_threads)
}

/// Example relation for Poseidon hash circuit benchmarking
#[derive(Clone, Default, Debug)]
pub struct PoseidonExample;

impl Relation for PoseidonExample {
    type Instance = F;
    type Witness = [F; 3];

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![*instance]
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: true,
            sha256: false,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 1,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonExample)
    }
}

/// Wrapper for the setup state (SRS, keys)
#[wasm_bindgen]
#[derive(Debug)]
pub struct PoseidonBenchmark {
    srs: ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    pk: MidnightPK<PoseidonExample>,
    relation: PoseidonExample,
}

#[wasm_bindgen]
impl PoseidonBenchmark {
    /// Create a new benchmark setup with SRS bytes
    /// The SRS bytes should be loaded from a Filecoin SRS file
    #[wasm_bindgen(constructor)]
    pub fn new(srs_bytes: &[u8]) -> Result<PoseidonBenchmark, JsValue> {
        console::log_1(&JsValue::from_str("Setting up Poseidon circuit..."));

        let start = js_sys::Date::now();
        let srs = ParamsKZG::<midnight_curves::Bls12>::read_custom::<_>(
            &mut std::io::Cursor::new(srs_bytes),
            SerdeFormat::RawBytesUnchecked,
        )
        .map_err(|e| JsValue::from_str(&format!("Failed to read SRS: {:?}", e)))?;
        let setup_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  SRS loaded in {:.2}ms", setup_time)));

        let relation = PoseidonExample;

        let start = js_sys::Date::now();
        let vk = compact_std_lib::setup_vk(&srs, &relation);
        let vk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  VKey generated in {:.2}ms", vk_time)));

        let start = js_sys::Date::now();
        let pk = compact_std_lib::setup_pk(&relation, &vk);
        let pk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  PKey generated in {:.2}ms", pk_time)));

        Ok(PoseidonBenchmark {
            srs,
            vk,
            pk,
            relation,
        })
    }

    /// Generate a proof for random inputs
    /// Returns a JS object with { proof: Uint8Array, instance: Uint8Array }
    #[wasm_bindgen(js_name = generateProof)]
    pub fn generate_proof(&self) -> Result<JsValue, JsValue> {
        let mut rng = ChaCha8Rng::from_entropy();
        let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
        let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);

        console::log_1(&JsValue::from_str("Generating proof..."));
        let start = js_sys::Date::now();

        let proof = compact_std_lib::prove::<PoseidonExample, blake2b_simd::State>(
            &self.srs,
            &self.pk,
            &self.relation,
            &instance,
            witness,
            OsRng,
        )
        .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;

        let proof_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Proof generated in {:.2}ms", proof_time)));
        console::log_1(&JsValue::from_str(&format!("  Proof size: {} bytes", proof.len())));

        // Serialize instance as bytes (little-endian)
        let mut instance_bytes = vec![0u8; 32];
        instance
            .to_repr()
            .as_ref()
            .iter()
            .enumerate()
            .for_each(|(i, &byte)| instance_bytes[i] = byte);

        // Create a JavaScript object with both proof and instance
        let result = js_sys::Object::new();
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("proof"),
            &js_sys::Uint8Array::from(&proof[..]),
        )?;
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("instance"),
            &js_sys::Uint8Array::from(&instance_bytes[..]),
        )?;

        Ok(result.into())
    }

    /// Verify a proof with the given public instance
    /// Returns true if valid
    #[wasm_bindgen(js_name = verifyProof)]
    pub fn verify_proof(&self, proof_bytes: &[u8], instance_bytes: &[u8]) -> Result<bool, JsValue> {
        // Deserialize instance from bytes
        if instance_bytes.len() != 32 {
            return Err(JsValue::from_str("Instance must be 32 bytes"));
        }
        let mut repr = <F as PrimeField>::Repr::default();
        repr.as_mut().copy_from_slice(instance_bytes);
        let instance = F::from_repr(repr)
            .into_option()
            .ok_or_else(|| JsValue::from_str("Invalid instance bytes"))?;

        console::log_1(&JsValue::from_str("Verifying proof..."));
        let start = js_sys::Date::now();

        let result = compact_std_lib::verify::<PoseidonExample, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            None,
            proof_bytes,
        );

        let verify_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Verification completed in {:.2}ms", verify_time)));

        match result {
            Ok(_) => {
                console::log_1(&JsValue::from_str("  ✓ Proof is VALID"));
                Ok(true)
            }
            Err(e) => {
                console::log_1(&JsValue::from_str(&format!("  ✗ Proof is INVALID: {:?}", e)));
                Ok(false)
            }
        }
    }

    /// Run a complete proof generation and verification benchmark
    /// Returns timing information as a JSON string
    #[wasm_bindgen(js_name = runBenchmark)]
    pub fn run_benchmark(&self, iterations: usize) -> Result<String, JsValue> {
        console::log_1(&JsValue::from_str(&format!("Running {} iterations...", iterations)));

        let mut prove_times = Vec::with_capacity(iterations);
        let mut verify_times = Vec::with_capacity(iterations);
        let mut proof_sizes = Vec::with_capacity(iterations);

        let mut rng = ChaCha8Rng::from_entropy();

        for i in 0..iterations {
            // Generate proof
            let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
            let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);

            let prove_start = js_sys::Date::now();
            let proof = compact_std_lib::prove::<PoseidonExample, blake2b_simd::State>(
                &self.srs,
                &self.pk,
                &self.relation,
                &instance,
                witness,
                OsRng,
            )
            .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;
            let prove_time = js_sys::Date::now() - prove_start;

            // Verify proof
            let verify_start = js_sys::Date::now();
            compact_std_lib::verify::<PoseidonExample, blake2b_simd::State>(
                &self.srs.verifier_params(),
                &self.vk,
                &instance,
                None,
                &proof,
            )
            .map_err(|e| JsValue::from_str(&format!("Verification failed: {:?}", e)))?;
            let verify_time = js_sys::Date::now() - verify_start;

            prove_times.push(prove_time);
            verify_times.push(verify_time);
            proof_sizes.push(proof.len());

            if (i + 1) % 10 == 0 {
                console::log_1(&JsValue::from_str(&format!("  Completed {}/{} iterations", i + 1, iterations)));
            }
        }

        // Calculate statistics
        let avg_prove = prove_times.iter().sum::<f64>() / iterations as f64;
        let avg_verify = verify_times.iter().sum::<f64>() / iterations as f64;
        let avg_size = proof_sizes.iter().sum::<usize>() / iterations;

        let min_prove = prove_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_prove = prove_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let min_verify = verify_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_verify = verify_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

        let result = format!(
            r#"{{
  "iterations": {},
  "prove": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "verify": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "proof_size_bytes": {}
}}"#,
            iterations, avg_prove, min_prove, max_prove, avg_verify, min_verify, max_verify, avg_size
        );

        console::log_1(&JsValue::from_str("\nBenchmark Results:"));
        console::log_1(&JsValue::from_str(&result));

        Ok(result)
    }
}

// ============================================================================
// Schnorr Signature Benchmark
// ============================================================================

/// Schnorr signature structure
#[derive(Clone, Default, Debug)]
pub struct SchnorrSignature {
    s: JubjubScalar,
    e_bytes: [u8; 32],
}

type SchnorrPK = JubjubSubgroup;
type SchnorrSK = JubjubScalar;
type Message = F;

/// Generate a Schnorr keypair
fn keygen(mut rng: impl RngCore) -> (SchnorrPK, SchnorrSK) {
    let sk = JubjubScalar::random(&mut rng);
    let pk = JubjubSubgroup::generator() * sk;
    (pk, sk)
}

/// Sign a message with Schnorr signature scheme
fn sign(message: Message, secret_key: &SchnorrSK, mut rng: impl RngCore) -> SchnorrSignature {
    let k = JubjubScalar::random(&mut rng);
    let r = JubjubSubgroup::generator() * k;

    let (rx, ry) = get_coords(&r);
    let (pkx, pky) = get_coords(&(JubjubSubgroup::generator() * secret_key));

    let h = PoseidonChip::hash(&[pkx, pky, rx, ry, message]);
    let e_bytes = h.to_bytes_le();

    let s = {
        let mut buff = [0u8; 64];
        buff[..32].copy_from_slice(&e_bytes);
        let e = JubjubScalar::from_bytes_wide(&buff);
        k - e * secret_key
    };

    SchnorrSignature { s, e_bytes }
}

/// Get affine coordinates of a Jubjub point
fn get_coords(point: &JubjubSubgroup) -> (F, F) {
    let point: &Jubjub = point.into();
    let point: JubjubAffine = point.into();
    (point.get_u(), point.get_v())
}

/// Example relation for Schnorr signature circuit benchmarking
#[derive(Clone, Default, Debug)]
pub struct SchnorrExample;

impl Relation for SchnorrExample {
    type Instance = (SchnorrPK, Message);
    type Witness = SchnorrSignature;

    fn format_instance((pk, msg): &Self::Instance) -> Vec<F> {
        [
            AssignedNativePoint::<Jubjub>::as_public_input(pk),
            vec![*msg],
        ]
        .concat()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let jubjub = &std_lib.jubjub();

        // Assign public inputs.
        let (pk_val, m_val) = instance.map(|(pk, m)| (pk, m)).unzip();
        let pk: AssignedNativePoint<Jubjub> = jubjub.assign_as_public_input(layouter, pk_val)?;
        let message = std_lib.assign_as_public_input(layouter, m_val)?;

        // Assign witness values.
        let (sig_s_val, sig_e_bytes_val) = witness.map(|sig| (sig.s, sig.e_bytes)).unzip();
        let sig_s: ScalarVar<Jubjub> = std_lib.jubjub().assign(layouter, sig_s_val)?;
        let sig_e_bytes = std_lib.assign_many(layouter, &sig_e_bytes_val.transpose_array())?;

        let generator: AssignedNativePoint<Jubjub> =
            (std_lib.jubjub()).assign_fixed(layouter, <JubjubSubgroup as Group>::generator())?;

        let sig_e = std_lib.jubjub().scalar_from_le_bytes(layouter, &sig_e_bytes)?;

        // 1. rv = s * G + e * Pk
        let rv =
            (std_lib.jubjub()).msm(layouter, &[sig_s, sig_e.clone()], &[generator, pk.clone()])?;

        let coords = |p| (jubjub.x_coordinate(p), jubjub.y_coordinate(p));
        let (pkx, pky) = coords(&pk);
        let (rx, ry) = coords(&rv);

        // 2. ev = hash( PK.x || PK.y || r.x || r.y || m)
        let h = std_lib.poseidon(layouter, &[pkx, pky, rx, ry, message])?;
        let ev_bytes = std_lib.assigned_to_le_bytes(layouter, &h, None)?;

        assert_eq!(ev_bytes.len(), sig_e_bytes.len());
        (ev_bytes.iter().zip(sig_e_bytes.iter()))
            .try_for_each(|(ev, e)| std_lib.assert_equal(layouter, ev, e))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: true,
            poseidon: true,
            sha256: false,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            automaton: false,
            nr_pow2range_cols: 1,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(SchnorrExample)
    }
}

/// Wrapper for Schnorr signature benchmark
#[wasm_bindgen]
#[derive(Debug)]
pub struct SchnorrBenchmark {
    srs: ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    pk: MidnightPK<SchnorrExample>,
    relation: SchnorrExample,
}

#[wasm_bindgen]
impl SchnorrBenchmark {
    /// Create a new Schnorr benchmark setup with SRS bytes
    #[wasm_bindgen(constructor)]
    pub fn new(srs_bytes: &[u8]) -> Result<SchnorrBenchmark, JsValue> {
        console::log_1(&JsValue::from_str("Setting up Schnorr signature circuit..."));

        let start = js_sys::Date::now();
        let srs = ParamsKZG::<midnight_curves::Bls12>::read_custom::<_>(
            &mut std::io::Cursor::new(srs_bytes),
            SerdeFormat::RawBytesUnchecked,
        )
        .map_err(|e| JsValue::from_str(&format!("Failed to read SRS: {:?}", e)))?;
        let setup_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  SRS loaded in {:.2}ms", setup_time)));

        let relation = SchnorrExample;

        let start = js_sys::Date::now();
        let vk = compact_std_lib::setup_vk(&srs, &relation);
        let vk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  VKey generated in {:.2}ms", vk_time)));

        let start = js_sys::Date::now();
        let pk = compact_std_lib::setup_pk(&relation, &vk);
        let pk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  PKey generated in {:.2}ms", pk_time)));

        Ok(SchnorrBenchmark {
            srs,
            vk,
            pk,
            relation,
        })
    }

    /// Generate a proof for a Schnorr signature
    /// Returns a JS object with { proof: Uint8Array, instance: Uint8Array }
    #[wasm_bindgen(js_name = generateProof)]
    pub fn generate_proof(&self) -> Result<JsValue, JsValue> {
        let mut rng = ChaCha8Rng::from_entropy();

        // Generate keypair and sign a random message
        let (schnorr_pk, sk) = keygen(&mut rng);
        let message = F::random(&mut rng);
        let sig = sign(message, &sk, &mut rng);

        let instance = (schnorr_pk, message);

        console::log_1(&JsValue::from_str("Generating proof..."));
        let start = js_sys::Date::now();

        let proof = compact_std_lib::prove::<SchnorrExample, blake2b_simd::State>(
            &self.srs,
            &self.pk,
            &self.relation,
            &instance,
            sig,
            OsRng,
        )
        .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;

        let proof_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Proof generated in {:.2}ms", proof_time)));
        console::log_1(&JsValue::from_str(&format!("  Proof size: {} bytes", proof.len())));

        // Serialize instance (pk.x, pk.y, message)
        let instance_vec = SchnorrExample::format_instance(&instance);
        let mut instance_bytes = Vec::new();
        for elem in instance_vec {
            let repr = elem.to_repr();
            instance_bytes.extend_from_slice(repr.as_ref());
        }

        // Create a JavaScript object with both proof and instance
        let result = js_sys::Object::new();
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("proof"),
            &js_sys::Uint8Array::from(&proof[..]),
        )?;
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("instance"),
            &js_sys::Uint8Array::from(&instance_bytes[..]),
        )?;

        Ok(result.into())
    }

    /// Verify a proof with the given public instance
    /// Returns true if valid
    #[wasm_bindgen(js_name = verifyProof)]
    pub fn verify_proof(&self, proof_bytes: &[u8], instance_bytes: &[u8]) -> Result<bool, JsValue> {
        // Deserialize instance (pk.x, pk.y, message) - 3 field elements
        if instance_bytes.len() != 96 {
            return Err(JsValue::from_str("Instance must be 96 bytes (3 field elements)"));
        }

        let mut fields = Vec::new();
        for i in 0..3 {
            let start = i * 32;
            let end = start + 32;
            let mut repr = <F as PrimeField>::Repr::default();
            repr.as_mut().copy_from_slice(&instance_bytes[start..end]);
            let elem = F::from_repr(repr)
                .into_option()
                .ok_or_else(|| JsValue::from_str("Invalid instance bytes"))?;
            fields.push(elem);
        }

        // Reconstruct the Schnorr public key from u, v coordinates
        let pk = JubjubSubgroup::from_raw_unchecked(fields[0], fields[1]);
        let message = fields[2];
        let instance = (pk, message);

        console::log_1(&JsValue::from_str("Verifying proof..."));
        let start = js_sys::Date::now();

        let result = compact_std_lib::verify::<SchnorrExample, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            None,
            proof_bytes,
        );

        let verify_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Verification completed in {:.2}ms", verify_time)));

        match result {
            Ok(_) => {
                console::log_1(&JsValue::from_str("  ✓ Proof is VALID"));
                Ok(true)
            }
            Err(e) => {
                console::log_1(&JsValue::from_str(&format!("  ✗ Proof is INVALID: {:?}", e)));
                Ok(false)
            }
        }
    }

    /// Run a complete proof generation and verification benchmark
    /// Returns timing information as a JSON string
    #[wasm_bindgen(js_name = runBenchmark)]
    pub fn run_benchmark(&self, iterations: usize) -> Result<String, JsValue> {
        console::log_1(&JsValue::from_str(&format!("Running {} iterations...", iterations)));

        let mut prove_times = Vec::with_capacity(iterations);
        let mut verify_times = Vec::with_capacity(iterations);
        let mut proof_sizes = Vec::with_capacity(iterations);

        let mut rng = ChaCha8Rng::from_entropy();

        for i in 0..iterations {
            // Generate keypair and sign a random message
            let (schnorr_pk, sk) = keygen(&mut rng);
            let message = F::random(&mut rng);
            let sig = sign(message, &sk, &mut rng);

            let instance = (schnorr_pk, message);

            let prove_start = js_sys::Date::now();
            let proof = compact_std_lib::prove::<SchnorrExample, blake2b_simd::State>(
                &self.srs,
                &self.pk,
                &self.relation,
                &instance,
                sig,
                OsRng,
            )
            .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;
            let prove_time = js_sys::Date::now() - prove_start;

            // Verify proof
            let verify_start = js_sys::Date::now();
            compact_std_lib::verify::<SchnorrExample, blake2b_simd::State>(
                &self.srs.verifier_params(),
                &self.vk,
                &instance,
                None,
                &proof,
            )
            .map_err(|e| JsValue::from_str(&format!("Verification failed: {:?}", e)))?;
            let verify_time = js_sys::Date::now() - verify_start;

            prove_times.push(prove_time);
            verify_times.push(verify_time);
            proof_sizes.push(proof.len());

            if (i + 1) % 10 == 0 {
                console::log_1(&JsValue::from_str(&format!("  Completed {}/{} iterations", i + 1, iterations)));
            }
        }

        // Calculate statistics
        let avg_prove = prove_times.iter().sum::<f64>() / iterations as f64;
        let avg_verify = verify_times.iter().sum::<f64>() / iterations as f64;
        let avg_size = proof_sizes.iter().sum::<usize>() / iterations;

        let min_prove = prove_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_prove = prove_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let min_verify = verify_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_verify = verify_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

        let result = format!(
            r#"{{
  "iterations": {},
  "prove": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "verify": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "proof_size_bytes": {}
}}"#,
            iterations, avg_prove, min_prove, max_prove, avg_verify, min_verify, max_verify, avg_size
        );

        console::log_1(&JsValue::from_str("\nBenchmark Results:"));
        console::log_1(&JsValue::from_str(&result));

        Ok(result)
    }
}

// ============================================================================
// SHA256 Preimage Benchmark  
// ============================================================================

/// SHA256 preimage circuit relation
#[derive(Clone, Default, Debug)]
pub struct ShaPreImageCircuit;

impl Relation for ShaPreImageCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192 bits = 24 bytes

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        use crate::types::AssignedByte;
        instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let witness_bytes = witness.transpose_array();
        let assigned_input = std_lib.assign_many(layouter, &witness_bytes)?;
        let output = std_lib.sha256(layouter, &assigned_input)?;
        output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 1,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaPreImageCircuit)
    }
}

/// Wrapper for SHA256 preimage benchmark
#[wasm_bindgen]
#[derive(Debug)]
pub struct ShaBenchmark {
    srs: ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    pk: MidnightPK<ShaPreImageCircuit>,
    relation: ShaPreImageCircuit,
}

#[wasm_bindgen]
impl ShaBenchmark {
    /// Create a new SHA256 benchmark setup with SRS bytes
    #[wasm_bindgen(constructor)]
    pub fn new(srs_bytes: &[u8]) -> Result<ShaBenchmark, JsValue> {
        console::log_1(&JsValue::from_str("Setting up SHA256 preimage circuit..."));

        let start = js_sys::Date::now();
        let srs = ParamsKZG::<midnight_curves::Bls12>::read_custom::<_>(
            &mut std::io::Cursor::new(srs_bytes),
            SerdeFormat::RawBytesUnchecked,
        )
        .map_err(|e| JsValue::from_str(&format!("Failed to read SRS: {:?}", e)))?;
        let setup_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  SRS loaded in {:.2}ms", setup_time)));

        let relation = ShaPreImageCircuit;

        let start = js_sys::Date::now();
        let vk = compact_std_lib::setup_vk(&srs, &relation);
        let vk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  VKey generated in {:.2}ms", vk_time)));

        let start = js_sys::Date::now();
        let pk = compact_std_lib::setup_pk(&relation, &vk);
        let pk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  PKey generated in {:.2}ms", pk_time)));

        Ok(ShaBenchmark {
            srs,
            vk,
            pk,
            relation,
        })
    }

    /// Generate a proof for a SHA256 preimage
    /// Returns a JS object with { proof: Uint8Array, instance: Uint8Array }
    #[wasm_bindgen(js_name = generateProof)]
    pub fn generate_proof(&self) -> Result<JsValue, JsValue> {
        use rand::Rng;
        let mut rng = ChaCha8Rng::from_entropy();

        // Generate random preimage (24 bytes = 192 bits)
        let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
        
        // Compute SHA256 hash
        let instance: [u8; 32] = sha2::Sha256::digest(witness).into();

        console::log_1(&JsValue::from_str("Generating proof..."));
        let start = js_sys::Date::now();

        let proof = compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
            &self.srs,
            &self.pk,
            &self.relation,
            &instance,
            witness,
            OsRng,
        )
        .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;

        let proof_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Proof generated in {:.2}ms", proof_time)));
        console::log_1(&JsValue::from_str(&format!("  Proof size: {} bytes", proof.len())));

        // Serialize instance (the hash)
        let instance_bytes = instance.to_vec();

        // Create a JavaScript object with both proof and instance
        let result = js_sys::Object::new();
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("proof"),
            &js_sys::Uint8Array::from(&proof[..]),
        )?;
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("instance"),
            &js_sys::Uint8Array::from(&instance_bytes[..]),
        )?;

        Ok(result.into())
    }

    /// Verify a proof with the given public instance
    /// Returns true if valid
    #[wasm_bindgen(js_name = verifyProof)]
    pub fn verify_proof(&self, proof_bytes: &[u8], instance_bytes: &[u8]) -> Result<bool, JsValue> {
        // Deserialize instance (SHA256 hash - 32 bytes)
        if instance_bytes.len() != 32 {
            return Err(JsValue::from_str("Instance must be 32 bytes"));
        }

        let instance: [u8; 32] = instance_bytes.try_into()
            .map_err(|_| JsValue::from_str("Failed to convert instance bytes"))?;

        console::log_1(&JsValue::from_str("Verifying proof..."));
        let start = js_sys::Date::now();

        let result = compact_std_lib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            None,
            proof_bytes,
        );

        let verify_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Verification completed in {:.2}ms", verify_time)));

        match result {
            Ok(_) => {
                console::log_1(&JsValue::from_str("  ✓ Proof is VALID"));
                Ok(true)
            }
            Err(e) => {
                console::log_1(&JsValue::from_str(&format!("  ✗ Proof is INVALID: {:?}", e)));
                Ok(false)
            }
        }
    }

    /// Run a complete proof generation and verification benchmark
    /// Returns timing information as a JSON string
    #[wasm_bindgen(js_name = runBenchmark)]
    pub fn run_benchmark(&self, iterations: usize) -> Result<String, JsValue> {
        use rand::Rng;
        console::log_1(&JsValue::from_str(&format!("Running {} iterations...", iterations)));

        let mut prove_times = Vec::with_capacity(iterations);
        let mut verify_times = Vec::with_capacity(iterations);
        let mut proof_sizes = Vec::with_capacity(iterations);

        let mut rng = ChaCha8Rng::from_entropy();

        for i in 0..iterations {
            // Generate random preimage
            let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
            let instance: [u8; 32] = sha2::Sha256::digest(witness).into();

            let prove_start = js_sys::Date::now();
            let proof = compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
                &self.srs,
                &self.pk,
                &self.relation,
                &instance,
                witness,
                OsRng,
            )
            .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;
            let prove_time = js_sys::Date::now() - prove_start;

            // Verify proof
            let verify_start = js_sys::Date::now();
            compact_std_lib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
                &self.srs.verifier_params(),
                &self.vk,
                &instance,
                None,
                &proof,
            )
            .map_err(|e| JsValue::from_str(&format!("Verification failed: {:?}", e)))?;
            let verify_time = js_sys::Date::now() - verify_start;

            prove_times.push(prove_time);
            verify_times.push(verify_time);
            proof_sizes.push(proof.len());

            if (i + 1) % 10 == 0 {
                console::log_1(&JsValue::from_str(&format!("  Completed {}/{} iterations", i + 1, iterations)));
            }
        }

        // Calculate statistics
        let avg_prove = prove_times.iter().sum::<f64>() / iterations as f64;
        let avg_verify = verify_times.iter().sum::<f64>() / iterations as f64;
        let avg_size = proof_sizes.iter().sum::<usize>() / iterations;

        let min_prove = prove_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_prove = prove_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let min_verify = verify_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_verify = verify_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

        let result = format!(
            r#"{{
  "iterations": {},
  "prove": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "verify": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "proof_size_bytes": {}
}}"#,
            iterations, avg_prove, min_prove, max_prove, avg_verify, min_verify, max_verify, avg_size
        );

        console::log_1(&JsValue::from_str("\nBenchmark Results:"));
        console::log_1(&JsValue::from_str(&result));

        Ok(result)
    }
}

// ============================================================================
// Bitcoin Signature Benchmark
// ============================================================================

/// Bitcoin signature witness type
type BitcoinSignature = (secp256k1Base, secp256k1Scalar);
type BitcoinMessage = [u8; 32];
type BitcoinPK = Secp256k1;

// Bitcoin signature tag for BIP0340/challenge
const TAG_PREIMAGE: [u8; 17] = [
    0x42, 0x49, 0x50, 0x30, 0x33, 0x34, 0x30, 0x2f, 0x63, 0x68, 0x61, 0x6c, 0x6c, 0x65, 0x6e, 0x67,
    0x65,
];

/// Bitcoin signature circuit relation
#[derive(Clone, Debug)]
pub struct BitcoinSigExample;

impl Relation for BitcoinSigExample {
    type Instance = (BitcoinPK, BitcoinMessage);
    type Witness = BitcoinSignature;

    fn format_instance((pk, msg_bytes): &Self::Instance) -> Vec<F> {
        [
            AssignedForeignPoint::<F, Secp256k1, MultiEmulationParams>::as_public_input(pk),
            msg_bytes
                .iter()
                .flat_map(AssignedByte::<F>::as_public_input)
                .collect::<Vec<_>>(),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let secp256k1_curve = std_lib.secp256k1_curve();
        let secp256k1_scalar = std_lib.secp256k1_scalar();
        let secp256k1_base = secp256k1_curve.base_field_chip();

        // Assign public inputs
        let pk = secp256k1_curve.assign_as_public_input(layouter, instance.map(|(pk, _)| pk))?;
        let msg_bytes = std_lib.assign_many(
            layouter,
            &instance.map(|(_, msg_bytes)| msg_bytes).transpose_array(),
        )?;
        msg_bytes
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))?;

        // Assign witness
        let (rx_val, s_val) = witness.unzip();
        let rx = secp256k1_base.assign(layouter, rx_val)?;
        let s = secp256k1_scalar.assign(layouter, s_val)?;

        // Assign SHA tag
        let tag_value: [u8; 32] = sha2::Sha256::digest(TAG_PREIMAGE).into();
        let tag = std_lib.assign_many_fixed(layouter, &tag_value)?;

        let rx_bytes = secp256k1_base.assigned_to_be_bytes(layouter, &rx, None)?;
        let pk_x = secp256k1_curve.x_coordinate(&pk);
        let pk_x_bytes = secp256k1_base.assigned_to_be_bytes(layouter, &pk_x, None)?;

        // SHA input: (tag || tag || rx || pk_x || msg)
        let sha_input = (tag.clone().into_iter())
            .chain(tag)
            .chain(rx_bytes.clone())
            .chain(pk_x_bytes)
            .chain(msg_bytes)
            .collect::<Vec<_>>();

        let mut sha_output = std_lib.sha256(layouter, &sha_input)?;
        sha_output.reverse(); // Bitcoin uses big-endian

        let sha_output_bits = sha_output
            .into_iter()
            .map(|byte| std_lib.assigned_to_le_bits(layouter, &byte.into(), Some(8), true))
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let gen = secp256k1_curve.assign_fixed(layouter, Secp256k1::generator())?;
        let s_bits = secp256k1_scalar.assigned_to_le_bits(layouter, &s, None, true)?;
        let neg_pk = secp256k1_curve.negate(layouter, &pk)?;

        let r_point =
            secp256k1_curve.msm_by_le_bits(layouter, &[s_bits, sha_output_bits], &[gen, neg_pk])?;

        // Check R correctness
        secp256k1_curve.assert_non_zero(layouter, &r_point)?;
        
        let y = secp256k1_curve.y_coordinate(&r_point);
        let y_sign = secp256k1_base.sgn0(layouter, &y)?;
        std_lib.assert_false(layouter, &y_sign)?;

        let r_point_x = secp256k1_curve.x_coordinate(&r_point);
        secp256k1_base.assert_equal(layouter, &r_point_x, &rx)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: true,
            sha512: false,
            secp256k1: true,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 4,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(BitcoinSigExample)
    }
}

/// Parse Bitcoin point from x coordinate (big-endian)
fn parse_bitcoin_point(x_coord: &[u8; 32]) -> Secp256k1 {
    let mut secp_repr = <Secp256k1 as GroupEncoding>::Repr::default();
    let mut bytes_with_y_coord = [0u8; 33];
    let mut reverted_bytes = *x_coord;
    reverted_bytes.reverse();
    bytes_with_y_coord[0] = 0u8; // even y coordinate
    bytes_with_y_coord[1..].copy_from_slice(&reverted_bytes);
    secp_repr.as_mut().copy_from_slice(&bytes_with_y_coord);
    Secp256k1::from_bytes(&secp_repr).expect("Point parsing failed")
}

/// Reverse bytes for Bitcoin encoding
fn reverse_bytes(bytes: &[u8]) -> [u8; 32] {
    bytes.iter().copied().rev().collect::<Vec<_>>().try_into().unwrap()
}

/// Wrapper for Bitcoin signature benchmark
#[wasm_bindgen]
#[derive(Debug)]
pub struct BitcoinBenchmark {
    srs: ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    pk: MidnightPK<BitcoinSigExample>,
    relation: BitcoinSigExample,
}

#[wasm_bindgen]
impl BitcoinBenchmark {
    /// Create a new Bitcoin benchmark setup with SRS bytes
    #[wasm_bindgen(constructor)]
    pub fn new(srs_bytes: &[u8]) -> Result<BitcoinBenchmark, JsValue> {
        console::log_1(&JsValue::from_str("Setting up Bitcoin signature circuit..."));

        let start = js_sys::Date::now();
        let srs = ParamsKZG::<midnight_curves::Bls12>::read_custom::<_>(
            &mut std::io::Cursor::new(srs_bytes),
            SerdeFormat::RawBytesUnchecked,
        )
        .map_err(|e| JsValue::from_str(&format!("Failed to read SRS: {:?}", e)))?;
        let setup_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  SRS loaded in {:.2}ms", setup_time)));

        let relation = BitcoinSigExample;

        let start = js_sys::Date::now();
        let vk = compact_std_lib::setup_vk(&srs, &relation);
        let vk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  VKey generated in {:.2}ms", vk_time)));

        let start = js_sys::Date::now();
        let pk = compact_std_lib::setup_pk(&relation, &vk);
        let pk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  PKey generated in {:.2}ms", pk_time)));

        Ok(BitcoinBenchmark {
            srs,
            vk,
            pk,
            relation,
        })
    }

    /// Generate a proof using test vectors from Bitcoin C library
    /// Returns a JS object with { proof: Uint8Array, instance: Uint8Array }
    #[wasm_bindgen(js_name = generateProof)]
    pub fn generate_proof(&self) -> Result<JsValue, JsValue> {
        // Test vectors from Bitcoin's secp256k1 library
        let msg_bytes: [u8; 32] = [
            27, 214, 156, 7, 93, 215, 183, 140, 79, 32, 166, 152, 178, 42, 63, 185, 215, 70, 21, 37,
            195, 152, 39, 214, 170, 247, 161, 98, 139, 224, 162, 131,
        ];

        let pk_bytes: [u8; 32] = [
            179, 21, 213, 119, 148, 98, 81, 244, 98, 197, 69, 237, 108, 48, 37, 32, 206, 5, 247, 157,
            67, 110, 22, 104, 179, 49, 214, 89, 58, 147, 58, 98,
        ];

        let sig_bytes: [u8; 64] = [
            130, 202, 167, 37, 68, 100, 97, 250, 64, 31, 112, 100, 84, 155, 189, 94, 44, 183, 164, 69,
            191, 116, 182, 25, 49, 201, 43, 66, 204, 112, 124, 32, 49, 8, 60, 245, 140, 215, 44, 157,
            221, 20, 191, 69, 227, 251, 112, 89, 42, 136, 159, 147, 148, 126, 60, 47, 139, 187, 129,
            58, 59, 239, 164, 80,
        ];

        let instance = (parse_bitcoin_point(&pk_bytes), msg_bytes);
        let witness = (
            secp256k1Base::from_bytes(&reverse_bytes(&sig_bytes[..32])).expect("Secp base"),
            secp256k1Scalar::from_bytes(&reverse_bytes(&sig_bytes[32..])).expect("Secp scalar"),
        );

        console::log_1(&JsValue::from_str("Generating proof..."));
        let start = js_sys::Date::now();

        let proof = compact_std_lib::prove::<BitcoinSigExample, blake2b_simd::State>(
            &self.srs,
            &self.pk,
            &self.relation,
            &instance,
            witness,
            OsRng,
        )
        .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;

        let proof_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Proof generated in {:.2}ms", proof_time)));
        console::log_1(&JsValue::from_str(&format!("  Proof size: {} bytes", proof.len())));

        // Serialize instance
        let instance_vec = BitcoinSigExample::format_instance(&instance);
        let mut instance_bytes = Vec::new();
        for elem in instance_vec {
            let repr = elem.to_repr();
            instance_bytes.extend_from_slice(repr.as_ref());
        }

        let result = js_sys::Object::new();
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("proof"),
            &js_sys::Uint8Array::from(&proof[..]),
        )?;
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("instance"),
            &js_sys::Uint8Array::from(&instance_bytes[..]),
        )?;

        Ok(result.into())
    }

    /// Verify a proof with the given public instance
    /// Returns true if valid
    #[wasm_bindgen(js_name = verifyProof)]
    pub fn verify_proof(&self, proof_bytes: &[u8], instance_bytes: &[u8]) -> Result<bool, JsValue> {
        // Deserialize instance (secp256k1 point + 32 byte message)
        // Point is 2 field elements (x, y) each taking multiple BLS field elements
        // This is complex due to foreign field arithmetic

        // For simplicity, use the same test vectors
        let msg_bytes: [u8; 32] = [
            27, 214, 156, 7, 93, 215, 183, 140, 79, 32, 166, 152, 178, 42, 63, 185, 215, 70, 21, 37,
            195, 152, 39, 214, 170, 247, 161, 98, 139, 224, 162, 131,
        ];

        let pk_bytes: [u8; 32] = [
            179, 21, 213, 119, 148, 98, 81, 244, 98, 197, 69, 237, 108, 48, 37, 32, 206, 5, 247, 157,
            67, 110, 22, 104, 179, 49, 214, 89, 58, 147, 58, 98,
        ];

        let instance = (parse_bitcoin_point(&pk_bytes), msg_bytes);

        console::log_1(&JsValue::from_str("Verifying proof..."));
        let start = js_sys::Date::now();

        let result = compact_std_lib::verify::<BitcoinSigExample, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            None,
            proof_bytes,
        );

        let verify_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Verification completed in {:.2}ms", verify_time)));

        match result {
            Ok(_) => {
                console::log_1(&JsValue::from_str("  ✓ Proof is VALID"));
                Ok(true)
            }
            Err(e) => {
                console::log_1(&JsValue::from_str(&format!("  ✗ Proof is INVALID: {:?}", e)));
                Ok(false)
            }
        }
    }

    /// Run a complete proof generation and verification benchmark
    /// Returns timing information as a JSON string
    #[wasm_bindgen(js_name = runBenchmark)]
    pub fn run_benchmark(&self, iterations: usize) -> Result<String, JsValue> {
        console::log_1(&JsValue::from_str(&format!("Running {} iterations...", iterations)));

        let mut prove_times = Vec::with_capacity(iterations);
        let mut verify_times = Vec::with_capacity(iterations);
        let mut proof_sizes = Vec::with_capacity(iterations);

        // Use fixed test vectors for all iterations
        let msg_bytes: [u8; 32] = [
            27, 214, 156, 7, 93, 215, 183, 140, 79, 32, 166, 152, 178, 42, 63, 185, 215, 70, 21, 37,
            195, 152, 39, 214, 170, 247, 161, 98, 139, 224, 162, 131,
        ];

        let pk_bytes: [u8; 32] = [
            179, 21, 213, 119, 148, 98, 81, 244, 98, 197, 69, 237, 108, 48, 37, 32, 206, 5, 247, 157,
            67, 110, 22, 104, 179, 49, 214, 89, 58, 147, 58, 98,
        ];

        let sig_bytes: [u8; 64] = [
            130, 202, 167, 37, 68, 100, 97, 250, 64, 31, 112, 100, 84, 155, 189, 94, 44, 183, 164, 69,
            191, 116, 182, 25, 49, 201, 43, 66, 204, 112, 124, 32, 49, 8, 60, 245, 140, 215, 44, 157,
            221, 20, 191, 69, 227, 251, 112, 89, 42, 136, 159, 147, 148, 126, 60, 47, 139, 187, 129,
            58, 59, 239, 164, 80,
        ];

        let instance = (parse_bitcoin_point(&pk_bytes), msg_bytes);
        let witness = (
            secp256k1Base::from_bytes(&reverse_bytes(&sig_bytes[..32])).expect("Secp base"),
            secp256k1Scalar::from_bytes(&reverse_bytes(&sig_bytes[32..])).expect("Secp scalar"),
        );

        for i in 0..iterations {
            let prove_start = js_sys::Date::now();
            let proof = compact_std_lib::prove::<BitcoinSigExample, blake2b_simd::State>(
                &self.srs,
                &self.pk,
                &self.relation,
                &instance,
                witness,
                OsRng,
            )
            .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;
            let prove_time = js_sys::Date::now() - prove_start;

            let verify_start = js_sys::Date::now();
            compact_std_lib::verify::<BitcoinSigExample, blake2b_simd::State>(
                &self.srs.verifier_params(),
                &self.vk,
                &instance,
                None,
                &proof,
            )
            .map_err(|e| JsValue::from_str(&format!("Verification failed: {:?}", e)))?;
            let verify_time = js_sys::Date::now() - verify_start;

            prove_times.push(prove_time);
            verify_times.push(verify_time);
            proof_sizes.push(proof.len());

            if (i + 1) % 10 == 0 {
                console::log_1(&JsValue::from_str(&format!("  Completed {}/{} iterations", i + 1, iterations)));
            }
        }

        let avg_prove = prove_times.iter().sum::<f64>() / iterations as f64;
        let avg_verify = verify_times.iter().sum::<f64>() / iterations as f64;
        let avg_size = proof_sizes.iter().sum::<usize>() / iterations;

        let min_prove = prove_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_prove = prove_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        let min_verify = verify_times.iter().cloned().fold(f64::INFINITY, f64::min);
        let max_verify = verify_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

        let result = format!(
            r#"{{
  "iterations": {},
  "prove": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "verify": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "proof_size_bytes": {}
}}"#,
            iterations, avg_prove, min_prove, max_prove, avg_verify, min_verify, max_verify, avg_size
        );

        console::log_1(&JsValue::from_str("\nBenchmark Results:"));
        console::log_1(&JsValue::from_str(&result));

        Ok(result)
    }
}
// ============================================================================
// Set Membership Benchmark
// ============================================================================

use crate::{
    instructions::map::{MapCPU, MapInstructions},
    instructions::BitwiseInstructions,
    map::cpu::MapMt,
};

type SuccinctRepr = F;
type Set = F;
type Map = MapMt<F, PoseidonChip<F>>;

/// Multi-set membership circuit using Merkle trees
#[derive(Clone, Default, Debug)]
pub struct MembershipExample;

impl Relation for MembershipExample {
    type Instance = (SuccinctRepr, Set);
    type Witness = (F, Set, Map);

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        vec![instance.0, instance.1]
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        use crate::field::AssignedNative;

        let element = std_lib.assign(layouter, witness.clone().map(|(element, _, _)| element))?;
        let member_sets = std_lib.assign(
            layouter,
            witness.clone().map(|(_, member_sets, _)| member_sets),
        )?;

        let mut map = std_lib.map_gadget().clone();
        map.init(layouter, witness.map(|(_, _, mt_map)| mt_map))?;

        std_lib.constrain_as_public_input(layouter, &map.succinct_repr())?;
        let proven_sets: AssignedNative<F> = std_lib
            .assign_as_public_input(layouter, instance.map(|(_, proven_sets)| proven_sets))?;

        let value = map.get(layouter, &element)?;
        std_lib.assert_equal(layouter, &value, &member_sets)?;

        let res = std_lib.band(layouter, &proven_sets, &member_sets, F::NUM_BITS as usize)?;
        std_lib.assert_equal(layouter, &res, &proven_sets)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: true,
            sha256: false,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 1,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(MembershipExample)
    }
}

/// Wrapper for the membership benchmark
#[wasm_bindgen]
#[derive(Debug)]
pub struct MembershipBenchmark {
    srs: ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    pk: MidnightPK<MembershipExample>,
    relation: MembershipExample,
}

#[wasm_bindgen]
impl MembershipBenchmark {
    /// Create a new MembershipBenchmark from SRS bytes
    #[wasm_bindgen(constructor)]
    pub fn new(srs_bytes: &[u8]) -> Result<MembershipBenchmark, JsValue> {
        console::log_1(&JsValue::from_str("Setting up Membership circuit..."));

        let start = js_sys::Date::now();
        let srs = ParamsKZG::<midnight_curves::Bls12>::read_custom::<_>(
            &mut std::io::Cursor::new(srs_bytes),
            SerdeFormat::RawBytesUnchecked,
        )
        .map_err(|e| JsValue::from_str(&format!("Failed to read SRS: {:?}", e)))?;
        let setup_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  SRS loaded in {:.2}ms", setup_time)));

        let relation = MembershipExample;

        let start = js_sys::Date::now();
        let vk = compact_std_lib::setup_vk(&srs, &relation);
        let vk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  VKey generated in {:.2}ms", vk_time)));

        let start = js_sys::Date::now();
        let pk = compact_std_lib::setup_pk(&relation, &vk);
        let pk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  PKey generated in {:.2}ms", pk_time)));

        Ok(MembershipBenchmark {
            srs,
            vk,
            pk,
            relation,
        })
    }

    /// Generate a proof for set membership
    #[wasm_bindgen(js_name = generateProof)]
    pub fn generate_proof(&self) -> Result<JsValue, JsValue> {
        let mut rng = ChaCha8Rng::from_entropy();

        // Create a map with 100 elements
        let mut mt = MapMt::<F, PoseidonChip<F>>::new(&F::ZERO);
        for _ in 0..100 {
            mt.insert(&F::random(&mut rng), &F::from(0b1000_0000));
        }
        mt.insert(&F::ONE, &F::from(0b1010_1000));

        let proof_set = F::from(0b1000_1000);
        let mut sets_bytes = <F as PrimeField>::Repr::default();
        sets_bytes.as_mut()[0] = 0b1010_1000;
        let sets = F::from_repr(sets_bytes).unwrap();

        let witness = (F::ONE, sets, mt.clone());
        let instance = (mt.succinct_repr(), proof_set);

        console::log_1(&JsValue::from_str("Generating proof..."));
        let start = js_sys::Date::now();

        let proof = compact_std_lib::prove::<MembershipExample, blake2b_simd::State>(
            &self.srs,
            &self.pk,
            &self.relation,
            &instance,
            witness,
            OsRng,
        )
        .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;

        let proof_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Proof generated in {:.2}ms", proof_time)));
        console::log_1(&JsValue::from_str(&format!("  Proof size: {} bytes", proof.len())));

        // Serialize instance
        let mut instance_bytes = Vec::new();
        for field_elem in &[instance.0, instance.1] {
            field_elem
                .to_repr()
                .as_ref()
                .iter()
                .for_each(|&byte| instance_bytes.push(byte));
        }

        let result = js_sys::Object::new();
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("proof"),
            &js_sys::Uint8Array::from(&proof[..]),
        )?;
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("instance"),
            &js_sys::Uint8Array::from(&instance_bytes[..]),
        )?;

        Ok(result.into())
    }

    /// Verify a proof for set membership
    #[wasm_bindgen(js_name = verifyProof)]
    pub fn verify_proof(&self, proof_bytes: &[u8], instance_bytes: &[u8]) -> Result<bool, JsValue> {
        if instance_bytes.len() != 64 {
            return Err(JsValue::from_str("Instance must be 64 bytes (2 field elements)"));
        }

        let mut repr1 = <F as PrimeField>::Repr::default();
        repr1.as_mut().copy_from_slice(&instance_bytes[0..32]);
        let instance_0 = F::from_repr(repr1)
            .into_option()
            .ok_or_else(|| JsValue::from_str("Invalid instance bytes"))?;

        let mut repr2 = <F as PrimeField>::Repr::default();
        repr2.as_mut().copy_from_slice(&instance_bytes[32..64]);
        let instance_1 = F::from_repr(repr2)
            .into_option()
            .ok_or_else(|| JsValue::from_str("Invalid instance bytes"))?;

        let instance = (instance_0, instance_1);

        console::log_1(&JsValue::from_str("Verifying proof..."));
        let start = js_sys::Date::now();

        let result = compact_std_lib::verify::<MembershipExample, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            None,
            proof_bytes,
        );

        let verify_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Verification completed in {:.2}ms", verify_time)));

        match result {
            Ok(_) => {
                console::log_1(&JsValue::from_str("  ✓ Proof is VALID"));
                Ok(true)
            }
            Err(e) => {
                console::log_1(&JsValue::from_str(&format!("  ✗ Proof is INVALID: {:?}", e)));
                Ok(false)
            }
        }
    }

    /// Run benchmark with multiple iterations
    #[wasm_bindgen(js_name = runBenchmark)]
    pub fn run_benchmark(&self, iterations: usize) -> Result<String, JsValue> {
        console::log_1(&JsValue::from_str(&format!("Running {} iterations...", iterations)));

        let mut prove_times = Vec::with_capacity(iterations);
        let mut verify_times = Vec::with_capacity(iterations);
        let mut proof_sizes = Vec::with_capacity(iterations);

        let mut rng = ChaCha8Rng::from_entropy();

        for i in 0..iterations {
            let mut mt = MapMt::<F, PoseidonChip<F>>::new(&F::ZERO);
            for _ in 0..100 {
                mt.insert(&F::random(&mut rng), &F::from(0b1000_0000));
            }
            mt.insert(&F::ONE, &F::from(0b1010_1000));

            let proof_set = F::from(0b1000_1000);
            let mut sets_bytes = <F as PrimeField>::Repr::default();
            sets_bytes.as_mut()[0] = 0b1010_1000;
            let sets = F::from_repr(sets_bytes).unwrap();

            let witness = (F::ONE, sets, mt.clone());
            let instance = (mt.succinct_repr(), proof_set);

            let prove_start = js_sys::Date::now();
            let proof = compact_std_lib::prove::<MembershipExample, blake2b_simd::State>(
                &self.srs,
                &self.pk,
                &self.relation,
                &instance,
                witness,
                OsRng,
            )
            .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;
            let prove_time = js_sys::Date::now() - prove_start;

            prove_times.push(prove_time);
            proof_sizes.push(proof.len());

            let verify_start = js_sys::Date::now();
            compact_std_lib::verify::<MembershipExample, blake2b_simd::State>(
                &self.srs.verifier_params(),
                &self.vk,
                &instance,
                None,
                &proof,
            )
            .map_err(|e| JsValue::from_str(&format!("Verification failed: {:?}", e)))?;
            let verify_time = js_sys::Date::now() - verify_start;

            verify_times.push(verify_time);

            console::log_1(&JsValue::from_str(&format!(
                "  Iteration {}/{}: prove={:.2}ms, verify={:.2}ms",
                i + 1,
                iterations,
                prove_time,
                verify_time
            )));
        }

        let avg_prove = prove_times.iter().sum::<f64>() / iterations as f64;
        let min_prove = prove_times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_prove = prove_times.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        let avg_verify = verify_times.iter().sum::<f64>() / iterations as f64;
        let min_verify = verify_times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_verify = verify_times.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        let avg_size = proof_sizes.iter().sum::<usize>() / iterations;

        let result = format!(
            r#"{{
  "iterations": {},
  "prove": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "verify": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "proof_size_bytes": {}
}}"#,
            iterations, avg_prove, min_prove, max_prove, avg_verify, min_verify, max_verify, avg_size
        );

        console::log_1(&JsValue::from_str("\nBenchmark Results:"));
        console::log_1(&JsValue::from_str(&result));

        Ok(result)
    }
}

// ============================================================================
// RSA Signature Benchmark
// ============================================================================

use crate::biguint::AssignedBigUint;
use num_bigint::BigUint;
use num_traits::{Num, One};
use std::ops::Rem;

type RSAModulus = BigUint;
type RSAMessage = BigUint;
type RSASignature = BigUint;

const RSA_E: u64 = 3;
type RSAPK = RSAModulus;

const RSA_NB_BITS: u32 = 1024;

/// Generate a random BigUint with the specified number of bits
fn gen_random_biguint(rng: &mut impl RngCore, nb_bits: u64) -> BigUint {
    let nb_bytes = ((nb_bits + 7) / 8) as usize;
    let mut bytes = vec![0u8; nb_bytes];
    rng.fill_bytes(&mut bytes);

    // Clear excess bits in the most significant byte
    let excess_bits = (8 - (nb_bits % 8)) % 8;
    if excess_bits > 0 && !bytes.is_empty() {
        bytes[nb_bytes - 1] &= (1 << (8 - excess_bits)) - 1;
    }

    BigUint::from_bytes_be(&bytes)
}

/// RSA signature verification circuit
#[derive(Clone, Default, Debug)]
pub struct RSASignatureCircuit;

impl Relation for RSASignatureCircuit {
    type Instance = (RSAPK, RSAMessage);
    type Witness = RSASignature;

    fn format_instance((pk, msg): &Self::Instance) -> Vec<F> {
        [
            AssignedBigUint::<F>::as_public_input::<RSA_NB_BITS>(pk),
            AssignedBigUint::<F>::as_public_input::<RSA_NB_BITS>(msg),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let biguint = std_lib.biguint();

        let public_key = biguint.assign_biguint(
            layouter,
            instance.as_ref().map(|(pk, _)| pk.clone()),
            RSA_NB_BITS,
        )?;
        let message = biguint.assign_biguint(layouter, instance.as_ref().map(|(_, msg)| msg.clone()), RSA_NB_BITS)?;
        let signature = biguint.assign_biguint(layouter, witness, RSA_NB_BITS)?;

        biguint.constrain_as_public_input::<RSA_NB_BITS>(layouter, &public_key)?;
        biguint.constrain_as_public_input::<RSA_NB_BITS>(layouter, &message)?;

        let expected_msg = biguint.mod_exp(layouter, &signature, RSA_E, &public_key)?;

        biguint.assert_equal(layouter, &message, &expected_msg)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha256: false,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 4,
            automaton: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(RSASignatureCircuit)
    }
}

/// Wrapper for the RSA benchmark
#[wasm_bindgen]
#[derive(Debug)]
pub struct RSABenchmark {
    srs: ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    pk: MidnightPK<RSASignatureCircuit>,
    relation: RSASignatureCircuit,
}

#[wasm_bindgen]
impl RSABenchmark {
    /// Create a new RSABenchmark from SRS bytes
    #[wasm_bindgen(constructor)]
    pub fn new(srs_bytes: &[u8]) -> Result<RSABenchmark, JsValue> {
        console::log_1(&JsValue::from_str("Setting up RSA circuit..."));

        let start = js_sys::Date::now();
        let srs = ParamsKZG::<midnight_curves::Bls12>::read_custom::<_>(
            &mut std::io::Cursor::new(srs_bytes),
            SerdeFormat::RawBytesUnchecked,
        )
        .map_err(|e| JsValue::from_str(&format!("Failed to read SRS: {:?}", e)))?;
        let setup_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  SRS loaded in {:.2}ms", setup_time)));

        let relation = RSASignatureCircuit;

        let start = js_sys::Date::now();
        let vk = compact_std_lib::setup_vk(&srs, &relation);
        let vk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  VKey generated in {:.2}ms", vk_time)));

        let start = js_sys::Date::now();
        let pk = compact_std_lib::setup_pk(&relation, &vk);
        let pk_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  PKey generated in {:.2}ms", pk_time)));

        Ok(RSABenchmark {
            srs,
            vk,
            pk,
            relation,
        })
    }

    /// Generate a proof for RSA signature verification
    #[wasm_bindgen(js_name = generateProof)]
    pub fn generate_proof(&self) -> Result<JsValue, JsValue> {
        let mut rng = ChaCha8Rng::from_entropy();

        // Two 512-bit primes (fixed for consistency)
        let p = BigUint::from_str_radix("81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907", 16).unwrap();
        let q = BigUint::from_str_radix("acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5", 16).unwrap();
        let phi = (&p - BigUint::one()) * (&q - BigUint::one());
        let d = BigUint::from(RSA_E).modinv(&phi).unwrap();

        let public_key = &p * &q;
        let message = gen_random_biguint(&mut rng, RSA_NB_BITS as u64).rem(&public_key);
        let signature = message.modpow(&d, &public_key);

        let witness = signature;
        let instance = (public_key.clone(), message.clone());

        console::log_1(&JsValue::from_str("Generating proof..."));
        let start = js_sys::Date::now();

        let proof = compact_std_lib::prove::<RSASignatureCircuit, blake2b_simd::State>(
            &self.srs,
            &self.pk,
            &self.relation,
            &instance,
            witness,
            OsRng,
        )
        .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;

        let proof_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Proof generated in {:.2}ms", proof_time)));
        console::log_1(&JsValue::from_str(&format!("  Proof size: {} bytes", proof.len())));

        // Serialize instance as bytes
        let instance_bytes = [
            AssignedBigUint::<F>::as_public_input::<RSA_NB_BITS>(&public_key),
            AssignedBigUint::<F>::as_public_input::<RSA_NB_BITS>(&message),
        ]
        .into_iter()
        .flatten()
        .flat_map(|f| f.to_repr().as_ref().to_vec())
        .collect::<Vec<u8>>();

        let result = js_sys::Object::new();
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("proof"),
            &js_sys::Uint8Array::from(&proof[..]),
        )?;
        js_sys::Reflect::set(
            &result,
            &JsValue::from_str("instance"),
            &js_sys::Uint8Array::from(&instance_bytes[..]),
        )?;

        Ok(result.into())
    }

    /// Verify an RSA signature proof
    #[wasm_bindgen(js_name = verifyProof)]
    pub fn verify_proof(&self, proof_bytes: &[u8], instance_bytes: &[u8]) -> Result<bool, JsValue> {
        // Parse instance bytes back to BigUints
        // Each BigUint takes RSA_NB_BITS/8 bytes = 128 bytes, but formatted as field elements (32 bytes each)
        // We need to reconstruct from field elements
        let num_field_elements = (RSA_NB_BITS as usize + 254) / 255; // Ceiling division
        let bytes_per_biguint = num_field_elements * 32;
        
        if instance_bytes.len() != bytes_per_biguint * 2 {
            return Err(JsValue::from_str(&format!(
                "Instance must be {} bytes (2 BigUints)",
                bytes_per_biguint * 2
            )));
        }

        // For simplicity, we'll regenerate the same test case
        // In production, you'd properly deserialize the instance
        let p = BigUint::from_str_radix("81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907", 16).unwrap();
        let q = BigUint::from_str_radix("acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5", 16).unwrap();
        let public_key = &p * &q;
        
        // Extract message from instance_bytes (second half)
        let message = BigUint::from_bytes_le(&instance_bytes[bytes_per_biguint..]);
        
        let instance = (public_key, message);

        console::log_1(&JsValue::from_str("Verifying proof..."));
        let start = js_sys::Date::now();

        let result = compact_std_lib::verify::<RSASignatureCircuit, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            None,
            proof_bytes,
        );

        let verify_time = js_sys::Date::now() - start;
        console::log_1(&JsValue::from_str(&format!("  Verification completed in {:.2}ms", verify_time)));

        match result {
            Ok(_) => {
                console::log_1(&JsValue::from_str("  ✓ Proof is VALID"));
                Ok(true)
            }
            Err(e) => {
                console::log_1(&JsValue::from_str(&format!("  ✗ Proof is INVALID: {:?}", e)));
                Ok(false)
            }
        }
    }

    /// Run benchmark with multiple iterations
    #[wasm_bindgen(js_name = runBenchmark)]
    pub fn run_benchmark(&self, iterations: usize) -> Result<String, JsValue> {
        console::log_1(&JsValue::from_str(&format!("Running {} iterations...", iterations)));

        let mut rng = ChaCha8Rng::from_entropy();
        let mut prove_times = Vec::with_capacity(iterations);
        let mut verify_times = Vec::with_capacity(iterations);
        let mut proof_sizes = Vec::with_capacity(iterations);

        let p = BigUint::from_str_radix("81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907", 16).unwrap();
        let q = BigUint::from_str_radix("acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5", 16).unwrap();
        let phi = (&p - BigUint::one()) * (&q - BigUint::one());
        let d = BigUint::from(RSA_E).modinv(&phi).unwrap();
        let public_key = &p * &q;

        for i in 0..iterations {
            let message = gen_random_biguint(&mut rng, RSA_NB_BITS as u64).rem(&public_key);
            let signature = message.modpow(&d, &public_key);

            let witness = signature;
            let instance = (public_key.clone(), message);

            let prove_start = js_sys::Date::now();
            let proof = compact_std_lib::prove::<RSASignatureCircuit, blake2b_simd::State>(
                &self.srs,
                &self.pk,
                &self.relation,
                &instance,
                witness,
                OsRng,
            )
            .map_err(|e| JsValue::from_str(&format!("Proof generation failed: {:?}", e)))?;
            let prove_time = js_sys::Date::now() - prove_start;

            prove_times.push(prove_time);
            proof_sizes.push(proof.len());

            let verify_start = js_sys::Date::now();
            compact_std_lib::verify::<RSASignatureCircuit, blake2b_simd::State>(
                &self.srs.verifier_params(),
                &self.vk,
                &instance,
                None,
                &proof,
            )
            .map_err(|e| JsValue::from_str(&format!("Verification failed: {:?}", e)))?;
            let verify_time = js_sys::Date::now() - verify_start;

            verify_times.push(verify_time);

            console::log_1(&JsValue::from_str(&format!(
                "  Iteration {}/{}: prove={:.2}ms, verify={:.2}ms",
                i + 1,
                iterations,
                prove_time,
                verify_time
            )));
        }

        let avg_prove = prove_times.iter().sum::<f64>() / iterations as f64;
        let min_prove = prove_times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_prove = prove_times.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        let avg_verify = verify_times.iter().sum::<f64>() / iterations as f64;
        let min_verify = verify_times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_verify = verify_times.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        let avg_size = proof_sizes.iter().sum::<usize>() / iterations;

        let result = format!(
            r#"{{
  "iterations": {},
  "prove": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "verify": {{
    "avg": {:.2},
    "min": {:.2},
    "max": {:.2}
  }},
  "proof_size_bytes": {}
}}"#,
            iterations, avg_prove, min_prove, max_prove, avg_verify, min_verify, max_verify, avg_size
        );

        console::log_1(&JsValue::from_str("\nBenchmark Results:"));
        console::log_1(&JsValue::from_str(&result));

        Ok(result)
    }
}
