//! Comprehensive proof generation benchmark with GPU acceleration
//! 
//! This benchmark measures MSM performance with realistic circuit-sized operations.
//! Uses the midnight_circuits high-level API to generate actual proofs.

use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    instructions::{AssignmentInstructions, PublicInputInstructions},
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedByte, Instantiable},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_curves::Fq as F;
use rand::{rngs::OsRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;
use std::time::Instant;

/// SHA256 preimage circuit - realistic benchmark with actual computation
#[derive(Clone, Default)]
pub struct ShaPreImageCircuit;

impl Relation for ShaPreImageCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192 bits

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
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

fn benchmark_proof_generation(k: u32) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== K={} ({} rows) ===", k, 1 << k);
    
    // Step 1: Load SRS parameters
    print!("  [1/4] Loading SRS params... ");
    let start = Instant::now();
    let srs = filecoin_srs(k);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    let relation = ShaPreImageCircuit;
    
    // Step 2: Setup verification key
    print!("  [2/4] Setup VK... ");
    let start = Instant::now();
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    // Step 3: Setup proving key
    print!("  [3/4] Setup PK... ");
    let start = Instant::now();
    let pk = compact_std_lib::setup_pk(&relation, &vk);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    // Generate witness
    let mut rng = ChaCha8Rng::from_entropy();
    let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
    let instance = sha2::Sha256::digest(witness).into();
    
    // Step 4: Create proof (THIS IS WHERE GPU ACCELERATION HAPPENS)
    print!("  [4/4] Proving... ");
    let start = Instant::now();
    let proof = compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, OsRng,
    )?;
    let elapsed = start.elapsed();
    let proof_time = elapsed.as_secs_f64() * 1000.0;
    println!("{:>8.2}ms ⭐", proof_time);
    
    // Verify the proof
    print!("  [5/4] Verifying... ");
    let start = Instant::now();
    compact_std_lib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof
    )?;
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    println!("  ✓ Proof verified");
    println!("  📊 Proving time: {:.2}ms", proof_time);
    
    Ok(())
}

fn main() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║   PLONK Proof Generation Benchmark (Phase 3)              ║");
    println!("║   GPU Acceleration via ICICLE (K≥14)                      ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    
    #[cfg(feature = "gpu")]
    {
        use midnight_proofs::gpu::is_gpu_available;
        if is_gpu_available() {
            println!("\n✓ GPU backend: AVAILABLE (ICICLE CUDA)");
        } else {
            println!("\n⚠ GPU backend: NOT AVAILABLE (will use CPU fallback)");
        }
    }
    
    #[cfg(not(feature = "gpu"))]
    println!("\n• GPU backend: DISABLED (compiled without 'gpu' feature)");
    
    println!("\nNote: K<14 uses CPU (BLST), K≥14 uses GPU (ICICLE)\n");
    
    let test_sizes = vec![
        (10, "Small circuit (CPU baseline)"),
        (12, "Medium circuit (CPU)"),
        (14, "Large circuit (GPU threshold)"),
        (16, "Very large circuit (GPU)"),
        (18, "Huge circuit (GPU)"),
    ];
    
    for (k, description) in test_sizes {
        println!("\n{} - K={}", description, k);
        match benchmark_proof_generation(k) {
            Ok(_) => {},
            Err(e) => {
                eprintln!("  ✗ Error: {}", e);
                continue;
            }
        }
    }
    
    println!("\n╔════════════════════════════════════════════════════════════╗");
    println!("║   Benchmark Complete!                                      ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!("\nTo compare GPU vs CPU performance:");
    println!("  CPU only: cargo run --example proof_generation_benchmark --release");
    println!("  With GPU: cargo run --features gpu --example proof_generation_benchmark --release");
}
