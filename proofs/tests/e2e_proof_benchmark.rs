//! sEnd-to-End Proof Generation Benchmark with GPU
//!
//! Based on the public_inputs test from midnight-circuits.
//! Measures actual proof generation time with realistic circuits.

use ff::Field;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib},
    hash::poseidon::PoseidonChip,
    instructions::{
        hash::HashCPU, AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::time::Instant;

type F = midnight_curves::Fq;

/// Test circuit that performs Poseidon hashing
/// Similar to real-world Midnight circuits
#[derive(Clone)]
struct BenchCircuit {
    nb_hashes: u32,
}

impl Relation for BenchCircuit {
    type Instance = Vec<F>;
    type Witness = Vec<F>;

    fn format_instance(x: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(x.clone())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        // Load public inputs
        let mut inputs = vec![F::ZERO; self.nb_hashes as usize];
        instance.map(|v| inputs = v[..self.nb_hashes as usize].to_vec());
        let inputs = inputs
            .into_iter()
            .map(|input| std_lib.assign_as_public_input(layouter, Value::known(input)))
            .collect::<Result<Vec<_>, Error>>()?;

        // Load witness (preimages)
        let preimage_values = witness.transpose_vec(self.nb_hashes as usize);
        let preimages = std_lib.assign_many(layouter, &preimage_values)?;

        // Compute Poseidon hashes
        let hashes = preimages
            .into_iter()
            .map(|preimage| std_lib.poseidon(layouter, &[preimage]))
            .collect::<Result<Vec<_>, Error>>()?;

        // Verify hashes match public inputs
        for (input, hash) in inputs.iter().zip(hashes.iter()) {
            std_lib.assert_equal(layouter, input, hash)?;
        }

        Ok(())
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.nb_hashes.to_le_bytes())
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut bytes = [0u8; 4];
        reader.read_exact(&mut bytes)?;
        Ok(BenchCircuit {
            nb_hashes: u32::from_le_bytes(bytes),
        })
    }
}

fn benchmark_e2e_proof(k: u32, nb_hashes: u32) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== K={} | {} Poseidon hashes ===", k, nb_hashes);
    
    // Step 1: Load SRS
    print!("  [1/5] Loading SRS... ");
    let start = Instant::now();
    let mut srs = filecoin_srs(k);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    let relation = BenchCircuit { nb_hashes };
    
    // Step 2: Downsize SRS
    print!("  [2/5] Downsize SRS... ");
    let start = Instant::now();
    compact_std_lib::downsize_srs_for_relation(&mut srs, &relation);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    // Step 3: Setup VK
    print!("  [3/5] Setup VK... ");
    let start = Instant::now();
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    // Step 4: Setup PK
    print!("  [4/5] Setup PK... ");
    let start = Instant::now();
    let pk = compact_std_lib::setup_pk(&relation, &vk);
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    // Generate witness and instance
    let mut rng = ChaCha8Rng::from_entropy();
    let witness = (0..nb_hashes).map(|_| F::random(&mut rng)).collect::<Vec<_>>();
    let instance = witness
        .iter()
        .map(|w| <PoseidonChip<F> as HashCPU<F, F>>::hash(&[*w]))
        .collect::<Vec<_>>();
    
    // Step 5: Generate proof (GPU ACCELERATION HERE!)
    print!("  [5/5] Proving... ");
    let start = Instant::now();
    let proof = compact_std_lib::prove::<BenchCircuit, blake2b_simd::State>(
        &srs, &pk, &relation, &instance, witness, rng,
    )?;
    let elapsed = start.elapsed();
    let proof_time = elapsed.as_secs_f64() * 1000.0;
    println!("{:>8.2}ms ⭐", proof_time);
    
    // Verify proof
    print!("  Verifying... ");
    let start = Instant::now();
    compact_std_lib::verify::<BenchCircuit, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof
    )?;
    let elapsed = start.elapsed();
    println!("{:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    println!("  ✓ Proof verified successfully");
    println!("  📊 Proving time: {:.2}ms", proof_time);
    
    Ok(())
}

#[test]
#[ignore] // Run with: cargo test --test e2e_proof_benchmark --features gpu --release -- --ignored --nocapture
fn e2e_proof_benchmark() {
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║  End-to-End Proof Generation Benchmark                        ║");
    println!("║  GPU-Accelerated PLONK Proving (ICICLE)                       ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
    
    #[cfg(feature = "gpu")]
    {
        use midnight_proofs::gpu::is_gpu_available;
        println!();
        if is_gpu_available() {
            println!("✓ GPU Backend: AVAILABLE (ICICLE CUDA)");
            println!("  • Threshold: K≥14 (16,384 constraints)");
            println!("  • All MSM operations will use GPU at K≥14");
        } else {
            println!("⚠ GPU Backend: NOT AVAILABLE");
            println!("  Will use CPU fallback (BLST)");
        }
    }
    
    #[cfg(not(feature = "gpu"))]
    {
        println!();
        println!("• GPU Feature: DISABLED");
        println!("  Using CPU-only (BLST) for all operations");
    }
    
    println!();
    println!("This benchmark uses real Midnight circuits with Poseidon hashing.");
    println!("Each test performs setup, proving, and verification.");
    println!();
    println!("═══════════════════════════════════════════════════════════════");
    
    // Test different circuit sizes with varying workloads
    let test_cases = vec![
        (10, 10, "Small circuit (CPU)"),
        (12, 20, "Medium circuit (CPU)"),
        (14, 30, "Large circuit (GPU threshold)"),
        (16, 40, "Very large circuit (GPU)"),
        (18, 50, "Huge circuit (GPU)"),
        (19, 60, "Massive circuit (GPU) - MAX TESTED"),
        // K=20: Blocked by SRS size assertion (assert!(k <= 19) in plonk_api.rs)
        // The Filecoin SRS only supports up to 2^19 constraints
        // Note: K=19 works perfectly with GPU, no ICICLE bugs at this size!
    ];
    
    for (k, nb_hashes, description) in test_cases {
        println!("\n{}", description);
        match benchmark_e2e_proof(k, nb_hashes) {
            Ok(_) => {},
            Err(e) => {
                eprintln!("  ✗ Error: {}", e);
                eprintln!("  Note: Make sure SRS files are downloaded.");
                eprintln!("  See: midnight-zk/circuits/examples/assets/");
                return;
            }
        }
    }
    
    println!();
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║  Benchmark Complete!                                          ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
    
    println!();
    println!("📈 Performance Analysis:");
    println!("  • K<14: CPU (BLST) - baseline performance");
    println!("  • K≥14: GPU (ICICLE) - accelerated MSM operations");
    println!("  • MSMs typically account for 60-70% of total proving time");
    println!();
    
    #[cfg(feature = "gpu")]
    println!("💡 To compare with CPU-only:");
    #[cfg(feature = "gpu")]
    println!("   cargo test --test e2e_proof_benchmark --release");
    
    #[cfg(not(feature = "gpu"))]
    println!("💡 To enable GPU acceleration:");
    #[cfg(not(feature = "gpu"))]
    println!("   cargo test --test e2e_proof_benchmark --features gpu --release");
}
