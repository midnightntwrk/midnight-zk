//! Benchmark MSM operations via the PLONK KZG path
//! This tests the integration into poly/kzg/msm.rs

use midnight_proofs::poly::kzg::msm::{msm_specific, MSMKZG};
use midnight_proofs::utils::arithmetic::MSM;
use midnight_curves::{Fq as Scalar, G1Affine, G1Projective};
use rand::thread_rng;
use ff::Field;
use group::Group;
use std::time::Instant;

fn bench_msm_via_kzg(k: u32) {
    let size = 1 << k;
    let mut rng = thread_rng();
    
    // Generate random scalars and bases
    let scalars: Vec<Scalar> = (0..size)
        .map(|_| Scalar::random(&mut rng))
        .collect();
    
    let bases: Vec<G1Projective> = (0..size)
        .map(|_| G1Projective::random(&mut rng))
        .collect();
    
    println!("K={} ({:7} points): ", k, size);
    
    // Measure via direct msm_specific call (this is what's used internally)
    let start = Instant::now();
    let _result = msm_specific::<G1Affine>(&scalars, &bases);
    let elapsed = start.elapsed();
    
    println!("  {:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    
    // Also measure via MSMKZG interface (used in proof generation)
    let mut msm = MSMKZG::<midnight_curves::Bls12>::init();
    
    for (scalar, base) in scalars.iter().zip(bases.iter()) {
        msm.append_term(*scalar, *base);
    }
    
    let start = Instant::now();
    let _result2 = msm.eval();
    let elapsed = start.elapsed();
    
    println!("  (via MSMKZG): {:>8.2}ms", elapsed.as_secs_f64() * 1000.0);
    println!();
}

fn main() {
    println!("Benchmarking MSM through PLONK KZG interface");
    println!("(Tests actual GPU integration in Phase 2)\n");
    
    // CPU range (should use BLST)
    println!("CPU Path (K<14):");
    bench_msm_via_kzg(10); // 1,024
    bench_msm_via_kzg(12); // 4,096
    
    // GPU range (should use ICICLE)
    println!("GPU Path (K≥14):");
    bench_msm_via_kzg(14); // 16,384
    bench_msm_via_kzg(16); // 65,536
    bench_msm_via_kzg(18); // 262,144
    
    println!("If GPU speedup is visible at K≥14, integration successful!");
}
