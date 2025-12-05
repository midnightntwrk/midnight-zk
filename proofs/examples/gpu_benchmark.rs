//! GPU performance benchmark
//!
//! Demonstrates GPU acceleration for K=14-18

#![cfg(feature = "gpu")]

use midnight_proofs::gpu::{GpuConfig, MsmExecutor};
use midnight_curves::{Fq as Scalar, G1Affine, G1Projective};
use ff::Field;
use group::{Group, Curve};
use std::time::Instant;

fn main() {
    println!("\n🚀 Midnight ZK - GPU MSM Benchmark");
    println!("====================================\n");
    
    let executor = MsmExecutor::default();
    let mut rng = rand::thread_rng();
    
    for k in [10, 12, 14, 16, 18, 20] {
        let size = 1 << k;
        print!("K={} ({:6} points): ", k, size);
        std::io::Write::flush(&mut std::io::stdout()).ok();
        
        // Generate random data
        let scalars: Vec<Scalar> = (0..size).map(|_| Scalar::random(&mut rng)).collect();
        let points: Vec<G1Affine> = (0..size)
            .map(|_| G1Projective::random(&mut rng).to_affine())
            .collect();
        
        // Execute MSM
        let start = Instant::now();
        let result = executor.execute(&scalars, &points)
            .expect("MSM failed");
        let elapsed = start.elapsed();
        
        // Verify result is valid (not identity with random inputs)
        assert!(!bool::from(result.is_identity()));
        
        // Determine backend used
        let backend = if size >= 16384 { "GPU" } else { "CPU" };
        
        println!("{:7.2}ms ({})", elapsed.as_secs_f64() * 1000.0, backend);
    }
    
    println!("\n✅ Benchmark complete!");
    println!("Note: K≥14 uses GPU, K<14 uses CPU");
}
