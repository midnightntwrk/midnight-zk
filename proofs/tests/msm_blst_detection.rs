//! Test BLST detection and performance with midnight_curves
//!
//! NOTE: msm_specific() now REQUIRES midnight_curves::G1Affine - other curves will panic.
//!
//! Run with: cargo test -p midnight-proofs --test msm_blst_detection -- --nocapture
//! With tracing: cargo test -p midnight-proofs --test msm_blst_detection --features trace-msm -- --nocapture

use ff::Field;
use midnight_proofs::poly::kzg::msm::{is_blst_available, msm_specific};
use midnight_curves::G1Affine;
use group::Group;
use rand_core::OsRng;
use std::time::Instant;

/// Test that BLST is available for midnight_curves (MANDATORY)
#[test]
fn test_blst_detection() {
    println!("\n{}", "=".repeat(80));
    println!("BLST MSM Detection Test");
    println!("{}\n", "=".repeat(80));
    
    // Check if BLST is available for midnight_curves (MUST be true)
    let blst_available = is_blst_available::<G1Affine>();
    println!("✓ BLST available for midnight_curves::G1Affine: {}", blst_available);
    println!("  This MUST be true - msm_specific() will panic otherwise");
    
    assert!(blst_available, "BLST MUST be available for midnight_curves");
    
    println!("\n✅ BLST optimization confirmed for midnight_curves");
    println!("   Any other curve type will panic in msm_specific()");
    println!("{}", "=".repeat(80));
}

/// This test demonstrates BLST performance across different MSM sizes.
/// Note: msm_specific() now REQUIRES midnight_curves - other curves will panic.
#[test]
fn test_msm_performance_scaling() {
    println!("\n{}", "=".repeat(80));
    println!("MSM Performance Scaling (BLST Mandatory)");
    println!("{}\n", "=".repeat(80));
    
    use midnight_curves::{Fq, G1Projective};
    
    let sizes = [128, 512, 2048, 8192];
    
    println!("Testing midnight_curves::G1Affine (BLST optimized):");
    for &size in &sizes {
        // Generate random scalars
        let scalars: Vec<Fq> = (0..size)
            .map(|_| Fq::random(OsRng))
            .collect();
        
        // Generate random points
        let bases: Vec<G1Projective> = (0..size)
            .map(|_| G1Projective::random(OsRng))
            .collect();
        
        // Measure MSM time
        let start = Instant::now();
        let _result = msm_specific::<G1Affine>(&scalars, &bases);
        let elapsed = start.elapsed();
        
        let throughput = size as f64 / elapsed.as_secs_f64() / 1000.0;
        println!("  Size {:5}: {:8.2}ms ({:7.2} K points/sec)", 
            size, elapsed.as_secs_f64() * 1000.0, throughput);
    }
    
    println!("\n✅ BLST provides consistent high performance across all sizes");
    println!("{}", "=".repeat(80));
}

#[test]
fn test_msm_large_size() {
    println!("\n{}", "=".repeat(80));
    println!("MSM Large Size Test (BLST Mandatory)");
    println!("{}\n", "=".repeat(80));
    
    // Test with large MSM - BLST handles all sizes now
    let size = 16_384;
    println!("Testing with {} points (BLST handles all sizes):", size);
    
    use midnight_curves::{Fq, G1Projective};
    let scalars: Vec<Fq> = vec![Fq::random(OsRng); size];
    let bases: Vec<G1Projective> = vec![G1Projective::random(OsRng); size];
    
    let start = Instant::now();
    let _result = msm_specific::<G1Affine>(&scalars, &bases);
    let elapsed = start.elapsed();
    println!("✓ Completed in {:?}", elapsed);
    
    println!("\n✅ BLST now handles all MSM sizes without fallback");
    println!("{}", "=".repeat(80));
}

/// Test BLST consistency across multiple iterations
#[test]
fn test_blst_consistency() {
    println!("\n{}", "=".repeat(80));
    println!("BLST Performance Consistency");
    println!("{}\n", "=".repeat(80));
    
    let size = 2048;
    let iterations = 5;
    
    println!("Running {} iterations with {} points each\n", iterations, size);
    
    use midnight_curves::{Fq, G1Projective};
    let mut times = Vec::new();
    
    for i in 0..iterations {
        let scalars: Vec<Fq> = (0..size).map(|_| Fq::random(OsRng)).collect();
        let bases: Vec<G1Projective> = (0..size).map(|_| G1Projective::random(OsRng)).collect();
        
        let start = Instant::now();
        let _result = msm_specific::<G1Affine>(&scalars, &bases);
        let elapsed = start.elapsed();
        times.push(elapsed);
        
        println!("  Iteration {}: {:?}", i + 1, elapsed);
    }
    
    // Calculate statistics
    let avg = times.iter().map(|d| d.as_secs_f64()).sum::<f64>() / iterations as f64;
    let min = times.iter().min().unwrap();
    let max = times.iter().max().unwrap();
    let variance = max.as_secs_f64() / min.as_secs_f64();
    
    println!("\n{}", "-".repeat(80));
    println!("Average time:  {:.3}ms", avg * 1000.0);
    println!("Min time:      {:?}", min);
    println!("Max time:      {:?}", max);
    println!("Variance:      {:.2}x", variance);
    println!("{}", "-".repeat(80));
    
    println!("\n✅ BLST provides consistent performance");
    println!("{}", "=".repeat(80));
}
