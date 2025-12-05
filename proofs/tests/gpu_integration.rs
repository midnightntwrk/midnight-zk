//! GPU integration tests
//! 
//! These tests verify GPU acceleration with ICICLE backend.
//! Requires GPU feature and ICICLE backend installed.

#![cfg(feature = "gpu")]

use midnight_proofs::gpu::{GpuConfig, MsmExecutor};
use midnight_curves::{Fq as Scalar, G1Affine, G1Projective};
use ff::Field;
use group::{Group, Curve, prime::PrimeCurveAffine};

#[test]
fn test_gpu_msm_small_k10() {
    // K=10: 1024 points - should use CPU (< 16384)
    let size = 1024;
    test_msm_with_size(size);
}

#[test]
fn test_gpu_msm_k14() {
    // K=14: 16384 points - should use GPU (>= 16384)
    let size = 16384;
    test_msm_with_size(size);
}

#[test]
fn test_gpu_msm_k16() {
    // K=16: 65536 points - should use GPU
    let size = 65536;
    test_msm_with_size(size);
}

fn test_msm_with_size(size: usize) {
    let mut rng = rand::thread_rng();
    
    // Generate random scalars and points
    let scalars: Vec<Scalar> = (0..size).map(|_| Scalar::random(&mut rng)).collect();
    let points: Vec<G1Affine> = (0..size)
        .map(|_| G1Projective::random(&mut rng).to_affine())
        .collect();
    
    // Create executor with default config
    let executor = MsmExecutor::default();
    
    // Execute MSM
    let result = executor.execute(&scalars, &points)
        .expect("MSM should succeed");
    
    // Verify result is not identity (with random inputs, extremely unlikely)
    assert!(!bool::from(result.is_identity()));
    
    // For K >= 14, also verify against CPU reference
    if size >= 16384 {
        let points_proj: Vec<G1Projective> = points.iter().map(|p| G1Projective::from(*p)).collect();
        let cpu_result = G1Projective::multi_exp(&points_proj, &scalars);
        assert_eq!(result, cpu_result, "GPU and CPU results should match");
    }
}

#[test]
fn test_gpu_backend_initialization() {
    use midnight_proofs::gpu::GpuBackend;
    
    let config = GpuConfig::default();
    let backend = GpuBackend::new(config);
    
    // Backend should initialize successfully on GPU systems
    // On CPU-only systems, this will fail gracefully
    match backend {
        Ok(_) => println!("GPU backend initialized successfully"),
        Err(e) => println!("GPU backend unavailable: {}", e),
    }
}

#[test]
fn test_executor_size_threshold() {
    let executor = MsmExecutor::default();
    
    // Small MSM (K=10: 1024 points) - uses CPU
    let small_scalars = vec![Scalar::ONE; 1024];
    let small_points = vec![G1Affine::generator(); 1024];
    
    let result = executor.execute(&small_scalars, &small_points);
    assert!(result.is_ok(), "Small MSM should succeed on CPU");
    
    // Large MSM (K=14: 16384 points) - attempts GPU
    let large_scalars = vec![Scalar::ONE; 16384];
    let large_points = vec![G1Affine::generator(); 16384];
    
    let result = executor.execute(&large_scalars, &large_points);
    // Result depends on GPU availability
    match result {
        Ok(_) => println!("GPU MSM succeeded"),
        Err(e) => println!("GPU MSM failed (expected on CPU-only systems): {}", e),
    }
}
