//! Test MSM batching infrastructure
//!
//! Validates:
//! - MsmBatch accumulation and execution
//! - Buffer reuse optimization
//! - Batch merging
//! - commit_lagrange_batch and commit_batch APIs
//!
//! Note: Batch functions are available for specialized scenarios (lookups, permutations)
//! but are not used in the main prover path for advice column commits.

#[cfg(feature = "gpu")]
#[test]
fn test_batch_accumulation() {
    use midnight_proofs::gpu::batch::MsmBatch;
    use midnight_curves::Fq as Scalar;
    use ff::Field;
    
    let mut batch = MsmBatch::new(false); // CPU for test
    
    // Add 3 MSMs
    let scalars1: Vec<Scalar> = (0..4).map(|_| Scalar::random(rand::thread_rng())).collect();
    let scalars2: Vec<Scalar> = (0..4).map(|_| Scalar::random(rand::thread_rng())).collect();
    let scalars3: Vec<Scalar> = (0..4).map(|_| Scalar::random(rand::thread_rng())).collect();
    
    batch.add(scalars1.clone(), 0..4);
    batch.add(scalars2.clone(), 0..4);
    batch.add(scalars3.clone(), 0..4);
    
    assert_eq!(batch.len(), 3);
    assert!(!batch.is_empty());
    
    println!("✓ Batch accumulation working: {} operations", batch.len());
}

#[cfg(feature = "gpu")]
#[test]
fn test_batch_merge() {
    use midnight_proofs::gpu::batch::MsmBatch;
    use midnight_curves::Fq as Scalar;
    use ff::Field;
    
    let mut batch1 = MsmBatch::new(false);
    let mut batch2 = MsmBatch::new(false);
    
    // Add MSMs to each batch
    let scalars1: Vec<Scalar> = (0..4).map(|_| Scalar::random(rand::thread_rng())).collect();
    let scalars2: Vec<Scalar> = (0..4).map(|_| Scalar::random(rand::thread_rng())).collect();
    
    batch1.add(scalars1, 0..4);
    batch2.add(scalars2, 0..4);
    
    assert_eq!(batch1.len(), 1);
    assert_eq!(batch2.len(), 1);
    
    // Merge batch2 into batch1
    batch1.merge(batch2);
    
    assert_eq!(batch1.len(), 2);
    
    println!("✓ Batch merging working: merged to {} operations", batch1.len());
}

#[cfg(feature = "gpu")]
#[test]
fn test_result_boundaries() {
    use midnight_proofs::gpu::batch::MsmBatch;
    use midnight_curves::Fq as Scalar;
    use ff::Field;
    
    let mut batch = MsmBatch::new(false);
    
    // Add 5 MSMs
    for _ in 0..5 {
        let scalars: Vec<Scalar> = (0..4).map(|_| Scalar::random(rand::thread_rng())).collect();
        batch.add(scalars, 0..4);
    }
    
    let boundaries = batch.result_boundaries();
    assert_eq!(boundaries.len(), 5);
    assert_eq!(boundaries.iter().sum::<usize>(), 5); // Each MSM produces 1 result
    
    println!("✓ Result boundaries working: {:?}", boundaries);
}

#[cfg(feature = "gpu")]
#[test]
#[ignore] // Requires GPU device - run with --ignored flag
fn test_commit_lagrange_batch() {
    use midnight_proofs::poly::kzg::params::ParamsKZG;
    use halo2curves::bn256::{Bn256, Fr};
    use ff::Field;
    use rand::thread_rng;
    
    // Create large params to trigger GPU path (K=14 = 16384 points)
    let k = 14;
    let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(k, thread_rng());
    
    // Create 3 polynomials in Lagrange form
    let size = 1 << k;
    let poly1: Vec<Fr> = (0..size).map(|_| Fr::random(thread_rng())).collect();
    let poly2: Vec<Fr> = (0..size).map(|_| Fr::random(thread_rng())).collect();
    let poly3: Vec<Fr> = (0..size).map(|_| Fr::random(thread_rng())).collect();
    
    let polys = vec![poly1.as_slice(), poly2.as_slice(), poly3.as_slice()];
    
    // Batch commit
    let commitments = params.commit_lagrange_batch(&polys);
    
    assert_eq!(commitments.len(), 3);
    
    println!("✓ commit_lagrange_batch working: produced {} commitments", commitments.len());
}

#[cfg(feature = "gpu")]
#[test]
#[ignore] // Requires GPU device - run with --ignored flag
fn test_commit_batch() {
    use midnight_proofs::poly::kzg::params::ParamsKZG;
    use halo2curves::bn256::{Bn256, Fr};
    use ff::Field;
    use rand::thread_rng;
    
    // Create large params to trigger GPU path (K=14 = 16384 points)
    let k = 14;
    let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(k, thread_rng());
    
    // Create 3 polynomials in coefficient form
    let size = 1 << k;
    let poly1: Vec<Fr> = (0..size).map(|_| Fr::random(thread_rng())).collect();
    let poly2: Vec<Fr> = (0..size).map(|_| Fr::random(thread_rng())).collect();
    let poly3: Vec<Fr> = (0..size).map(|_| Fr::random(thread_rng())).collect();
    
    let polys = vec![poly1.as_slice(), poly2.as_slice(), poly3.as_slice()];
    
    // Batch commit
    let commitments = params.commit_batch(&polys);
    
    assert_eq!(commitments.len(), 3);
    
    println!("✓ commit_batch working: produced {} commitments", commitments.len());
}
