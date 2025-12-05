//! MSM Batching for GPU acceleration
//!
//! Accumulate multiple MSMs and execute together to reduce GPU kernel launch overhead.
//! Useful for lookups, permutations, and multi-proof scenarios.
//! Not used in main prover path (advice columns use parallel individual commits).

use crate::gpu::msm::MsmError;
use crate::gpu::TypeConverter;
use midnight_curves::{Fq as Scalar, G1Projective};
use std::ops::Range;

#[cfg(feature = "gpu")]
use icicle_runtime::memory::DeviceVec;
#[cfg(feature = "gpu")]
use icicle_bls12_381::curve::G1Affine as IcicleG1Affine;

/// Batch of MSM operations to execute together
/// 
/// Accumulates multiple MSMs and executes them using shared GPU context.
/// Reduces kernel launch overhead by reusing device buffers.
#[derive(Debug)]
pub struct MsmBatch {
    /// Accumulated scalars from all MSMs
    scalars: Vec<Scalar>,
    
    /// Range in bases for each MSM (all use same base set)
    /// Each entry is (scalar_start, scalar_len, base_start, base_len)
    operations: Vec<(usize, usize, usize, usize)>,
    
    /// Whether to use GPU for execution
    use_gpu: bool,
}

impl MsmBatch {
    /// Create a new empty batch
    pub fn new(use_gpu: bool) -> Self {
        Self {
            scalars: Vec::new(),
            operations: Vec::new(),
            use_gpu,
        }
    }
    
    /// Add an MSM operation to the batch
    /// 
    /// # Arguments
    /// * `scalars` - Scalars for this MSM
    /// * `base_range` - Range in the global base array to use
    pub fn add(&mut self, scalars: Vec<Scalar>, base_range: Range<usize>) {
        let scalar_start = self.scalars.len();
        let scalar_len = scalars.len();
        
        assert_eq!(
            scalar_len,
            base_range.len(),
            "Scalar and base count must match"
        );
        
        self.scalars.extend(scalars);
        self.operations.push((
            scalar_start,
            scalar_len,
            base_range.start,
            base_range.len(),
        ));
    }
    
    /// Get the number of MSMs in this batch
    pub fn len(&self) -> usize {
        self.operations.len()
    }
    
    /// Check if batch is empty
    pub fn is_empty(&self) -> bool {
        self.operations.is_empty()
    }
    
    /// Merge another batch into this one
    /// 
    /// Useful for accumulating MSMs across multiple proof generation operations
    pub fn merge(&mut self, other: MsmBatch) {
        let scalar_offset = self.scalars.len();
        
        // Extend scalars
        self.scalars.extend(other.scalars);
        
        // Adjust operation indices and add to this batch
        for (scalar_start, scalar_len, base_start, base_len) in other.operations {
            self.operations.push((
                scalar_start + scalar_offset,
                scalar_len,
                base_start,
                base_len,
            ));
        }
    }
    
    /// Get result boundaries for distributing batched results
    /// 
    /// Returns the number of results expected for each operation
    pub fn result_boundaries(&self) -> Vec<usize> {
        vec![1; self.operations.len()] // Each MSM produces 1 result
    }
    
    /// Execute all batched MSMs using GPU with pre-uploaded bases
    /// 
    /// Returns results in the same order MSMs were added
    #[cfg(feature = "gpu")]
    pub fn execute_all_gpu(
        &self,
        device_bases: &DeviceVec<IcicleG1Affine>,
    ) -> Result<Vec<G1Projective>, MsmError> {
        use icicle_core::msm::{msm, MSMConfig};
        use icicle_core::ecntt::Projective;
        use icicle_runtime::memory::{DeviceVec, HostSlice, HostOrDeviceSlice};
        use icicle_bls12_381::curve::G1Projective as IcicleG1Projective;
        use icicle_runtime::{Device, set_device};
        use group::Group;
        
        if self.operations.is_empty() {
            return Ok(Vec::new());
        }
        
        #[cfg(feature = "trace-msm")]
        eprintln!("[MSM-BATCH] Executing {} MSMs in single GPU call", self.operations.len());
        
        #[cfg(feature = "trace-msm")]
        let start = std::time::Instant::now();
        
        // Ensure correct GPU device
        let device = Device::new("CUDA", 0);
        set_device(&device).map_err(|e| 
            MsmError::GpuError(crate::gpu::GpuError::OperationFailed(format!("Device error: {:?}", e)))
        )?;
        
        let mut results = Vec::with_capacity(self.operations.len());
        
        // Buffer reuse optimization: Pre-allocate device buffers once, reuse for all MSMs
        let mut device_result = DeviceVec::<IcicleG1Projective>::device_malloc(1)
            .map_err(|e| MsmError::GpuError(
                crate::gpu::GpuError::OperationFailed(format!("Failed to allocate device buffer: {:?}", e))
            ))?;
        
        // Pre-allocate host result buffer (reused for all MSMs)
        let mut host_result = vec![IcicleG1Projective::zero(); 1];
        
        #[cfg(feature = "trace-msm")]
        eprintln!("   [MSM-BATCH] Executing {} MSMs with buffer reuse", self.operations.len());
        
        // Execute each MSM with buffer reuse
        for (idx, (scalar_start, scalar_len, base_start, base_len)) in self.operations.iter().enumerate() {
            let scalars = &self.scalars[*scalar_start..(*scalar_start + *scalar_len)];
            
            // Convert scalars to ICICLE format
            let icicle_scalars = TypeConverter::scalar_slice_to_icicle_vec(scalars);
            
            // Use slice of pre-uploaded bases
            let bases_slice = &device_bases[*base_start..(*base_start + *base_len)];
            
            // Execute MSM (reusing device_result buffer - no reallocation!)
            let cfg = MSMConfig::default();
            msm(
                HostSlice::from_slice(&icicle_scalars),
                bases_slice,
                &cfg,
                &mut device_result[..]
            ).map_err(|e| MsmError::GpuError(
                crate::gpu::GpuError::OperationFailed(format!("MSM {} failed: {:?}", idx, e))
            ))?;
            
            // Copy result back (reusing host_result buffer)
            device_result.copy_to_host(HostSlice::from_mut_slice(&mut host_result))
                .map_err(|e| MsmError::GpuError(
                    crate::gpu::GpuError::OperationFailed(format!("Copy {} failed: {:?}", idx, e))
                ))?;
            
            results.push(TypeConverter::icicle_to_g1_projective(&host_result[0]));
        }
        
        #[cfg(feature = "trace-msm")]
        eprintln!("[MSM-BATCH] Completed {} MSMs in {:?} (buffer reuse enabled)", self.operations.len(), start.elapsed());
        
        Ok(results)
    }
    
    /// Execute all batched MSMs using CPU
    pub fn execute_all_cpu(&self, bases: &[G1Projective]) -> Result<Vec<G1Projective>, MsmError> {
        use group::Group;
        
        if self.operations.is_empty() {
            return Ok(Vec::new());
        }
        
        let mut results = Vec::with_capacity(self.operations.len());
        
        for (scalar_start, scalar_len, base_start, base_len) in &self.operations {
            let scalars = &self.scalars[*scalar_start..(*scalar_start + *scalar_len)];
            let operation_bases = &bases[*base_start..(*base_start + *base_len)];
            
            if scalars.is_empty() {
                results.push(G1Projective::identity());
            } else {
                results.push(G1Projective::multi_exp(operation_bases, scalars));
            }
        }
        
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_batch_creation() {
        let mut batch = MsmBatch::new(false);
        assert_eq!(batch.len(), 0);
        assert!(batch.is_empty());
    }
    
    #[test]
    fn test_batch_add() {
        use ff::Field;
        let mut batch = MsmBatch::new(false);
        
        batch.add(vec![Scalar::ONE; 10], 0..10);
        batch.add(vec![Scalar::ONE; 20], 10..30);
        
        assert_eq!(batch.len(), 2);
        assert_eq!(batch.scalars.len(), 30);
    }
    
    #[test]
    #[should_panic(expected = "Scalar and base count must match")]
    fn test_batch_add_mismatch() {
        use ff::Field;
        let mut batch = MsmBatch::new(false);
        batch.add(vec![Scalar::ONE; 10], 0..20); // Mismatch!
    }
}
