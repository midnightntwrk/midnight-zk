//! Multi-Scalar Multiplication (MSM) implementations
//!
//! This module provides GPU-accelerated MSM with automatic CPU fallback.

use crate::gpu::{GpuBackend, GpuConfig, GpuError, TypeConverter};
use midnight_curves::{Fq as Scalar, G1Affine, G1Projective};
use group::Group; // For identity() method
use tracing::{debug, warn};

/// Trait for MSM backend implementations
pub trait MsmBackend {
    /// Compute MSM: sum(scalars[i] * points[i])
    fn compute_msm(
        &self,
        scalars: &[Scalar],
        points: &[G1Affine],
    ) -> Result<G1Projective, MsmError>;
}

/// Errors that can occur during MSM operations
#[derive(Debug)]
pub enum MsmError {
    /// GPU operation failed
    GpuError(GpuError),
    /// CPU fallback also failed
    CpuError(String),
    /// Invalid input
    InvalidInput(String),
}

impl std::fmt::Display for MsmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MsmError::GpuError(e) => write!(f, "GPU MSM error: {}", e),
            MsmError::CpuError(e) => write!(f, "CPU MSM error: {}", e),
            MsmError::InvalidInput(e) => write!(f, "Invalid MSM input: {}", e),
        }
    }
}

impl std::error::Error for MsmError {}

impl From<GpuError> for MsmError {
    fn from(e: GpuError) -> Self {
        MsmError::GpuError(e)
    }
}

/// GPU MSM backend using ICICLE
#[cfg(feature = "gpu")]
#[derive(Debug)]
pub struct GpuMsmBackend {
    pub(crate) backend: GpuBackend,
}

#[cfg(feature = "gpu")]
impl GpuMsmBackend {
    /// Create a new GPU MSM backend with the given configuration
    pub fn new(config: GpuConfig) -> Result<Self, GpuError> {
        let backend = GpuBackend::new(config)?;
        Ok(Self { backend })
    }
    
    fn compute_msm_internal(
        &self,
        scalars: &[Scalar],
        points: &[G1Affine],
    ) -> Result<G1Projective, MsmError> {
        use icicle_core::msm::{msm, MSMConfig};
        use icicle_core::ecntt::Projective; // For zero() method
        use icicle_runtime::memory::{DeviceVec, HostSlice};
        use icicle_bls12_381::curve::G1Projective as IcicleG1Projective;
        
        if scalars.len() != points.len() {
            return Err(MsmError::InvalidInput(format!(
                "Scalar and point count mismatch: {} vs {}",
                scalars.len(),
                points.len()
            )));
        }
        
        if scalars.is_empty() {
            return Ok(G1Projective::identity());
        }
        
        // Convert to ICICLE types - this allocates new memory
        let icicle_scalars = TypeConverter::scalar_slice_to_icicle_vec(scalars);
        let icicle_points = TypeConverter::g1_affine_slice_to_icicle_vec(points);
        
        // Allocate device result buffer
        let mut device_result = DeviceVec::<IcicleG1Projective>::device_malloc(1)
            .map_err(|e| MsmError::GpuError(GpuError::OperationFailed(format!("{:?}", e))))?;
        
        // Configure and execute MSM
        let cfg = MSMConfig::default();
        msm(
            HostSlice::from_slice(&icicle_scalars),
            HostSlice::from_slice(&icicle_points),
            &cfg,
            &mut device_result[..]
        ).map_err(|e| MsmError::GpuError(GpuError::OperationFailed(format!("{:?}", e))))?;
        
        // Copy result back to host
        let mut host_result = vec![IcicleG1Projective::zero(); 1];
        device_result.copy_to_host(HostSlice::from_mut_slice(&mut host_result))
            .map_err(|e| MsmError::GpuError(GpuError::OperationFailed(format!("{:?}", e))))?;
        
        // Convert back to midnight types
        Ok(TypeConverter::icicle_to_g1_projective(&host_result[0]))
    }
}

#[cfg(feature = "gpu")]
impl MsmBackend for GpuMsmBackend {
    fn compute_msm(
        &self,
        scalars: &[Scalar],
        points: &[G1Affine],
    ) -> Result<G1Projective, MsmError> {
        self.compute_msm_internal(scalars, points)
    }
}

/// CPU MSM backend (fallback)
#[derive(Debug)]
pub struct CpuMsmBackend;

impl MsmBackend for CpuMsmBackend {
    fn compute_msm(
        &self,
        scalars: &[Scalar],
        points: &[G1Affine],
    ) -> Result<G1Projective, MsmError> {
        if scalars.len() != points.len() {
            return Err(MsmError::InvalidInput(format!(
                "Scalar and point count mismatch: {} vs {}",
                scalars.len(),
                points.len()
            )));
        }
        
        if scalars.is_empty() {
            return Ok(G1Projective::identity());
        }
        
        // Convert affine to projective for multi_exp
        let points_proj: Vec<G1Projective> = points.iter().map(|p| G1Projective::from(*p)).collect();
        Ok(G1Projective::multi_exp(&points_proj, scalars))
    }
}

/// MSM executor that automatically selects GPU or CPU backend
#[derive(Debug)]
pub struct MsmExecutor {
    #[cfg(feature = "gpu")]
    gpu_backend: Option<GpuMsmBackend>,
    cpu_backend: CpuMsmBackend,
    config: GpuConfig,
}

impl MsmExecutor {
    /// Create a new MSM executor with the given configuration
    pub fn new(config: GpuConfig) -> Self {
        #[cfg(feature = "gpu")]
        let gpu_backend = match GpuMsmBackend::new(config.clone()) {
            Ok(backend) => {
                debug!("GPU MSM backend initialized");
                Some(backend)
            }
            Err(e) => {
                warn!("GPU MSM backend initialization failed: {}, using CPU fallback", e);
                None
            }
        };
        
        Self {
            #[cfg(feature = "gpu")]
            gpu_backend,
            cpu_backend: CpuMsmBackend,
            config,
        }
    }
    
    /// Execute MSM with automatic backend selection based on size
    /// 
    /// For K >= 14 (16384+ points): Use GPU
    /// For K < 14: Use CPU
    pub fn execute(
        &self,
        scalars: &[Scalar],
        points: &[G1Affine],
    ) -> Result<G1Projective, MsmError> {
        if self.should_use_gpu(scalars.len()) {
            #[cfg(feature = "gpu")]
            if let Some(gpu) = &self.gpu_backend {
                debug!("Using GPU for MSM with {} points (K >= 14)", scalars.len());
                return gpu.compute_msm(scalars, points);
            }
            
            #[cfg(not(feature = "gpu"))]
            {
                return Err(MsmError::InvalidInput(
                    "GPU requested but feature not enabled".to_string()
                ));
            }
        }
        
        debug!("Using CPU for MSM with {} points (K < 14)", scalars.len());
        self.cpu_backend.compute_msm(scalars, points)
    }
    
    /// Execute MSM using pre-uploaded GPU bases (zero-copy optimization)
    /// 
    /// Eliminates per-call conversion and upload overhead by using bases
    /// cached in GPU memory. Primary optimization for GPU-accelerated commitments.
    #[cfg(feature = "gpu")]
    pub fn execute_with_device_bases(
        &self,
        scalars: &[Scalar],
        device_bases: &icicle_runtime::memory::DeviceVec<icicle_bls12_381::curve::G1Affine>,
    ) -> Result<G1Projective, MsmError> {
        use icicle_core::msm::{msm, MSMConfig};
        use icicle_core::ecntt::Projective; // For zero() method
        use icicle_runtime::memory::{DeviceVec, HostSlice, HostOrDeviceSlice};
        use icicle_bls12_381::curve::G1Projective as IcicleG1Projective;
        
        if scalars.is_empty() {
            return Ok(G1Projective::identity());
        }
        
        // CRITICAL: Must set device context in multi-threaded environment
        // Cached GPU bases require active device context to access memory
        // Use backend's cached device to avoid creating new device (which triggers backend reload)
        use icicle_runtime::set_device;
        if let Some(ref gpu_backend) = self.gpu_backend {
            set_device(gpu_backend.backend.device())
                .map_err(|e| MsmError::GpuError(GpuError::DeviceSetFailed(format!("{:?}", e))))?;
        } else {
            return Err(MsmError::GpuError(GpuError::NotAvailable));
        }
        
        if scalars.len() > device_bases.len() {
            return Err(MsmError::InvalidInput(format!(
                "More scalars ({}) than available bases ({})",
                scalars.len(),
                device_bases.len()
            )));
        }
        
        #[cfg(feature = "trace-msm")]
        eprintln!("   [GPU] Using pre-uploaded bases (zero-copy MSM) - {} points", scalars.len());
        
        // Convert scalars to ICICLE format (only conversion, no bases conversion!)
        let icicle_scalars = TypeConverter::scalar_slice_to_icicle_vec(scalars);
        
        // Allocate device result buffer
        let mut device_result = DeviceVec::<IcicleG1Projective>::device_malloc(1)
            .map_err(|e| MsmError::GpuError(GpuError::OperationFailed(format!("Device malloc failed: {:?}", e))))?;
        
        // Execute MSM directly on device bases (no upload!)
        let cfg = MSMConfig::default();
        
        #[cfg(feature = "trace-msm")]
        eprintln!("   [GPU] Calling ICICLE msm() with {} scalars, slice range 0..{}", icicle_scalars.len(), scalars.len());
        
        msm(
            HostSlice::from_slice(&icicle_scalars),
            &device_bases[..scalars.len()],  // Use slice of pre-uploaded bases
            &cfg,
            &mut device_result[..]
        ).map_err(|e| MsmError::GpuError(GpuError::OperationFailed(format!("MSM operation failed: {:?}", e))))?;
        
        // Copy result back to host
        let mut host_result = vec![IcicleG1Projective::zero(); 1];
        device_result.copy_to_host(HostSlice::from_mut_slice(&mut host_result))
            .map_err(|e| MsmError::GpuError(GpuError::OperationFailed(format!("Copy to host failed: {:?}", e))))?;
        
        // Convert back to midnight types
        Ok(TypeConverter::icicle_to_g1_projective(&host_result[0]))
    }
    
    /// Determine if GPU should be used for the given problem size
    fn should_use_gpu(&self, size: usize) -> bool {
        #[cfg(feature = "gpu")]
        {
            self.gpu_backend.is_some() && size >= self.config.min_gpu_size
        }
        #[cfg(not(feature = "gpu"))]
        {
            let _ = size; // Suppress unused warning
            false
        }
    }
}

impl Default for MsmExecutor {
    fn default() -> Self {
        Self::new(GpuConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_msm_empty() {
        let backend = CpuMsmBackend;
        let result = backend.compute_msm(&[], &[]).unwrap();
        assert_eq!(result, G1Projective::identity());
    }

    #[test]
    fn test_cpu_msm_size_mismatch() {
        use ff::Field;
        let backend = CpuMsmBackend;
        let scalars = vec![Scalar::ONE];
        let points = vec![];
        let result = backend.compute_msm(&scalars, &points);
        assert!(matches!(result, Err(MsmError::InvalidInput(_))));
    }

    #[test]
    fn test_msm_executor_default() {
        let executor = MsmExecutor::default();
        // Just verify it constructs without panicking
        let _ = executor.should_use_gpu(1000);
    }
}
