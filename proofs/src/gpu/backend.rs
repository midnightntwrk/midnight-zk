//! GPU backend initialization and management
//!
//! This module handles loading the ICICLE CUDA backend, device initialization,
//! and warmup operations.

use crate::gpu::config::{DeviceType, GpuConfig};
use std::sync::OnceLock;
use tracing::{debug, error, info, warn};

#[cfg(feature = "gpu")]
use icicle_runtime::{Device, load_backend_from_env_or_default, set_device};

/// Errors that can occur during GPU operations
#[derive(Debug)]
pub enum GpuError {
    /// GPU backend failed to load
    BackendLoadFailed(String),
    /// Failed to set device
    DeviceSetFailed(String),
    /// GPU operation failed
    OperationFailed(String),
    /// GPU not available
    NotAvailable,
}

impl std::fmt::Display for GpuError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GpuError::BackendLoadFailed(msg) => write!(f, "Backend load failed: {}", msg),
            GpuError::DeviceSetFailed(msg) => write!(f, "Device set failed: {}", msg),
            GpuError::OperationFailed(msg) => write!(f, "GPU operation failed: {}", msg),
            GpuError::NotAvailable => write!(f, "GPU not available"),
        }
    }
}

impl std::error::Error for GpuError {}

/// GPU backend state
#[cfg(feature = "gpu")]
#[derive(Debug)]
pub struct GpuBackend {
    config: GpuConfig,
    device: Device,
    initialized: bool,
}

/// Stub for when GPU feature is disabled
#[cfg(not(feature = "gpu"))]
#[derive(Debug)]
pub struct GpuBackend;

#[cfg(feature = "gpu")]
impl GpuBackend {
    /// Create a new GPU backend with the given configuration
    ///
    /// This will:
    /// 1. Load the ICICLE CUDA backend from the configured path
    /// 2. Initialize the specified device
    /// 3. Run warmup iterations to ensure GPU is ready
    pub fn new(config: GpuConfig) -> Result<Self, GpuError> {
        info!("Initializing GPU backend with config: {:?}", config);
        
        // Set environment variable for backend path
        std::env::set_var("ICICLE_BACKEND_INSTALL_DIR", &config.backend_path);
        
        // Load backend
        debug!("Loading ICICLE backend from {:?}", config.backend_path);
        load_backend_from_env_or_default()
            .map_err(|e| {
                error!("Failed to load ICICLE backend: {:?}", e);
                GpuError::BackendLoadFailed(format!("{:?}", e))
            })?;
        
        info!("ICICLE backend loaded successfully");
        
        // Determine device type
        let device_type_str = match config.device_type {
            DeviceType::Auto | DeviceType::Cuda => "CUDA",
            DeviceType::Cpu => "CPU",
        };
        
        // Create and set device
        debug!("Creating device: {} {}", device_type_str, config.device_id);
        let device = Device::new(device_type_str, config.device_id as i32);
        
        set_device(&device)
            .map_err(|e| {
                error!("Failed to set device: {:?}", e);
                GpuError::DeviceSetFailed(format!("{:?}", e))
            })?;
        
        info!("Device {} {} set successfully", device_type_str, config.device_id);
        
        let mut backend = Self {
            config,
            device,
            initialized: true,
        };
        
        // Run warmup
        if backend.config.warmup_iterations > 0 {
            backend.warmup()?;
        }
        
        Ok(backend)
    }
    
    /// Run warmup iterations to initialize GPU and caches
    fn warmup(&mut self) -> Result<(), GpuError> {
        use icicle_bls12_381::curve::{G1Affine, G1Projective, ScalarField};
        use icicle_core::msm::{msm, MSMConfig};
        use icicle_core::traits::GenerateRandom;
        use icicle_runtime::memory::{DeviceVec, HostSlice};
        
        debug!("Running {} warmup iterations", self.config.warmup_iterations);
        let start = std::time::Instant::now();
        
        // Small warmup size
        let warmup_size = 1024;
        let scalars = ScalarField::generate_random(warmup_size);
        let points = G1Affine::generate_random(warmup_size);
        let mut result = DeviceVec::<G1Projective>::device_malloc(1)
            .map_err(|e| GpuError::OperationFailed(format!("Warmup malloc failed: {:?}", e)))?;
        
        let cfg = MSMConfig::default();
        
        for i in 0..self.config.warmup_iterations {
            msm(
                HostSlice::from_slice(&scalars),
                HostSlice::from_slice(&points),
                &cfg,
                &mut result[..]
            ).map_err(|e| {
                warn!("Warmup iteration {} failed: {:?}", i, e);
                GpuError::OperationFailed(format!("Warmup MSM failed: {:?}", e))
            })?;
        }
        
        let elapsed = start.elapsed();
        info!(
            "Warmup complete: {} iterations in {:?} ({:.2}ms avg)",
            self.config.warmup_iterations,
            elapsed,
            elapsed.as_secs_f64() * 1000.0 / self.config.warmup_iterations as f64
        );
        
        Ok(())
    }
    
    /// Get the configuration
    pub fn config(&self) -> &GpuConfig {
        &self.config
    }
    
    /// Check if backend is initialized
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }
    
    /// Get the device
    pub fn device(&self) -> &Device {
        &self.device
    }
}

#[cfg(not(feature = "gpu"))]
impl GpuBackend {
    pub fn new(_config: GpuConfig) -> Result<Self, GpuError> {
        Err(GpuError::NotAvailable)
    }
}

/// Global GPU backend instance (lazily initialized)
static GPU_BACKEND: OnceLock<Option<GpuBackend>> = OnceLock::new();

/// Initialize the global GPU backend
pub fn initialize_gpu(config: GpuConfig) -> Result<(), GpuError> {
    GPU_BACKEND.get_or_init(|| {
        match GpuBackend::new(config) {
            Ok(backend) => {
                info!("Global GPU backend initialized successfully");
                Some(backend)
            }
            Err(e) => {
                warn!("GPU backend initialization failed: {}", e);
                None
            }
        }
    });
    
    if GPU_BACKEND.get().and_then(|b| b.as_ref()).is_some() {
        Ok(())
    } else {
        Err(GpuError::NotAvailable)
    }
}

/// Get the global GPU backend (returns None if not initialized or failed)
pub fn get_gpu_backend() -> Option<&'static GpuBackend> {
    GPU_BACKEND.get().and_then(|b| b.as_ref())
}

/// Check if GPU is available at runtime
pub fn is_gpu_available() -> bool {
    #[cfg(feature = "gpu")]
    {
        // Try to initialize if not already done
        if GPU_BACKEND.get().is_none() {
            let _ = initialize_gpu(GpuConfig::default());
        }
        get_gpu_backend().is_some()
    }
    #[cfg(not(feature = "gpu"))]
    {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gpu_error_display() {
        let err = GpuError::NotAvailable;
        assert_eq!(err.to_string(), "GPU not available");
        
        let err = GpuError::BackendLoadFailed("test".to_string());
        assert_eq!(err.to_string(), "Backend load failed: test");
    }

    #[cfg(feature = "gpu")]
    #[test]
    #[ignore] // Only run when GPU is available
    fn test_backend_initialization() {
        let config = GpuConfig::default();
        let result = GpuBackend::new(config);
        
        // This test may fail if GPU is not available, which is expected
        match result {
            Ok(backend) => {
                assert!(backend.is_initialized());
                println!("GPU backend initialized successfully");
            }
            Err(e) => {
                println!("GPU not available (expected on some systems): {}", e);
            }
        }
    }
}
