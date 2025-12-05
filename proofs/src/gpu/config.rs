//! GPU backend configuration

use std::path::PathBuf;

/// Device type for computation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceType {
    /// Automatically select best available device
    Auto,
    /// Force CUDA GPU
    Cuda,
    /// Force CPU
    Cpu,
}

impl DeviceType {
    /// Get the string representation of the device type
    pub fn as_str(&self) -> &'static str {
        match self {
            DeviceType::Auto => "Auto",
            DeviceType::Cuda => "CUDA",
            DeviceType::Cpu => "CPU",
        }
    }
}

impl std::fmt::Display for DeviceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Configuration for GPU backend
#[derive(Debug, Clone)]
pub struct GpuConfig {
    /// Path to ICICLE backend installation
    pub backend_path: PathBuf,
    
    /// Device type to use
    pub device_type: DeviceType,
    
    /// GPU device index (for multi-GPU systems)
    pub device_id: u32,
    
    /// Number of warmup iterations to run on initialization
    pub warmup_iterations: usize,
    
    /// Enable automatic CPU fallback on GPU errors
    pub enable_fallback: bool,
    
    /// Minimum problem size to use GPU (smaller problems use CPU)
    pub min_gpu_size: usize,
}

impl Default for GpuConfig {
    fn default() -> Self {
        Self {
            backend_path: std::env::var("ICICLE_BACKEND_INSTALL_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|_| PathBuf::from("/opt/icicle/lib/backend")),
            device_type: DeviceType::Auto,
            device_id: 0,
            warmup_iterations: 10,
            enable_fallback: false, // No automatic CPU fallback
            min_gpu_size: 16384, // Use GPU for K >= 14 (2^14 = 16384 points)
        }
    }
}

impl GpuConfig {
    /// Create a new GPU configuration
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Set the backend path
    pub fn with_backend_path(mut self, path: PathBuf) -> Self {
        self.backend_path = path;
        self
    }
    
    /// Set the device type
    pub fn with_device_type(mut self, device_type: DeviceType) -> Self {
        self.device_type = device_type;
        self
    }
    
    /// Set the device ID
    pub fn with_device_id(mut self, id: u32) -> Self {
        self.device_id = id;
        self
    }
    
    /// Set the number of warmup iterations
    pub fn with_warmup_iterations(mut self, iterations: usize) -> Self {
        self.warmup_iterations = iterations;
        self
    }
    
    /// Enable or disable CPU fallback
    pub fn with_fallback(mut self, enable: bool) -> Self {
        self.enable_fallback = enable;
        self
    }
    
    /// Set minimum problem size for GPU usage
    pub fn with_min_gpu_size(mut self, size: usize) -> Self {
        self.min_gpu_size = size;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = GpuConfig::default();
        assert_eq!(config.device_type, DeviceType::Auto);
        assert_eq!(config.device_id, 0);
        assert_eq!(config.warmup_iterations, 10);
        assert!(!config.enable_fallback); // Fallback disabled by default
        assert_eq!(config.min_gpu_size, 16384); // K >= 14
    }

    #[test]
    fn test_config_builder() {
        let config = GpuConfig::new()
            .with_device_type(DeviceType::Cuda)
            .with_device_id(1)
            .with_warmup_iterations(20)
            .with_fallback(false)
            .with_min_gpu_size(8192);
        
        assert_eq!(config.device_type, DeviceType::Cuda);
        assert_eq!(config.device_id, 1);
        assert_eq!(config.warmup_iterations, 20);
        assert!(!config.enable_fallback);
        assert_eq!(config.min_gpu_size, 8192);
    }

    #[test]
    fn test_device_type_display() {
        assert_eq!(DeviceType::Auto.to_string(), "Auto");
        assert_eq!(DeviceType::Cuda.to_string(), "CUDA");
        assert_eq!(DeviceType::Cpu.to_string(), "CPU");
    }
}
