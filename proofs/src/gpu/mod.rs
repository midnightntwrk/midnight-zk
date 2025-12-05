//! GPU acceleration for midnight-zk proof generation
//!
//! This module provides GPU-accelerated implementations of computationally intensive
//! operations in the PLONK prover, specifically Multi-Scalar Multiplication (MSM).
//!
//! # Features
//!
//! Enable GPU support by compiling with the `gpu` feature:
//! ```toml
//! midnight-proofs = { version = "*", features = ["gpu"] }
//! ```
//!
//! # Backend Support
//!
//! Currently supports:
//! - **CUDA**: NVIDIA GPUs (requires ICICLE CUDA backend)
//! - **CPU**: Automatic fallback when GPU unavailable
//!
//! # Setup
//!
//! 1. Install ICICLE CUDA backend:
//!    ```bash
//!    wget https://github.com/ingonyama-zk/icicle/releases/download/v4.0.0/icicle_4_0_0-ubuntu22-cuda122.tar.gz
//!    sudo tar -xzf icicle_4_0_0-ubuntu22-cuda122.tar.gz -C /opt
//!    export ICICLE_BACKEND_INSTALL_DIR=/opt/icicle/lib/backend
//!    ```
//!
//! 2. The backend will be automatically loaded when the prover is initialized.
//!
//! # License
//!
//! ICICLE uses a free R&D license that connects to `license.icicle.ingonyama.com`.
//! For production deployments, contact sales@ingonyama.com for commercial licensing.
//!
//! # Example
//!
//! ```rust,no_run
//! use midnight_proofs::gpu::{GpuBackend, GpuConfig};
//!
//! // Initialize GPU backend with default config
//! let backend = GpuBackend::new(GpuConfig::default())?;
//!
//! // Backend will automatically select GPU or CPU based on availability
//! ```

pub mod backend;
pub mod batch;
pub mod config;
pub mod msm;
pub mod types;

pub use backend::{GpuBackend, GpuError};
pub use batch::MsmBatch;
pub use config::{DeviceType, GpuConfig};
pub use msm::{MsmBackend, MsmExecutor};
pub use types::TypeConverter;

/// Check if GPU support is compiled in
pub const GPU_SUPPORT: bool = cfg!(feature = "gpu");

/// Check if GPU is available at runtime
pub fn is_gpu_available() -> bool {
    #[cfg(feature = "gpu")]
    {
        backend::is_gpu_available()
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
    fn test_gpu_support() {
        // This test just verifies the module compiles
        assert_eq!(GPU_SUPPORT, cfg!(feature = "gpu"));
    }
}
