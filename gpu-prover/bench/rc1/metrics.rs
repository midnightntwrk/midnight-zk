#[derive(Default)]
pub struct Metrics {
    pub msm: u64,
    pub ntt: u64,
    pub quotient: u64,
    pub device_errors: u64,
    pub fallbacks: u64,
    pub declines: Vec<(&'static str, &'static str, u64)>,
    pub hook_declines: Vec<(&'static str, &'static str, u64)>,
    pub h2d_copies: u64,
    pub h2d_bytes: u64,
    pub d2h_copies: u64,
    pub d2h_bytes: u64,
    pub msm_d2h_copies: u64,
    pub msm_d2h_bytes: u64,
    pub stage: [u64; 8],
    pub peak_bytes: u64,
}

#[cfg(feature = "rc1-bench-cuda")]
pub mod device {
    use midnight_curves::Bls12;
    use midnight_gpu as gpu;
    use midnight_proofs::{
        gpu::{self as hooks, adapter},
        poly::{Coeff, LagrangeCoeff, kzg::params::ParamsKZG},
    };

    use super::Metrics;
    use crate::{Key, Result};

    /// The device model and its total memory in bytes.
    pub fn info() -> Result<(String, u64)> {
        let info = gpu::present().ok_or("CUDA device unavailable")?;
        Ok((info.name.clone(), info.total_bytes))
    }

    pub fn install(
        params: &ParamsKZG<Bls12>,
        pk: &Key,
    ) -> Result<([gpu::SrsHandle; 2], gpu::KeyHandle)> {
        if gpu::present().is_none() {
            return Err("CUDA device unavailable".into());
        }
        let srs = [params.bases::<Coeff>(), params.bases::<LagrangeCoeff>()]
            .map(|p| gpu::register_srs(adapter::affine(p)));
        let polys = pk.gpu_resident_polys().ok_or("unsupported quotient shape")?;
        let key = gpu::register_key(&polys.iter().map(|p| adapter::scalars(p)).collect::<Vec<_>>());
        if !hooks::install(hooks::GpuHooks {
            msm_g1: Some(gpu::msm_g1),
            fft: Some(gpu::fft),
            ifft: Some(gpu::ifft),
            quotient: Some(gpu::quotient),
        }) {
            return Err("hooks already installed".into());
        }
        Ok((srs, key))
    }

    pub struct Baseline {
        quotient: u64,
        stage: [u64; 8],
    }

    pub fn begin() -> Baseline {
        gpu::begin_request();
        gpu::reset_stats();
        hooks::reset_hook_declines();
        Baseline {
            quotient: gpu::stats().quotient,
            stage: gpu::xfer::stats().stage,
        }
    }

    pub fn finish(before: Baseline) -> Result<Metrics> {
        let stats = gpu::stats();
        let xfer = gpu::xfer::stats();
        let hook_declines = hooks::hook_declines();
        let peak_bytes = gpu::device_bytes().1;
        if !gpu::end_request() {
            return Err("device cleanup failed".into());
        }
        Ok(Metrics {
            msm: stats.msm,
            ntt: stats.ntt,
            quotient: stats.quotient - before.quotient,
            device_errors: stats.device_errors,
            fallbacks: hook_declines.iter().map(|d| d.2).sum(),
            declines: gpu::declines(),
            hook_declines,
            h2d_copies: xfer.h2d_copies,
            h2d_bytes: xfer.h2d_bytes,
            d2h_copies: xfer.d2h_copies,
            d2h_bytes: xfer.d2h_bytes,
            msm_d2h_copies: xfer.msm_d2h_copies,
            msm_d2h_bytes: xfer.msm_d2h_bytes,
            stage: std::array::from_fn(|i| {
                if i == 7 {
                    xfer.stage[i]
                } else {
                    xfer.stage[i] - before.stage[i]
                }
            }),
            peak_bytes,
        })
    }
}

/// The Metal counterpart of the CUDA `device` module above.
#[cfg(all(feature = "rc1-bench-metal", not(feature = "rc1-bench-cuda")))]
pub mod device {
    use midnight_curves::Bls12;
    use midnight_metal as metal;
    use midnight_proofs::{
        gpu::{self as hooks, adapter},
        poly::{
            Coeff, LagrangeCoeff, LagrangeDeltaCoeff, LagrangeDoubleDeltaCoeff,
            kzg::params::ParamsKZG,
        },
    };

    use super::Metrics;
    use crate::{Key, Result};

    /// The device model and its recommended working set in bytes.
    pub fn info() -> Result<(String, u64)> {
        let info = metal::present().ok_or("Metal device unavailable")?;
        Ok((info.name.clone(), info.recommended_max_working_set))
    }

    /// Registers the SRS vectors and the key's resident polynomials, and
    /// installs the hooks.
    pub fn install(
        params: &ParamsKZG<Bls12>,
        pk: &Key,
    ) -> Result<([metal::SrsHandle; 4], metal::KeyHandle)> {
        if !metal::device() {
            return Err("Metal device unavailable".into());
        }
        let srs = [
            params.bases::<Coeff>(),
            params.bases::<LagrangeCoeff>(),
            params.bases::<LagrangeDeltaCoeff>(),
            params.bases::<LagrangeDoubleDeltaCoeff>(),
        ]
        .map(|p| metal::register_srs(adapter::affine(p)));
        let polys = pk.gpu_resident_polys().ok_or("unsupported quotient shape")?;
        let key =
            metal::register_key(&polys.iter().map(|p| adapter::scalars(p)).collect::<Vec<_>>());
        if !hooks::install(hooks::GpuHooks {
            msm_g1: Some(metal::msm_g1),
            fft: Some(metal::fft),
            ifft: Some(metal::ifft),
            quotient: Some(metal::quotient),
        }) {
            return Err("hooks already installed".into());
        }
        Ok((srs, key))
    }

    /// The crate's counters are reset at `begin`.
    pub struct Baseline;

    pub fn begin() -> Baseline {
        metal::begin_request();
        metal::reset_stats();
        hooks::reset_hook_declines();
        Baseline
    }

    /// Unified memory: the transfer and staging counters are 0.
    pub fn finish(_: Baseline) -> Result<Metrics> {
        let stats = metal::stats();
        let hook_declines = hooks::hook_declines();
        let declines = metal::declines();
        let peak_bytes = metal::device_bytes().1;
        if !metal::end_request() {
            return Err("device cleanup failed".into());
        }
        Ok(Metrics {
            msm: stats.msm.served,
            ntt: stats.fft.served + stats.ifft.served,
            quotient: stats.quotient.served,
            device_errors: declines.iter().filter(|d| d.1 == "device-error").map(|d| d.2).sum(),
            fallbacks: hook_declines.iter().map(|d| d.2).sum(),
            declines,
            hook_declines,
            peak_bytes,
            ..Metrics::default()
        })
    }
}
