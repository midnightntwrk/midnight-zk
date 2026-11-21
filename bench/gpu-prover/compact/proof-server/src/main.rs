// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The Midnight proof server 9.0.1 with GPU hooks.
//!
//! `main` installs the hooks of the backend crate first, then runs the stock
//! proof-server `main`: the same flags and environment variables, the same
//! key-material prefetch, `WorkerPool::new` and `server`. The routes and the
//! request and response formats do not change.
//!
//! Built with the `gpu` feature, the server refuses to start when the backend
//! installs no hooks, so a CPU-only build cannot run under a GPU label. A
//! background thread logs the hook counters each time they change (one line
//! per proof with one worker), so a silent CPU fallback shows in the log.

use std::time::Duration;

use base_crypto::data_provider::{FetchMode, MidnightDataProvider, OutputMode};
use clap::Parser;
use futures::future::join;
use ledger::dust::DustResolver;
use ledger::prove::Resolver;
use midnight_proof_server::endpoints::PUBLIC_PARAMS;
use midnight_proof_server::{server, worker_pool::WorkerPool};
use tracing::{Level, info};
use tracing_subscriber::filter::Targets;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{Layer, Registry};
use transient_crypto::proofs::{KeyLocation, Resolver as ResolverT};

#[derive(Parser, Debug)]
struct Args {
    #[arg(
        short,
        long,
        default_value_t = 6300,
        env = "MIDNIGHT_PROOF_SERVER_PORT"
    )]
    port: u16,
    #[arg(short, long, env = "MIDNIGHT_PROOF_SERVER_VERBOSE")]
    verbose: bool,
    #[arg(long, default_value_t = 10, env = "MIDNIGHT_PROOF_SERVER_JOB_CAPACITY")]
    job_capacity: usize,
    /// One worker by default: two proofs at the same time would share one
    /// device. (The stock default is 2.)
    #[arg(long, default_value_t = 1, env = "MIDNIGHT_PROOF_SERVER_NUM_WORKERS")]
    num_workers: usize,
    #[arg(
        long,
        default_value_t = 600.0,
        env = "MIDNIGHT_PROOF_SERVER_JOB_TIMEOUT"
    )]
    job_timeout: f64,
    #[arg(
        long,
        default_value_t = false,
        env = "MIDNIGHT_PROOF_SERVER_NO_FETCH_PARAMS"
    )]
    no_fetch_params: bool,
}

#[cfg(feature = "gpu")]
mod gpu {
    pub(crate) fn install() -> Option<String> {
        compact_bench_gpu::install_hooks()
    }
    pub(crate) fn counters() -> [u64; 6] {
        let c = compact_bench_gpu::counters();
        [
            c.msm,
            c.ntt,
            c.coset,
            c.quotient,
            c.fallbacks,
            c.device_peak_bytes,
        ]
    }
}

#[cfg(not(feature = "gpu"))]
mod gpu {
    pub(crate) fn install() -> Option<String> {
        None
    }
    pub(crate) fn counters() -> [u64; 6] {
        [0; 6]
    }
}

/// Logs the hook counters each time they change.
fn watch_counters() {
    std::thread::spawn(|| {
        let mut last = gpu::counters();
        loop {
            std::thread::sleep(Duration::from_millis(200));
            let now = gpu::counters();
            if now != last {
                let d: Vec<u64> = (0..5).map(|i| now[i] - last[i]).collect();
                info!(
                    "hooks: msm {} ntt {} coset {} quotient {} fallbacks {} (since last line); \
                     device peak {} B",
                    d[0], d[1], d[2], d[3], d[4], now[5]
                );
                last = now;
            }
        }
    });
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    let args = Args::parse();
    init_logging(args.verbose);
    match gpu::install() {
        Some(device) => {
            info!("GPU hooks installed: {device}");
            watch_counters();
        }
        None if cfg!(feature = "gpu") => {
            return Err(std::io::Error::other(
                "built with the gpu feature, but the backend installed no hooks (no device?)",
            ));
        }
        None => info!("no GPU hooks: stock CPU proving"),
    }
    if !args.no_fetch_params {
        info!("Ensuring zswap key material is available...");
        let resolver = Resolver::new(
            PUBLIC_PARAMS.clone(),
            DustResolver(
                MidnightDataProvider::new(
                    FetchMode::OnDemand,
                    OutputMode::Log,
                    ledger::dust::DUST_EXPECTED_FILES.to_owned(),
                )
                .expect("data provider initialization failed"),
            ),
            Box::new(move |_: KeyLocation| Box::pin(std::future::ready(Ok(None)))),
        );
        let ks = futures::future::join_all((10..=15).map(|k| PUBLIC_PARAMS.0.fetch_k(k)));
        let keys = futures::future::join_all(
            [
                "midnight/zswap/spend",
                "midnight/zswap/output",
                "midnight/zswap/sign",
                "midnight/dust/spend",
            ]
            .into_iter()
            .map(|k| resolver.resolve_key(KeyLocation(k.into()))),
        );
        let (ks, keys) = join(ks, keys).await;
        ks.into_iter().collect::<Result<Vec<_>, _>>()?;
        keys.into_iter().collect::<Result<Vec<_>, _>>()?;
    }
    let pool = WorkerPool::new(args.num_workers, args.job_capacity, args.job_timeout);
    server(args.port, !args.no_fetch_params, pool).unwrap().0.await
}

/// The log filter of the server. It does not read `RUST_LOG`, so no
/// environment setting can turn the zkir targets back on.
///
/// zkir logs the private transcript at error level on malformed-witness paths.
/// The stock server turns off `zkir`, which matches only the zkir command-line
/// tool; the library's target is `midnight_zkir`, so both are off here.
fn log_filter(level: Level) -> Targets {
    use tracing_subscriber::filter::LevelFilter;
    Targets::new()
        .with_default(level)
        .with_target("zkir", LevelFilter::OFF)
        .with_target("midnight_zkir", LevelFilter::OFF)
}

fn init_logging(verbose: bool) {
    let level = if verbose { Level::DEBUG } else { Level::INFO };
    Registry::default()
        .with(tracing_subscriber::fmt::layer().with_filter(log_filter(level)))
        .try_init()
        .ok();
}

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::sync::{Arc, Mutex};

    use tracing::Level;
    use tracing_subscriber::Layer;
    use tracing_subscriber::layer::SubscriberExt;
    use transient_crypto::curve::Fr;
    use transient_crypto::proofs::{KeyLocation, ProofPreimage, Zkir};

    #[derive(Clone, Default)]
    struct Captured(Arc<Mutex<Vec<u8>>>);
    impl Write for Captured {
        fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(b);
            Ok(b.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// A malformed witness (one private-transcript value that the circuit does
    /// not consume) makes zkir log the private transcript at error level. With
    /// the server's filter, nothing from zkir reaches the log.
    #[test]
    fn malformed_witness_logs_nothing_from_zkir() {
        let out = Captured::default();
        let w = out.clone();
        let layer = tracing_subscriber::fmt::layer()
            .with_ansi(false)
            .with_writer(move || w.clone())
            .with_filter(super::log_filter(Level::DEBUG));
        let subscriber = tracing_subscriber::registry().with(layer);
        let secret = Fr::from(0x5ec2e7u64);
        let preimage = ProofPreimage {
            inputs: vec![],
            private_transcript: vec![secret],
            public_transcript_inputs: vec![],
            public_transcript_outputs: vec![],
            binding_input: Fr::from(0u64),
            communications_commitment: None,
            key_location: KeyLocation("test".into()),
        };
        let ir = zkir_v3::IrSource::default();
        let res = tracing::subscriber::with_default(subscriber, || ir.check(&preimage));
        assert!(res.is_err(), "the malformed witness must be refused");
        let log = String::from_utf8(out.0.lock().unwrap().clone()).unwrap();
        assert!(
            !log.contains("zkir"),
            "zkir wrote to the log on a malformed witness:\n{log}"
        );
    }
}
