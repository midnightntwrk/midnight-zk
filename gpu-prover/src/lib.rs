// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A resident prover service for Midnight circuits (KZG over BLS12-381).
//!
//! [`ProverService`] holds the SRS, the proving and verifying keys and the
//! device state between requests. For each request it:
//!
//! 1. computes the device memory the proof needs from the loaded key, and
//!    admits the device phases by the ladder `gpu`, `wait`, `evict`, `cpu`
//!    ([`admission`]);
//! 2. proves with fresh operating-system randomness;
//! 3. zeroes and frees every witness-dependent device and staging buffer;
//! 4. verifies the proof with the stock verifier, and returns nothing if it
//!    fails;
//! 5. returns the proof with a [`report::ProofRecord`] that holds counts,
//!    sizes, times and hashes only.
//!
//! The daemon ([`daemon`]) serves one service on a local Unix socket. The
//! client ([`client`]) sends requests and proves on the CPU in-process when
//! the daemon cannot serve, with a circuit breaker.
//!
//! Without the `cuda` and `metal` features, or without a detected device, every
//! phase runs on the CPU and no CUDA toolkit is needed.

#![deny(missing_docs)]

pub mod admission;
pub mod client;
pub mod config;
pub mod daemon;
pub mod device;
pub mod example;
pub mod input;
pub mod lock;
pub mod need;
pub mod protocol;
pub mod report;
pub mod service;

pub use config::{ClientConfig, Config};
pub use service::{ProverService, RequestOptions, ServedRelation};

/// Errors of the service, the daemon and the client.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// A configuration value is invalid.
    Config(String),
    /// The service refuses to start or to serve (bad k, VK mismatch, policy).
    Refused(String),
    /// The request input is invalid or not accessible.
    Input(String),
    /// The output file cannot be written.
    Output(String),
    /// The prover failed.
    Prove(String),
    /// The stock verifier refused the proof. No proof is returned.
    Verify,
    /// In acceptance mode, the request would be served degraded.
    Degraded(String),
    /// The service stopped serving because an erasure was not confirmed.
    Retired(String),
    /// The daemon is busy (one request served, one waiting).
    Busy,
    /// The daemon cannot be reached or broke the protocol.
    Daemon(String),
}

impl Error {
    /// The protocol name of the error kind.
    pub fn kind(&self) -> &'static str {
        match self {
            Error::Config(_) => "config",
            Error::Refused(_) => "refused",
            Error::Input(_) => "input",
            Error::Output(_) => "output",
            Error::Prove(_) => "prove",
            Error::Verify => "verify",
            Error::Degraded(_) => "degraded",
            Error::Retired(_) => "retired",
            Error::Busy => "busy",
            Error::Daemon(_) => "daemon",
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Verify => write!(f, "verify: the stock verifier refused the proof"),
            Error::Busy => write!(f, "busy: one request is served and one waits"),
            Error::Config(m)
            | Error::Refused(m)
            | Error::Input(m)
            | Error::Output(m)
            | Error::Prove(m)
            | Error::Degraded(m)
            | Error::Retired(m)
            | Error::Daemon(m) => write!(f, "{}: {m}", self.kind()),
        }
    }
}

impl std::error::Error for Error {}
