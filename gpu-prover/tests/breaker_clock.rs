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

//! ORACLE-29: the client records a breaker failure at the end of the
//! exchange, not at its start (an exchange may take up to the reply
//! timeout, so a failure stamped at the start ages out of the window early).

mod common;

use std::{
    path::Path,
    sync::{Arc, atomic::Ordering::SeqCst},
};

use common::*;
use midnight_gpu_prover::{
    ClientConfig, Error,
    client::{Breaker, Client},
};

#[test]
fn breaker_failure_is_stamped_after_the_exchange() {
    let dir = tempfile::tempdir().unwrap();
    let cfg = ClientConfig {
        socket: Some(dir.path().join("none.sock")),
        breaker_state: Some(dir.path().join("breaker")),
        ..ClientConfig::default()
    };
    let c = Arc::new(std::sync::atomic::AtomicU64::new(0));
    // 0 before the exchange, 1000 after it
    let client = Client::with_clock(cfg.clone(), Box::new(move || c.fetch_add(1, SeqCst) * 1000));
    let inp = input_file(dir.path(), "in", 1);
    let no_fallback = |_: &Path, _: &Path| Err(Error::Daemon("no fallback in this test".into()));
    let _ = client.prove(&inp, &dir.path().join("out"), false, None, &no_fallback);
    let b = Breaker::new(cfg.breaker_path(), 3, 600, 600);
    assert_eq!(b.state().failures, vec![1000]);
}
