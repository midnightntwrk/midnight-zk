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

//! The device-owner actor's protocol core replays every ITF trace of the
//! Quint model in `formal/gpu-prover/vectors/actor`, or in the `actor`
//! folder of `ORACLE_VECTOR_DIR` when it is set. No device is used.

#[test]
fn itf_traces_replay() {
    let dir = std::env::var_os("ORACLE_VECTOR_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../formal/gpu-prover/vectors")
        })
        .join("actor");
    let mut files = 0;
    for entry in std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display())) {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|e| e == "json") {
            let text = std::fs::read_to_string(&path).expect("read trace");
            let steps = midnight_gpu::actor::protocol::replay_itf(&text)
                .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
            assert!(steps > 0, "{} has no steps", path.display());
            files += 1;
        }
    }
    assert!(files > 0, "the trace directory holds no traces");
}
