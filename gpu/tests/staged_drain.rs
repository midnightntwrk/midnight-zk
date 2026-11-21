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

//! A staged copy (through the bounce buffer) whose final synchronisation
//! fails returns only after its stream drained, as every other error exit
//! does: the drain is counted, a drain that is not confirmed holds the bounce
//! buffer (never handed out, wiped or freed again) and counts one erasure
//! failure. In its own test binary: the held buffer stays for the rest of
//! the process.
#![cfg(feature = "test-fault")]

use midnight_gpu as gpu;

#[test]
fn staged_copy_sync_failure_drains_and_holds() {
    if !gpu::device() {
        eprintln!(
            "skipped: no device (CUDA core built: {})",
            gpu::cuda_built()
        );
        return;
    }
    let o = gpu::fault::staged_sync_fail().expect("the staged copy runs");
    if o[0] == 2 {
        eprintln!("skipped: this device does not stage copies");
        return;
    }
    eprintln!(
        "error {}, idle {}, drains {}, unconfirmed {}, held {}, erasure failures {}",
        o[0], o[1], o[2], o[3], o[4], o[5]
    );
    assert_eq!(o[0], 1, "the injected failure returns an error");
    assert_eq!(o[1], 1, "returned with work still queued");
    assert_eq!(o[2], 1, "the error exit counts one drain");
    assert_eq!(o[3], 1, "the unconfirmed drain is counted");
    assert_eq!(
        o[4], 1,
        "the bounce buffer is held after the unconfirmed drain"
    );
    assert_eq!(o[5], 1, "the held buffer counts one erasure failure");
}
