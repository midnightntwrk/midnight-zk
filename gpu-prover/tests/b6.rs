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

//! B6: no witness byte reaches a reply or the daemon's log. A relation whose
//! decoder echoes its input in its error, and panics with its input, is
//! served by a daemon in a child process (this test binary run again);
//! two prove requests carry a marker in their witness bytes; the marker, in
//! hex and in decimal, must appear in neither reply nor the child's stderr.

mod common;

use std::{
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use common::*;
use midnight_gpu_prover::{
    ServedRelation, client, daemon, device::NoDevice, example::PoseidonPreimage, protocol::Request,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};

type F = midnight_curves::Fq;

/// The marker in the witness bytes.
const MARKER: [u8; 5] = [0xC0, 0xFF, 0xEE, 0x5E, 0xED];

/// The example relation with a decoder that leaks: its error carries the
/// input in hex and decimal, and an input starting with 0 makes it panic
/// with the same text.
#[derive(Clone, Copy, Debug, Default)]
struct Echo;

impl Relation for Echo {
    type Instance = F;
    type Witness = [F; 3];
    type Error = Error;

    fn format_instance(i: &F) -> Result<Vec<F>, Error> {
        PoseidonPreimage::format_instance(i)
    }

    fn circuit(
        &self,
        std: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<F>,
        witness: Value<[F; 3]>,
    ) -> Result<(), Error> {
        PoseidonPreimage.circuit(std, layouter, instance, witness)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        PoseidonPreimage.used_chips()
    }

    fn write_relation<W: std::io::Write>(&self, _: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_: &mut R) -> std::io::Result<Self> {
        Ok(Echo)
    }
}

impl ServedRelation for Echo {
    fn name(&self) -> String {
        "echo".into()
    }

    fn decode_input(&self, input: &[u8]) -> Result<(F, [F; 3]), String> {
        let text = format!("{} {:?}", hex::encode(input), input);
        if input.first() == Some(&0) {
            panic!("the decoder saw {text}");
        }
        Err(format!("the decoder refuses {text}"))
    }
}

/// The marker forms that must not appear: hex (both cases) and the decimal
/// bytes as `{:?}` prints them.
fn leaks(s: &str) -> Vec<&'static str> {
    ["c0ffee5eed", "C0FFEE5EED", "192, 255, 238, 94, 237"]
        .into_iter()
        .filter(|m| s.contains(m))
        .collect()
}

fn owner_only(dir: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, bytes).unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o600)).unwrap();
    p
}

/// The child: serves `Echo` on `B6_SOCKET` until a stop. Does nothing in a
/// normal test run.
#[test]
fn b6_child_daemon() {
    let Some(sock) = std::env::var_os("B6_SOCKET") else {
        return;
    };
    let svc =
        midnight_gpu_prover::ProverService::with_device(Echo, srs(), config(), Box::new(NoDevice))
            .unwrap();
    let _ = daemon::run(svc, Path::new(&sock));
}

/// A child process that is killed and reaped when dropped.
struct Reaped(std::process::Child);

impl Drop for Reaped {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[test]
fn witness_bytes_reach_neither_reply_nor_log() {
    let dir = tempfile::tempdir().unwrap();
    let sock = dir.path().join("b6.sock");
    let log = dir.path().join("stderr.log");
    let mut child = Reaped(
        Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "b6_child_daemon",
                "--nocapture",
                "--test-threads=1",
            ])
            .env("B6_SOCKET", &sock)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(std::fs::File::create(&log).unwrap())
            .spawn()
            .unwrap(),
    );
    let t = Instant::now();
    let ask = |req: &Request| match client::request(&sock, req, None, Duration::from_secs(60)) {
        Ok(v) => v.to_string(),
        Err(e) => e.to_string(),
    };
    while client::request(&sock, &Request::Health {}, None, Duration::from_secs(5)).is_err() {
        assert!(
            t.elapsed() < Duration::from_secs(120),
            "the child daemon did not start"
        );
        std::thread::sleep(Duration::from_millis(100));
    }
    let refused: Vec<u8> = MARKER.iter().copied().cycle().take(100).collect();
    let mut panics = vec![0u8];
    panics.extend(&refused);
    let mut replies = Vec::new();
    for (name, bytes) in [("refused.bin", &refused), ("panics.bin", &panics)] {
        let input = owner_only(dir.path(), name, bytes);
        replies.push(ask(&Request::Prove {
            input,
            output: dir.path().join("proof.bin"),
            zero_check: false,
        }));
    }
    let _ = ask(&Request::Stop {});
    let deadline = Instant::now() + Duration::from_secs(30);
    while child.0.try_wait().unwrap().is_none() && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(100));
    }
    drop(child);
    let stderr = std::fs::read_to_string(&log).unwrap();
    for (i, r) in replies.iter().enumerate() {
        assert!(leaks(r).is_empty(), "reply {i} leaks {:?}: {r}", leaks(r));
        assert!(
            r.contains("\"ok\":false"),
            "reply {i} is not a refusal: {r}"
        );
    }
    assert!(
        leaks(&stderr).is_empty(),
        "the daemon log leaks {:?}:\n{stderr}",
        leaks(&stderr)
    );
}
