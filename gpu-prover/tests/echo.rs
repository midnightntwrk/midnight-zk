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

//! ECHO-AUDIT: no caller-supplied value comes back in a reply or goes into
//! a log line. Requests carry a unique marker in enum fields, unknown
//! fields, numbers, paths and malformed input bytes; the marker appears
//! neither in the daemon's replies and stderr nor in the client's output.

use std::{
    io::{BufRead, BufReader, Write},
    os::unix::{fs::PermissionsExt, net::UnixStream},
    path::Path,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

const MARKER: &str = "zq7MARKERx9";

/// A spawned binary, killed and reaped when dropped.
struct Reaped(std::process::Child);

impl Drop for Reaped {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// A command for a shipped binary: stdin null, every descriptor above 2
/// closed in the child.
fn binary(path: &str) -> Command {
    use std::os::unix::process::CommandExt;
    let mut c = Command::new(path);
    c.stdin(Stdio::null());
    // SAFETY: only close(2), which is async-signal-safe, runs in the child
    unsafe {
        c.pre_exec(|| {
            for fd in 3..1024 {
                libc::close(fd);
            }
            Ok(())
        });
    }
    c
}

fn exchange(sock: &Path, line: &str) -> String {
    let mut s = UnixStream::connect(sock).unwrap();
    s.set_read_timeout(Some(Duration::from_secs(120))).unwrap();
    s.write_all(line.as_bytes()).unwrap();
    s.write_all(b"\n").unwrap();
    let mut r = String::new();
    let _ = BufReader::new(&s).read_line(&mut r);
    r
}

fn owner_only(p: &Path, bytes: &[u8]) {
    std::fs::write(p, bytes).unwrap();
    std::fs::set_permissions(p, std::fs::Permissions::from_mode(0o600)).unwrap();
}

#[test]
fn no_caller_value_is_echoed() {
    let dir = tempfile::tempdir().unwrap();
    let sock = dir.path().join("e.sock");
    let err = dir.path().join("daemon.stderr");
    let mut daemon = Reaped(
        binary(env!("CARGO_BIN_EXE_midnight-gpu-proverd"))
            .args(["--insecure-test-srs", "--socket"])
            .arg(&sock)
            .env("MIDNIGHT_GPU_PROVER_THREADS", "2")
            .env("MIDNIGHT_GPU_PROVER_WSL", "off")
            .env("MIDNIGHT_GPU_PROVER_DEVICE", "off")
            .stdout(Stdio::null())
            .stderr(std::fs::File::create(&err).unwrap())
            .spawn()
            .unwrap(),
    );
    let t = Instant::now();
    while UnixStream::connect(&sock).is_err() {
        assert!(
            t.elapsed() < Duration::from_secs(300),
            "daemon did not start"
        );
        std::thread::sleep(Duration::from_millis(200));
    }

    // malformed inputs whose bytes carry the marker: wrong length, and the
    // right length with non-canonical scalars
    let short = dir.path().join("short.bin");
    owner_only(&short, MARKER.as_bytes());
    let bad = dir.path().join("bad.bin");
    let mut b = MARKER.repeat(10).into_bytes();
    b.resize(96, 0xff);
    owner_only(&bad, &b);
    let out = dir.path().join(format!("out-{MARKER}"));
    let missing = dir.path().join(format!("in-{MARKER}"));
    let q = |p: &Path| serde_json::to_string(p.to_str().unwrap()).unwrap();

    let lines = [
        format!("{MARKER} is not JSON"),
        format!(r#"{{"op":"{MARKER}"}}"#),
        format!(r#"{{"op":"health","{MARKER}":1}}"#),
        format!(r#"{{"op":"evict","tables":"{MARKER}"}}"#),
        format!(r#"{{"op":"evict","tables":1e999{MARKER}}}"#),
        format!(
            r#"{{"op":"prove","input":{},"output":{},"zero_check":"{MARKER}"}}"#,
            q(&short),
            q(&out)
        ),
        format!(
            r#"{{"op":"prove","input":{},"output":{}}}"#,
            q(&missing),
            q(&out)
        ),
        format!(
            r#"{{"op":"prove","input":{},"output":{}}}"#,
            q(&short),
            q(&out)
        ),
        format!(
            r#"{{"op":"prove","input":{},"output":{}}}"#,
            q(&bad),
            q(&out)
        ),
        format!(
            r#"{{"op":"prove","input":{},"output":"/{MARKER}/no/dir/p"}}"#,
            q(&bad)
        ),
    ];
    for l in &lines {
        let r = exchange(&sock, l);
        assert!(!r.is_empty(), "no reply to {l}");
        assert!(!r.contains(MARKER), "the reply echoes the request: {r}");
    }

    // the client: arguments, paths and its environment carry the marker
    let client_at = |sock: &Path, args: &[&str], env: &[(&str, &str)]| -> String {
        let mut c = binary(env!("CARGO_BIN_EXE_midnight-gpu-prover-client"));
        c.arg("--socket")
            .arg(sock)
            .args(args)
            .env(
                "MIDNIGHT_GPU_PROVER_BREAKER_STATE",
                dir.path().join("breaker"),
            )
            .env("MIDNIGHT_GPU_PROVER_THREADS", "2");
        for (k, v) in env {
            c.env(k, v);
        }
        let o = c.output().unwrap();
        format!(
            "{}{}",
            String::from_utf8_lossy(&o.stdout),
            String::from_utf8_lossy(&o.stderr)
        )
    };
    let (m, s, o) = (
        missing.to_str().unwrap(),
        short.to_str().unwrap(),
        out.to_str().unwrap(),
    );
    let bad_s = bad.to_str().unwrap();
    for (args, env) in [
        (vec!["prove", m, o, "--no-fallback"], vec![]),
        (vec!["prove", s, o, "--no-fallback"], vec![]),
        (vec!["prove", bad_s, o, "--no-fallback"], vec![]),
        (vec![MARKER], vec![]),
        (vec!["prove", s, o, MARKER], vec![]),
        (
            vec!["health"],
            vec![("MIDNIGHT_GPU_PROVER_REPLY_TIMEOUT_S", MARKER)],
        ),
        (
            vec!["health"],
            vec![("MIDNIGHT_GPU_PROVER_CPU_FALLBACK", MARKER)],
        ),
    ] {
        let r = client_at(&sock, &args, &env);
        assert!(
            !r.contains(MARKER),
            "the client echoes {args:?} {env:?}: {r}"
        );
    }
    // no daemon: the in-process fallback gets the marker paths (input,
    // output, SRS, lock) and the socket path carries the marker too
    let dead = dir.path().join(format!("{MARKER}.sock"));
    let lock = dir.path().join(MARKER).join("lock");
    let srs = dir.path().join(format!("{MARKER}.srs"));
    let (l, srs_s) = (lock.to_str().unwrap(), srs.to_str().unwrap());
    for args in [
        vec!["prove", m, o],
        vec!["prove", bad_s, o, "--srs", srs_s],
        vec!["prove", s, o, "--lock", l],
        vec!["health"],
    ] {
        let r = client_at(&dead, &args, &[]);
        assert!(!r.contains(MARKER), "the client echoes {args:?}: {r}");
    }
    // a config file named by the client's environment: missing, and with a
    // marker field
    let cfgf = dir.path().join(format!("{MARKER}.json"));
    let r = client_at(
        &dead,
        &["health"],
        &[("MIDNIGHT_GPU_PROVER_CLIENT_CONFIG", cfgf.to_str().unwrap())],
    );
    assert!(
        !r.contains(MARKER),
        "the client echoes its config path: {r}"
    );
    std::fs::write(&cfgf, format!(r#"{{"{MARKER}": 1}}"#)).unwrap();
    let r = client_at(
        &dead,
        &["health"],
        &[("MIDNIGHT_GPU_PROVER_CLIENT_CONFIG", cfgf.to_str().unwrap())],
    );
    assert!(
        !r.contains(MARKER),
        "the client echoes its config file: {r}"
    );

    let _ = exchange(&sock, r#"{"op":"stop"}"#);
    let _ = daemon.0.wait();
    let log = std::fs::read_to_string(&err).unwrap();
    assert!(
        !log.contains(MARKER),
        "the daemon log echoes a request: {log}"
    );
}
