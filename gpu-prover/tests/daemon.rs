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

//! The daemon and the client over a real Unix socket: protocol, socket mode,
//! queue and `busy`, health during a proof, input refusal, lock leases, CPU
//! fallback labelling, and the shipped binaries end to end.

mod common;

use std::{
    os::unix::fs::MetadataExt,
    path::{Path, PathBuf},
    thread::JoinHandle,
    time::Duration,
};

use common::*;
use midnight_gpu_prover::{
    ClientConfig, Config, Error,
    client::{self, Client},
    daemon::{self, ServeEnd},
    device::{Device, NoDevice},
    example::{PoseidonPreimage, example_input},
    protocol::Request,
    report::Label,
};

const T: Duration = Duration::from_secs(300);

struct Daemon {
    socket: PathBuf,
    handle: Option<JoinHandle<ServeEnd>>,
}

impl Daemon {
    fn start(dir: &Path, cfg: Config, dev: Box<dyn Device>) -> Daemon {
        let socket = dir.join("d.sock");
        let l = daemon::bind(&socket).unwrap();
        let (tx, rx) = std::sync::mpsc::channel();
        let handle = std::thread::spawn(move || {
            let mut svc = service(cfg, dev);
            tx.send(()).unwrap();
            daemon::serve_with(&mut svc, l, Duration::from_secs(2))
        });
        rx.recv().unwrap();
        Daemon {
            socket,
            handle: Some(handle),
        }
    }

    fn ask(&self, req: &Request) -> serde_json::Value {
        client::request(&self.socket, req, None, T).unwrap()
    }

    fn stop(mut self) -> ServeEnd {
        let _ = self.ask(&Request::Stop {});
        self.handle.take().unwrap().join().unwrap()
    }
}

fn prove_req(input: &Path, output: &Path) -> Request {
    Request::Prove {
        input: input.into(),
        output: output.into(),
        zero_check: false,
    }
}

#[test]
fn round_trip_health_prove_stats_evict_stop() {
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), config(), Box::new(NoDevice));
    assert_eq!(std::fs::metadata(&d.socket).unwrap().mode() & 0o777, 0o600);
    let h = d.ask(&Request::Health {});
    assert_eq!(
        (h["ok"].as_bool(), h["state"].as_str()),
        (Some(true), Some("ready"))
    );
    assert_eq!(h["device"], false);

    let inp = input_file(dir.path(), "in.bin", 1);
    let out = dir.path().join("proof.bin");
    let r = d.ask(&prove_req(&inp, &out));
    assert_eq!(r["ok"], true, "{r}");
    assert_eq!(r["record"]["label"], "cpu");
    assert!(r["queue"]["wait_s"].as_f64().is_some());
    // the reply does not repeat the request's paths
    let text = r.to_string();
    assert!(!text.contains("in.bin") && !text.contains("proof.bin"));
    // the proof is owner-only, its hash is in the record, and it verifies
    assert_eq!(std::fs::metadata(&out).unwrap().mode() & 0o777, 0o600);
    let proof = std::fs::read(&out).unwrap();
    assert_eq!(
        r["record"]["proof_sha256"],
        midnight_gpu_prover::report::sha256_hex(&proof)
    );
    let svc = service(config(), Box::new(NoDevice));
    let (inst, _) =
        midnight_gpu_prover::ServedRelation::decode_input(&PoseidonPreimage, &example_input(1))
            .unwrap();
    midnight_zk_stdlib::verify::<PoseidonPreimage, blake2b_simd::State, _>(
        svc.verifier_params(),
        svc.vk(),
        &inst,
        None,
        &proof,
    )
    .unwrap();

    let s = d.ask(&Request::Stats {});
    assert_eq!(s["served"], 1);
    assert_eq!(s["start"]["vk_sha256"], svc.start_record().vk_sha256);
    let e = d.ask(&Request::Evict { tables: true });
    assert_eq!(e["evicted_bytes"], 0);
    assert_eq!(d.stop(), ServeEnd::Stopped);
}

#[test]
fn malformed_and_unknown_requests_are_refused() {
    use std::io::{BufRead, BufReader, Write};
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), config(), Box::new(NoDevice));
    for line in [
        "{\"op\":\"fly\"}\n",
        "not json\n",
        "{\"op\":\"health\",\"x\":1}\n",
    ] {
        let mut s = std::os::unix::net::UnixStream::connect(&d.socket).unwrap();
        s.write_all(line.as_bytes()).unwrap();
        let mut reply = String::new();
        BufReader::new(&s).read_line(&mut reply).unwrap();
        let v: serde_json::Value = serde_json::from_str(&reply).unwrap();
        assert_eq!(v["error"]["kind"], "bad-request", "{line}");
        assert!(!reply.contains("fly"));
    }
    // a client that sends nothing gets an error after the deadline
    let s = std::os::unix::net::UnixStream::connect(&d.socket).unwrap();
    let mut reply = String::new();
    BufReader::new(&s).read_line(&mut reply).unwrap();
    assert!(reply.contains("bad-request"));
    d.stop();
}

#[test]
fn input_readable_by_others_is_refused_and_no_proof_is_written() {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), config(), Box::new(NoDevice));
    let inp = input_file(dir.path(), "in.bin", 1);
    std::fs::set_permissions(&inp, std::fs::Permissions::from_mode(0o644)).unwrap();
    let out = dir.path().join("proof.bin");
    let r = d.ask(&prove_req(&inp, &out));
    assert_eq!(r["error"]["kind"], "input");
    assert!(!out.exists());
    d.stop();
}

#[test]
fn queue_of_one_third_request_is_busy_and_health_answers_during_a_proof() {
    let dir = tempfile::tempdir().unwrap();
    let f = Fake {
        delay: Duration::from_secs(3),
        ..Fake::default()
    };
    let d = Daemon::start(dir.path(), config(), Box::new(f));
    let socket = d.socket.clone();
    let mut handles = Vec::new();
    for i in 0..2u64 {
        let inp = input_file(dir.path(), &format!("in{i}.bin"), i);
        let out = dir.path().join(format!("p{i}.bin"));
        let s = socket.clone();
        handles.push(std::thread::spawn(move || {
            client::request(&s, &prove_req(&inp, &out), None, T).unwrap()
        }));
        std::thread::sleep(Duration::from_millis(400));
        if i == 0 {
            // health is answered while the proof runs and a place is free
            let h = client::request(&socket, &Request::Health {}, None, T).unwrap();
            assert_eq!(h["state"], "proving");
            assert_eq!(h["queued"], 1);
        }
    }
    // one is served and one waits: a third gets `busy` at once
    let inp = input_file(dir.path(), "in2.bin", 2);
    let t = std::time::Instant::now();
    let r = client::request(
        &socket,
        &prove_req(&inp, &dir.path().join("p2.bin")),
        None,
        T,
    )
    .unwrap();
    assert_eq!(r["error"]["kind"], "busy");
    assert!(t.elapsed() < Duration::from_secs(2));
    // with both places taken, health also gets `busy` at once (alive)
    let h = client::request(&socket, &Request::Health {}, None, T).unwrap();
    assert_eq!(h["error"]["kind"], "busy");
    let replies: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    for r in &replies {
        assert_eq!(r["ok"], true, "{r}");
    }
    // the second waited for the first
    assert!(replies[1]["queue"]["wait_s"].as_f64().unwrap() > 1.0);
    d.stop();
}

#[test]
fn lock_lease_gates_device_work() {
    let dir = tempfile::tempdir().unwrap();
    let lock = dir.path().join("device.lock");
    std::fs::write(&lock, b"").unwrap();
    let cfg = Config {
        lock_path: Some(lock.clone()),
        ..config()
    };
    let f = Fake {
        shape: Some(Fake::big_shape()),
        ..Fake::default()
    };
    let d = Daemon::start(dir.path(), cfg, Box::new(f));
    let inp = input_file(dir.path(), "in.bin", 1);
    let out = dir.path().join("p.bin");
    // without the lock: CPU, marked
    let r = d.ask(&prove_req(&inp, &out));
    assert_eq!(r["record"]["label"], "cpu", "{r}");
    assert!(r["record"]["degraded_reasons"][0].as_str().unwrap().contains("no-descriptor"));
    // holding the lock and passing its descriptor: the device phases run
    let held = midnight_gpu_prover::lock::lock_exclusive(&lock).unwrap();
    use std::os::fd::AsFd;
    let r = client::request(&d.socket, &prove_req(&inp, &out), Some(held.as_fd()), T).unwrap();
    assert_eq!(r["record"]["label"], "gpu", "{r}");
    // a descriptor of the lock file that another holder's lock covers: refused
    let stranger = std::fs::File::open(&lock).unwrap();
    let r = client::request(&d.socket, &prove_req(&inp, &out), Some(stranger.as_fd()), T).unwrap();
    assert_eq!(r["record"]["label"], "cpu");
    assert!(r["record"]["degraded_reasons"][0].as_str().unwrap().contains("held-by-other"));
    drop(held);
    d.stop();
}

#[test]
fn client_labels_daemon_and_fallback_results() {
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), config(), Box::new(NoDevice));
    let cc = ClientConfig {
        socket: Some(d.socket.clone()),
        breaker_state: Some(dir.path().join("b")),
        ..ClientConfig::default()
    };
    let fallback = |i: &Path, o: &Path| -> Result<serde_json::Value, Error> {
        client::cpu_prove(PoseidonPreimage, srs(), &config(), i, o)
    };
    let c = Client::new(cc);
    let inp = input_file(dir.path(), "in.bin", 3);
    let out = dir.path().join("p.bin");
    let o = c.prove(&inp, &out, false, None, &fallback).unwrap();
    assert_eq!((o.label, o.daemon_error), (Label::Cpu, None));
    d.stop();
    // daemon gone: the client proves in-process and labels the result
    std::fs::remove_file(&out).unwrap();
    let o = c.prove(&inp, &out, false, None, &fallback).unwrap();
    assert_eq!(o.label, Label::CpuFallback);
    assert_eq!(o.record["label"], "cpu-fallback");
    assert!(out.exists());
    assert_eq!(c.breaker().state().failures.len(), 1);
}

#[test]
fn retired_daemon_stops_after_its_reply() {
    let dir = tempfile::tempdir().unwrap();
    let f = Fake {
        shape: Some(Fake::big_shape()),
        wipe_fails: true,
        ..Fake::default()
    };
    let mut d = Daemon::start(dir.path(), config(), Box::new(f));
    let inp = input_file(dir.path(), "in.bin", 1);
    let out = dir.path().join("p.bin");
    let r = d.ask(&prove_req(&inp, &out));
    assert_eq!(r["error"]["kind"], "retired");
    assert!(!out.exists());
    let end = d.handle.take().unwrap().join().unwrap();
    assert!(matches!(end, ServeEnd::Retired(_)));
}

/// A spawned binary that is killed and reaped when dropped, also when the
/// test panics, so no daemon outlives its test.
struct Reaped(std::process::Child);

impl Reaped {
    fn pid(&self) -> u32 {
        self.0.id()
    }
}

impl Drop for Reaped {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// A command for a shipped binary: stdin and stdout null, stderr null, and
/// every file descriptor above 2 closed in the child, so it holds no pipe
/// or lock of the test runner.
fn binary(path: &str) -> std::process::Command {
    use std::{os::unix::process::CommandExt, process::Stdio};
    let mut c = std::process::Command::new(path);
    c.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
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

/// Whether `pid` is a live process (not reaped).
fn alive(pid: u32) -> bool {
    Path::new(&format!("/proc/{pid}")).exists()
}

/// A daemon spawned by a test that panics is killed and reaped by the guard.
#[test]
fn spawned_daemon_is_reaped_when_the_test_panics() {
    let dir = tempfile::tempdir().unwrap();
    let sock = dir.path().join("p.sock");
    let (tx, rx) = std::sync::mpsc::channel();
    let r = std::thread::spawn(move || {
        let d = Reaped(
            binary(env!("CARGO_BIN_EXE_midnight-gpu-proverd"))
                .args(["--insecure-test-srs", "--socket"])
                .arg(&sock)
                .env("MIDNIGHT_GPU_PROVER_DEVICE", "off")
                .spawn()
                .unwrap(),
        );
        tx.send(d.pid()).unwrap();
        panic!("a failing test");
    })
    .join();
    assert!(r.is_err());
    let pid = rx.recv().unwrap();
    assert!(!alive(pid), "the daemon {pid} outlived its test");
}

/// The shipped binaries: `midnight-gpu-proverd` serves and
/// `midnight-gpu-prover-client` calls; after the daemon stops, the client
/// falls back to the CPU.
#[test]
fn binaries_serve_and_call() {
    use std::process::Stdio;
    let dir = tempfile::tempdir().unwrap();
    let sock = dir.path().join("p.sock");
    // the device is off: this test checks the binaries, not the device path
    let mut daemon = Reaped(
        binary(env!("CARGO_BIN_EXE_midnight-gpu-proverd"))
            .args(["--insecure-test-srs", "--socket"])
            .arg(&sock)
            .env("MIDNIGHT_GPU_PROVER_THREADS", "2")
            .env("MIDNIGHT_GPU_PROVER_WSL", "off")
            .env("MIDNIGHT_GPU_PROVER_DEVICE", "off")
            .spawn()
            .unwrap(),
    );
    let pid = daemon.pid();
    let client = |args: &[&str]| -> serde_json::Value {
        let o = binary(env!("CARGO_BIN_EXE_midnight-gpu-prover-client"))
            .stdout(Stdio::piped())
            .arg("--socket")
            .arg(&sock)
            .args(args)
            .env(
                "MIDNIGHT_GPU_PROVER_BREAKER_STATE",
                dir.path().join("breaker"),
            )
            .env("MIDNIGHT_GPU_PROVER_THREADS", "2")
            .output()
            .unwrap();
        serde_json::from_slice(&o.stdout).unwrap()
    };
    let t = std::time::Instant::now();
    while client(&["health"])["ok"] != true {
        assert!(t.elapsed() < T, "daemon did not start");
        std::thread::sleep(Duration::from_millis(200));
    }
    let inp = input_file(dir.path(), "in.bin", 9);
    let out = dir.path().join("proof.bin");
    let (i, o) = (inp.to_str().unwrap(), out.to_str().unwrap());
    let r = client(&["prove", i, o, "--insecure-test-srs"]);
    assert_eq!(r["label"], "cpu", "{r}");
    assert_eq!(client(&["stop"])["ok"], true);
    assert!(daemon.0.wait().unwrap().success());
    assert!(!sock.exists(), "the socket file is removed at the stop");
    let r = client(&["prove", i, o, "--insecure-test-srs"]);
    assert_eq!(r["label"], "cpu-fallback", "{r}");
    let r = client(&["prove", i, o, "--no-fallback"]);
    assert_eq!(r["ok"], false);
    drop(daemon);
    assert!(!alive(pid), "the daemon {pid} outlived its test");
}
