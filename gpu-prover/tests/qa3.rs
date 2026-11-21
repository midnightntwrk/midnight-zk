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

//! Regression tests of QA fix list 3: one test per item. Each failed on the
//! code before its fix.

mod common;

use std::{
    io::Read,
    os::unix::net::UnixStream,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{Arc, atomic::Ordering::SeqCst},
    thread::JoinHandle,
    time::{Duration, Instant},
};

use common::*;
use midnight_gpu_prover::{
    Config, Error, RequestOptions, client,
    daemon::{self, ServeEnd},
    device::{Device, NoDevice, Phases},
    input::SecretBytes,
    protocol::Request,
    report::Label,
    service::Retirement,
};

const T: Duration = Duration::from_secs(300);

/// An in-process daemon on a fresh socket.
struct Daemon {
    socket: PathBuf,
    handle: Option<JoinHandle<ServeEnd>>,
}

impl Daemon {
    fn start(dir: &Path, cfg: Config, dev: Box<dyn Device>) -> Daemon {
        let socket = dir.join("q.sock");
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

    /// Waits until `n` requests hold queue places (a full queue answers
    /// `busy`): the order of the requests is then fixed, whatever the load.
    fn wait_places(&self, n: u64) {
        let t = Instant::now();
        loop {
            let full = match client::request(&self.socket, &Request::Health {}, None, T) {
                Ok(h) => h["error"]["kind"] == "busy" || h["queued"].as_u64().unwrap_or(0) >= n,
                Err(Error::Busy) => true,
                Err(e) => panic!("health: {e}"),
            };
            if full {
                return;
            }
            assert!(
                t.elapsed() < Duration::from_secs(30),
                "{n} places not taken"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    fn end(mut self) -> ServeEnd {
        self.handle.take().unwrap().join().unwrap()
    }
}

fn prove_req(input: &Path, output: &Path) -> Request {
    Request::Prove {
        input: input.to_path_buf(),
        output: output.to_path_buf(),
        zero_check: false,
    }
}

fn input() -> SecretBytes {
    SecretBytes::new(midnight_gpu_prover::example::example_input(3))
}

/// A child process that is killed and reaped when dropped.
struct Reaped(std::process::Child);

impl Drop for Reaped {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Runs the daemon binary with `env` and `args`; returns its exit code and
/// stderr, or `None` when it still runs after `limit`.
fn run_daemon(env: &[(&str, &str)], args: &[&str], limit: Duration) -> Option<(i32, String)> {
    let dir = tempfile::tempdir().unwrap();
    let err = dir.path().join("stderr");
    let mut c = Command::new(env!("CARGO_BIN_EXE_midnight-gpu-proverd"));
    c.args(args)
        .arg("--socket")
        .arg(dir.path().join("d.sock"))
        .env("MIDNIGHT_GPU_PROVER_DEVICE", "off")
        .env("MIDNIGHT_GPU_PROVER_WSL", "off")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&err).unwrap());
    for (k, v) in env {
        c.env(k, v);
    }
    let mut child = Reaped(c.spawn().unwrap());
    let t = Instant::now();
    while t.elapsed() < limit {
        if let Some(st) = child.0.try_wait().unwrap() {
            let mut s = String::new();
            std::fs::File::open(&err).unwrap().read_to_string(&mut s).unwrap();
            return Some((st.code().unwrap_or(-1), s));
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    None
}

/// ORACLE-12 (GPU-042): k above max_k is refused before any SRS load. With
/// no SRS configured, the refusal names max_k, not the missing SRS.
#[test]
fn max_k_is_checked_before_the_srs_load() {
    let r = run_daemon(
        &[("MIDNIGHT_GPU_PROVER_MAX_K", "1")],
        &[],
        Duration::from_secs(60),
    );
    let (code, err) = r.expect("the daemon did not exit");
    assert_eq!(code, 3, "{err}");
    assert!(err.contains("above max_k = 1"), "{err}");
    assert!(!err.contains("no SRS"), "{err}");
}

/// ORACLE-09 (GPU-046): while both queue places are taken, a connection that
/// sends nothing gets `busy` at once.
#[test]
fn silent_connection_on_a_full_queue_gets_busy_at_once() {
    let dir = tempfile::tempdir().unwrap();
    let f = Fake {
        delay: Duration::from_secs(4),
        ..Fake::default()
    };
    let d = Daemon::start(dir.path(), config(), Box::new(f));
    let mut handles = Vec::new();
    for i in 0..2u64 {
        let (inp, out) = (
            input_file(dir.path(), &format!("i{i}"), i),
            dir.path().join(format!("o{i}")),
        );
        let s = d.socket.clone();
        handles.push(std::thread::spawn(move || {
            client::request(&s, &prove_req(&inp, &out), None, T).unwrap()
        }));
        d.wait_places(i + 1);
    }
    let mut c = UnixStream::connect(&d.socket).unwrap();
    c.set_read_timeout(Some(Duration::from_secs(1))).unwrap();
    let t = Instant::now();
    let mut buf = String::new();
    let _ = c.read_to_string(&mut buf);
    assert!(
        t.elapsed() < Duration::from_secs(1),
        "no reply at once: {buf:?}"
    );
    let v: serde_json::Value = serde_json::from_str(buf.trim()).unwrap();
    assert_eq!(v["error"]["kind"], "busy", "{v}");
    for h in handles {
        h.join().unwrap();
    }
    let _ = d.ask(&Request::Stop {});
    d.end();
}

/// ORACLE-11 (GPU-018): a release daemon refuses to start when a test
/// switch is set, before it loads the SRS.
#[test]
fn release_daemon_refuses_test_switches() {
    if cfg!(feature = "test-seed") {
        // a test-seed build takes the switches; this checks the release build
        return;
    }
    for var in daemon::TEST_SWITCH_VARS {
        let r = run_daemon(
            &[(var, "msm:launch")],
            &["--insecure-test-srs"],
            Duration::from_secs(60),
        );
        let (code, err) = r.unwrap_or_else(|| panic!("{var}: the daemon kept serving"));
        assert_eq!(code, 2, "{var}: {err}");
        assert!(
            err.contains("test switches are not taken by a release build"),
            "{err}"
        );
    }
}

/// ORACLE-02 (GPU-037/061): a request whose client hung up or whose lease
/// was lost has its device phases withdrawn: the proof finishes on the CPU,
/// one fallback is counted and the erasure still runs.
#[test]
fn cancel_withdraws_the_device_and_keeps_the_erasure() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        ..Fake::default()
    };
    let log = f.log.clone();
    let mut s = service(config(), Box::new(f));
    let opts = RequestOptions {
        cancel: Some(Arc::new(|| true)),
        ..RequestOptions::default()
    };
    let r = s.prove(&input(), opts).unwrap().record;
    assert_eq!(log.revokes.load(SeqCst), 1);
    assert_eq!(log.ends.load(SeqCst), 1);
    assert_eq!(r.fallback_count, 1);
    assert_eq!(r.label, Label::GpuDegraded);
    // a request that keeps its client is untouched
    let opts = RequestOptions {
        cancel: Some(Arc::new(|| false)),
        ..RequestOptions::default()
    };
    let r = s.prove(&input(), opts).unwrap().record;
    assert_eq!((r.fallback_count, r.label), (0, Label::Gpu));
    assert_eq!(log.revokes.load(SeqCst), 1);
}

/// ORACLE-02, lease side: removing or replacing the lock file loses the
/// lease.
#[test]
fn lease_is_lost_when_the_lock_file_is_replaced() {
    use std::os::fd::AsFd;
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("dev.lock");
    let held = midnight_gpu_prover::lock::lock_exclusive(&p).unwrap();
    let fd = held.as_fd().try_clone_to_owned().unwrap();
    let lease = midnight_gpu_prover::lock::Lease::validate(&p, Some(fd)).unwrap();
    let lost = lease.watch();
    assert!(!lost());
    std::fs::remove_file(&p).unwrap();
    std::fs::write(&p, b"").unwrap();
    assert!(lost());
}

/// ORACLE-03 (GPU-050): a request above a memory bound is answered, then the
/// service retires as restartable (exit 3), and the first request of a
/// process is labelled cold.
#[test]
fn memory_bound_overrun_replies_then_retires_restartable() {
    let cfg = Config {
        max_host_hwm_mib: 1,
        ..config()
    };
    let mut s = service(cfg.clone(), Box::new(NoDevice));
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(r.cold);
    assert!(matches!(s.retirement(), Some(Retirement::Bound(_))));
    assert!(matches!(
        s.prove(&input(), RequestOptions::default()),
        Err(Error::Retired(_))
    ));
    // through the daemon: the reply goes out, then the serve loop ends Bound
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), cfg, Box::new(NoDevice));
    let inp = input_file(dir.path(), "in", 1);
    let r = d.ask(&prove_req(&inp, &dir.path().join("out")));
    assert_eq!(r["ok"], true, "{r}");
    assert_eq!(r["record"]["cold"], true);
    assert!(matches!(d.end(), ServeEnd::Bound(_)));
}

/// ORACLE-05 (GPU-036): the record's wipe carries the non-zero region and
/// check failure counts.
#[test]
fn wipe_record_has_nonzero_regions_and_check_failures() {
    let mut s = service(config(), Box::new(NoDevice));
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    let v = serde_json::to_value(&r).unwrap();
    assert_eq!(v["wipe"]["nonzero_regions"], 0, "{v}");
    assert_eq!(v["wipe"]["check_failures"], 0, "{v}");
    assert_eq!(v["wipe"]["erasure_failures"], 0, "{v}");
}

/// A3: the reply carries the request's declines by phase and reason; a
/// below-min-k MSM is a decline, not a fallback, and `coset` is no phase.
#[test]
fn below_min_k_msm_shows_in_the_reply_as_a_decline() {
    let fake = Fake {
        shape: Some(Fake::big_shape()),
        declines: vec![("msm", "below-min-k", 1)],
        ..Fake::default()
    };
    let mut s = service(config(), Box::new(fake));
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    let v = serde_json::to_value(&r).unwrap();
    let d = v["declines"].as_array().expect("declines in the reply");
    assert!(
        d.iter()
            .any(|f| f["phase"] == "msm" && f["reason"] == "below-min-k" && f["count"] == 1),
        "{v}"
    );
    assert_eq!(v["fallback_count"], 0, "{v}");
    assert!(!v["configured"].to_string().contains("coset"), "{v}");
}

/// Minor 9: only a verified, returned proof counts as served in the daemon
/// (the service's count: `service::tests::served_counts_only_verified_proofs`).
#[test]
fn served_counts_only_verified_replies() {
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), config(), Box::new(NoDevice));
    let bad = dir.path().join("bad");
    std::fs::write(&bad, [0xffu8; 96]).unwrap();
    std::fs::set_permissions(&bad, std::os::unix::fs::PermissionsExt::from_mode(0o600)).unwrap();
    let r = d.ask(&prove_req(&bad, &dir.path().join("o")));
    assert_eq!(r["ok"], false);
    assert_eq!(d.ask(&Request::Stats {})["served"], 0);
    let _ = d.ask(&Request::Stop {});
    d.end();
}

/// Minor 11: the start record names the SHA-256 of the running binary.
#[test]
fn start_record_has_the_binary_sha256() {
    let s = service(config(), Box::new(NoDevice));
    let h = s.start_record().binary_sha256.clone().expect("no binary hash");
    assert_eq!(h.len(), 64);
    assert!(h.bytes().all(|b| b.is_ascii_hexdigit()));
}

/// Minors 13 and 14: an error reply to a prove names its request id, and a
/// request queued behind a retirement gets `daemon-lost`, not `busy`.
#[test]
fn queued_request_at_retirement_gets_daemon_lost() {
    let dir = tempfile::tempdir().unwrap();
    let f = Fake {
        delay: Duration::from_secs(2),
        wipe_fails: true,
        ..Fake::default()
    };
    let d = Daemon::start(dir.path(), config(), Box::new(f));
    let mut handles = Vec::new();
    for i in 0..2u64 {
        let (inp, out) = (
            input_file(dir.path(), &format!("i{i}"), i),
            dir.path().join(format!("o{i}")),
        );
        let s = d.socket.clone();
        handles.push(std::thread::spawn(move || {
            client::request(&s, &prove_req(&inp, &out), None, T).unwrap()
        }));
        d.wait_places(i + 1);
    }
    let r: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    assert_eq!(r[0]["error"]["kind"], "retired", "{}", r[0]);
    assert_eq!(r[0]["request"], 1, "{}", r[0]);
    assert_eq!(r[1]["error"]["kind"], "daemon-lost", "{}", r[1]);
    assert!(matches!(d.end(), ServeEnd::Retired(_)));
}

/// r13 BLOCKING 1: on a native host the admission makes the device context
/// and reads the free memory before it picks the device rung. A device that
/// reports the whole device as free before its context exists (another
/// process may hold that memory) does not get the request onto the device.
#[test]
fn cold_admission_reads_free_memory_after_activation() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        lazy: true,
        free: 1 << 20,
        ..Fake::default()
    };
    let log = f.log.clone();
    let mut cfg = config();
    cfg.wait_s = 0.0;
    let mut s = service(cfg, Box::new(f));
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(log.activations.load(SeqCst) >= 1);
    assert!(r.admitted.is_empty(), "{:?}", r.admitted);
    assert_eq!(r.label, Label::Cpu, "{:?}", r.degraded_reasons);
}

/// r13 BLOCKING 3: a request with no device phase reports no device peak,
/// whatever the device layer still holds from an earlier request, and does
/// not trip the peak bound.
#[test]
fn cpu_only_request_reports_no_device_peak() {
    let f = Fake {
        take: Some(Phases::NONE),
        peak: 5 << 30,
        ..Fake::default()
    };
    let mut cfg = config();
    cfg.max_device_peak_mib = 1024;
    let mut s = service(cfg, Box::new(f));
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(r.admitted.is_empty());
    assert_eq!(r.device_peak_bytes, 0);
    assert!(s.retirement().is_none());
}

/// QA4 ORACLE-19: the daemon counts a proof as served once its output file
/// is written. A verified proof whose output cannot be written is not
/// served, in `stats` and in `health`.
#[test]
fn served_is_counted_at_the_output_boundary() {
    let dir = tempfile::tempdir().unwrap();
    let d = Daemon::start(dir.path(), config(), Box::new(NoDevice));
    let inp = input_file(dir.path(), "in", 2);
    let r = d.ask(&prove_req(&inp, &dir.path().join("no-such-dir").join("p")));
    assert_eq!(r["ok"], false, "{r}");
    assert_eq!(r["error"]["kind"], "output", "{r}");
    assert_eq!(d.ask(&Request::Stats {})["served"], 0);
    assert_eq!(d.ask(&Request::Health {})["served"], 0);
    let r = d.ask(&prove_req(&inp, &dir.path().join("p")));
    assert_eq!(r["ok"], true, "{r}");
    assert_eq!(d.ask(&Request::Stats {})["served"], 1);
    let _ = d.ask(&Request::Stop {});
    d.end();
}

/// QA4 ORACLE-09: a refused connection is answered `busy`, shut down and
/// closed; nothing of what the client sends afterwards is read.
#[test]
fn busy_refusal_reads_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let f = Fake {
        delay: Duration::from_secs(3),
        ..Fake::default()
    };
    let d = Daemon::start(dir.path(), config(), Box::new(f));
    let mut handles = Vec::new();
    for i in 0..2u64 {
        let (inp, out) = (
            input_file(dir.path(), &format!("i{i}"), i),
            dir.path().join(format!("o{i}")),
        );
        let s = d.socket.clone();
        handles.push(std::thread::spawn(move || {
            client::request(&s, &prove_req(&inp, &out), None, T).unwrap()
        }));
        d.wait_places(i + 1);
    }
    let mut c = UnixStream::connect(&d.socket).unwrap();
    c.set_read_timeout(Some(Duration::from_secs(2))).unwrap();
    let mut line = String::new();
    std::io::BufRead::read_line(&mut std::io::BufReader::new(&c), &mut line).unwrap();
    assert!(line.contains("busy"), "{line}");
    // the daemon closed its end: a later write fails (nothing reads it)
    std::thread::sleep(Duration::from_millis(50));
    let w = (0..64).try_for_each(|_| std::io::Write::write_all(&mut c, &[b'x'; 4096]));
    assert!(w.is_err(), "the daemon still reads a refused connection");
    for h in handles {
        h.join().unwrap();
    }
    let _ = d.ask(&Request::Stop {});
    d.end();
}

/// QA4 ORACLE-03: the memory bounds are checked on an acceptance-mode
/// degraded outcome too: the error goes out, then the service retires.
#[test]
fn bound_is_checked_on_a_degraded_outcome() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        fallbacks: 1,
        peak: 5 << 30,
        ..Fake::default()
    };
    let mut cfg = config();
    cfg.mode = midnight_gpu_prover::config::RunMode::Acceptance;
    cfg.max_device_peak_mib = 1024;
    let mut s = service(cfg, Box::new(f));
    let e = s.prove(&input(), RequestOptions::default()).unwrap_err();
    assert!(matches!(e, Error::Degraded(_)), "{e}");
    assert!(matches!(s.retirement(), Some(Retirement::Bound(_))));
}

/// QA4 ORACLE-02: the lease is lost when its open file description is
/// unlocked on the same inode (the path still names the locked file).
#[test]
fn lease_is_lost_when_its_descriptor_is_unlocked() {
    use std::os::fd::{AsFd, AsRawFd};
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("dev.lock");
    let held = midnight_gpu_prover::lock::lock_exclusive(&p).unwrap();
    let fd = held.as_fd().try_clone_to_owned().unwrap();
    let lease = midnight_gpu_prover::lock::Lease::validate(&p, Some(fd)).unwrap();
    let lost = lease.watch();
    assert!(!lost());
    // the holder unlocks the shared description, and another process
    // takes the lock
    // SAFETY: `flock` on an open descriptor.
    unsafe { libc::flock(held.as_raw_fd(), libc::LOCK_UN) };
    let other = midnight_gpu_prover::lock::lock_exclusive(&p).unwrap();
    assert!(lost());
    drop(other);
}

/// GPU-085: the label follows the fallback reasons. Every call declined
/// below the size threshold is `cpu`; some calls served and others
/// declined below the threshold is `gpu`; an injected device fault is
/// `gpu-degraded`. Expected declines are not fallbacks.
#[test]
fn label_follows_the_fallback_reasons() {
    let run = |f: Fake| {
        let mut s = service(config(), Box::new(f));
        s.prove(&input(), RequestOptions::default()).unwrap().record
    };
    let r = run(Fake {
        shape: Some(Fake::big_shape()),
        no_calls: true,
        declines: vec![("msm", "below-min-k", 6), ("fft", "below-min-k", 9)],
        ..Fake::default()
    });
    assert!(!r.admitted.is_empty());
    assert_eq!(r.label, Label::Cpu, "{:?}", r.degraded_reasons);
    assert_eq!(r.fallback_count, 0);
    let r = run(Fake {
        shape: Some(Fake::big_shape()),
        declines: vec![("fft", "below-min-k", 2)],
        ..Fake::default()
    });
    assert_eq!(r.label, Label::Gpu, "{:?}", r.degraded_reasons);
    assert_eq!(r.fallback_count, 0);
    let r = run(Fake {
        shape: Some(Fake::big_shape()),
        fallbacks: 1,
        ..Fake::default()
    });
    assert_eq!(r.label, Label::GpuDegraded);
    assert_eq!(r.fallback_count, 1);
}

/// GPU-075: with a state file that cannot be opened, the breaker still
/// counts failures in this process and opens after three.
#[test]
fn breaker_opens_without_a_state_file() {
    let dir = tempfile::tempdir().unwrap();
    let b = client::Breaker::new(dir.path().join("no-such-dir").join("b"), 3, 600, 600);
    assert!(b.failure(100).is_none());
    assert!(b.failure(110).is_none());
    assert!(b.failure(120).is_some(), "three failures open the breaker");
    assert!(!b.allows(130));
}

/// GPU-050: the first served proof is cold, also when a request before it
/// failed; the next one is not.
#[test]
fn cold_is_the_first_served_proof() {
    let f = Fake {
        shape: Some(Fake::big_shape()),
        ..Fake::default()
    };
    let mut cfg = config();
    cfg.mode = midnight_gpu_prover::config::RunMode::Acceptance;
    let mut s = service(cfg, Box::new(f));
    // a client that hung up: the request fails in acceptance mode
    let gone = RequestOptions {
        cancel: Some(Arc::new(|| true)),
        ..RequestOptions::default()
    };
    assert!(matches!(s.prove(&input(), gone), Err(Error::Degraded(_))));
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(r.cold, "the first served proof is cold");
    let r = s.prove(&input(), RequestOptions::default()).unwrap().record;
    assert!(!r.cold);
}
