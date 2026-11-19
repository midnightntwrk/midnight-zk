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

//! The client: sends requests to the daemon, and proves on the CPU
//! in-process when the daemon cannot serve.
//!
//! [`Client::prove`] tries the daemon first. When the daemon is absent,
//! refuses, is busy or returns an error, and CPU fallback is on, it calls the
//! fallback prover and labels the result [`Label::CpuFallback`].
//!
//! Circuit breaker: after `breaker_failures` consecutive daemon failures
//! within `breaker_window_s`, the client stops trying the daemon for
//! `breaker_cooldown_s` and writes one alert line to stderr (and runs
//! `alert_cmd` with that line, if set). The state lives in an owner-only file
//! so that it holds across client processes. A failure is a daemon that
//! cannot be reached, breaks the protocol, fails to prove or verify, or has
//! retired. `busy` and refusals caused by the request (input, output,
//! degraded, refused) are not failures; a served reply resets the count.

use std::{
    io::{BufRead, BufReader, Write},
    os::{
        fd::{AsRawFd, BorrowedFd},
        unix::{fs::OpenOptionsExt, net::UnixStream},
    },
    path::{Path, PathBuf},
    time::Duration,
};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{
    ClientConfig, Config, Error, ProverService, RequestOptions, ServedRelation,
    config::DeviceSelect,
    device::NoDevice,
    input, lock,
    protocol::{self, Request},
    report::Label,
};

/// The result of [`Client::prove`].
#[derive(Clone, Debug, PartialEq)]
pub struct Outcome {
    /// How the proof was produced.
    pub label: Label,
    /// The proof record (from the daemon, or from the in-process prover).
    pub record: Value,
    /// Why the daemon did not serve, when it did not.
    pub daemon_error: Option<String>,
}

/// Whether an error counts as a daemon failure for the breaker.
pub fn is_daemon_failure(e: &Error) -> bool {
    matches!(
        e,
        Error::Daemon(_) | Error::Prove(_) | Error::Verify | Error::Retired(_)
    )
}

fn error_of_reply(kind: &str, message: String) -> Error {
    match kind {
        "busy" => Error::Busy,
        "refused" => Error::Refused(message),
        "input" | "bad-request" => Error::Input(message),
        "output" => Error::Output(message),
        "prove" => Error::Prove(message),
        "verify" => Error::Verify,
        "degraded" => Error::Degraded(message),
        "retired" => Error::Retired(message),
        _ => Error::Daemon(message),
    }
}

/// Sends one request and reads the reply. `lock_fd` is passed with the
/// request as `SCM_RIGHTS`.
pub fn request(
    socket: &Path,
    req: &Request,
    lock_fd: Option<BorrowedFd<'_>>,
    timeout: Duration,
) -> Result<Value, Error> {
    let s = UnixStream::connect(socket)
        .map_err(|e| Error::Daemon(format!("cannot connect to the daemon: {}", e.kind())))?;
    let _ = s.set_read_timeout(Some(timeout));
    let _ = s.set_write_timeout(Some(Duration::from_secs(10)));
    let mut line = serde_json::to_vec(req)
        .map_err(|_| Error::Daemon("the request cannot be encoded".into()))?;
    line.push(b'\n');
    let w = match lock_fd {
        Some(fd) => lock::send_with_fd(&s, &line, fd.as_raw_fd()).and_then(|n| {
            let mut w = &s;
            w.write_all(&line[n..])
        }),
        None => {
            let mut w = &s;
            w.write_all(&line)
        }
    };
    // the reply is read even when the write failed: a daemon that refused
    // at once has written it already
    let mut reply = String::new();
    let r = BufReader::new(&s).read_line(&mut reply);
    if reply.trim().is_empty() {
        if let Err(e) = w {
            return Err(Error::Daemon(format!(
                "cannot send the request: {}",
                e.kind()
            )));
        }
        return Err(Error::Daemon(match r {
            Err(e) => format!("no reply: {}", e.kind()),
            Ok(_) => "the daemon closed the connection without a reply".into(),
        }));
    }
    serde_json::from_str(&reply).map_err(|_| Error::Daemon("the reply is not JSON".into()))
}

/// Sends a request and turns an error reply into an [`Error`].
pub fn request_ok(
    socket: &Path,
    req: &Request,
    lock_fd: Option<BorrowedFd<'_>>,
    timeout: Duration,
) -> Result<Value, Error> {
    #[cfg(test)]
    if let Some(reply) = crate::service::oracle_conformance::take_reply() {
        return reply;
    }
    let v = request(socket, req, lock_fd, timeout)?;
    match protocol::reply_error(&v) {
        None => Ok(v),
        Some(e) => Err(error_of_reply(&e.kind, e.message)),
    }
}

/// The persisted state of the breaker.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct BreakerState {
    /// Unix seconds of the consecutive failures inside the window.
    pub failures: Vec<u64>,
    /// While now is before this Unix second, the daemon is skipped.
    pub open_until: u64,
}

/// The client-side circuit breaker.
#[derive(Clone, Debug)]
pub struct Breaker {
    path: PathBuf,
    failures: u32,
    window_s: u64,
    cooldown_s: u64,
    /// The state of this process, used while the state file cannot be
    /// opened (the breaker still opens; the state is not shared).
    local: std::sync::Arc<std::sync::Mutex<BreakerState>>,
    /// The "not persisted" line was written.
    warned: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl Breaker {
    /// A breaker with its state at `path`.
    pub fn new(path: PathBuf, failures: u32, window_s: u64, cooldown_s: u64) -> Breaker {
        Breaker {
            path,
            failures: failures.max(1),
            window_s,
            cooldown_s,
            local: Default::default(),
            warned: Default::default(),
        }
    }

    /// Runs `f` on the state under an exclusive lock of the state file.
    fn update<T>(&self, f: impl FnOnce(&mut BreakerState) -> T) -> T {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o600)
            .open(&self.path);
        let Ok(mut file) = file else {
            // no state file: the breaker works for this process only (a
            // fixed text: the path is not repeated)
            if !self.warned.swap(true, std::sync::atomic::Ordering::Relaxed) {
                eprintln!(
                    "midnight-gpu-prover: the breaker state file cannot be opened; \
                     the breaker state is kept in this process only"
                );
            }
            let mut st = self.local.lock().unwrap_or_else(|e| e.into_inner());
            return f(&mut st);
        };
        // SAFETY: `flock` on an open descriptor.
        unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) };
        let mut text = String::new();
        let _ = std::io::Read::read_to_string(&mut file, &mut text);
        let mut st: BreakerState = serde_json::from_str(&text).unwrap_or_default();
        let out = f(&mut st);
        let _ = file.set_len(0);
        let _ = std::io::Seek::rewind(&mut file);
        let _ = file.write_all(serde_json::to_string(&st).unwrap_or_default().as_bytes());
        out
    }

    /// Whether the daemon may be tried at `now`.
    pub fn allows(&self, now: u64) -> bool {
        self.update(|s| now >= s.open_until)
    }

    /// Records a served reply.
    pub fn success(&self) {
        self.update(|s| s.failures.clear());
    }

    /// Records a failure at `now`. Returns the alert line when this failure
    /// opens the breaker.
    pub fn failure(&self, now: u64) -> Option<String> {
        let (n, w, c) = (self.failures, self.window_s, self.cooldown_s);
        self.update(|s| {
            s.failures.retain(|t| now.saturating_sub(*t) < w);
            s.failures.push(now);
            if s.failures.len() as u32 >= n {
                s.failures.clear();
                s.open_until = now + c;
                Some(format!(
                    "midnight-gpu-prover: ALERT: circuit breaker open: {n} consecutive daemon failures within {w} s; the daemon is skipped for {c} s and requests are proved on the CPU"
                ))
            } else {
                None
            }
        })
    }

    /// The state now.
    pub fn state(&self) -> BreakerState {
        self.update(|s| s.clone())
    }
}

fn now_s() -> u64 {
    protocol::unix_s() as u64
}

/// The fallback prover of a client.
pub type Fallback<'a> = &'a dyn Fn(&Path, &Path) -> Result<Value, Error>;

/// A client of one daemon.
pub struct Client {
    cfg: ClientConfig,
    breaker: Breaker,
    clock: Box<dyn Fn() -> u64 + Send + Sync>,
}

impl std::fmt::Debug for Client {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Client").field("cfg", &self.cfg).finish_non_exhaustive()
    }
}

impl Client {
    /// A client with the system clock.
    pub fn new(cfg: ClientConfig) -> Client {
        Client::with_clock(cfg, Box::new(now_s))
    }

    /// A client with an explicit clock (Unix seconds), for tests.
    pub fn with_clock(cfg: ClientConfig, clock: Box<dyn Fn() -> u64 + Send + Sync>) -> Client {
        let breaker = Breaker::new(
            cfg.breaker_path(),
            cfg.breaker_failures,
            cfg.breaker_window_s,
            cfg.breaker_cooldown_s,
        );
        Client {
            cfg,
            breaker,
            clock,
        }
    }

    /// The configuration.
    pub fn config(&self) -> &ClientConfig {
        &self.cfg
    }

    /// The breaker.
    pub fn breaker(&self) -> &Breaker {
        &self.breaker
    }

    /// Sends a request that is not `prove` (health, stats, evict, stop).
    pub fn send(&self, req: &Request) -> Result<Value, Error> {
        request_ok(
            &self.cfg.socket_path(),
            req,
            None,
            Duration::from_secs(self.cfg.reply_timeout_s),
        )
    }

    fn alert(&self, line: &str) {
        eprintln!("{line}");
        if let Some(cmd) = &self.cfg.alert_cmd
            && let Err(e) = std::process::Command::new(cmd).arg(line).status()
        {
            eprintln!(
                "midnight-gpu-prover: the alert command did not run: {}",
                e.kind()
            );
        }
    }

    /// Proves `input` into `output` through the daemon, or with `fallback`
    /// when the daemon cannot serve and CPU fallback is on. `lock_fd` is the
    /// caller's locked device-lock descriptor, passed to the daemon.
    pub fn prove(
        &self,
        input: &Path,
        output: &Path,
        zero_check: bool,
        lock_fd: Option<BorrowedFd<'_>>,
        fallback: Fallback<'_>,
    ) -> Result<Outcome, Error> {
        let now = (self.clock)();
        let daemon_error = if self.breaker.allows(now) {
            let req = Request::Prove {
                input: input.to_path_buf(),
                output: output.to_path_buf(),
                zero_check,
            };
            let timeout = Duration::from_secs(self.cfg.reply_timeout_s);
            match request_ok(&self.cfg.socket_path(), &req, lock_fd, timeout) {
                Ok(v) => {
                    self.breaker.success();
                    let record = v.get("record").cloned().unwrap_or(Value::Null);
                    let label = record
                        .get("label")
                        .and_then(|l| serde_json::from_value(l.clone()).ok())
                        .ok_or_else(|| Error::Daemon("the reply has no label".into()))?;
                    return Ok(Outcome {
                        label,
                        record,
                        daemon_error: None,
                    });
                }
                Err(e) => {
                    // the exchange may have taken up to the reply timeout:
                    // the failure is recorded at its end
                    if is_daemon_failure(&e)
                        && let Some(line) = self.breaker.failure((self.clock)())
                    {
                        self.alert(&line);
                    }
                    e
                }
            }
        } else {
            Error::Daemon("circuit breaker open".into())
        };
        if !self.cfg.cpu_fallback {
            return Err(daemon_error);
        }
        let record = fallback(input, output)?;
        Ok(Outcome {
            label: Label::CpuFallback,
            record,
            daemon_error: Some(daemon_error.to_string()),
        })
    }
}

/// Proves `input` into `output` on the CPU in-process: builds a service
/// with no device, proves, verifies and writes the proof owner-only. The
/// record's label is [`Label::CpuFallback`].
pub fn cpu_prove<R: ServedRelation>(
    relation: R,
    params: midnight_proofs::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>,
    cfg: &Config,
    input: &Path,
    output: &Path,
) -> Result<Value, Error> {
    let cfg = Config {
        device: DeviceSelect::Off,
        lock_path: None,
        ..cfg.clone()
    };
    let mut svc = ProverService::with_device(relation, params, cfg, Box::new(NoDevice))?;
    let bytes = input::read_input(input)?;
    let served = svc.prove(&bytes, RequestOptions::default())?;
    input::write_owner_only(output, &served.proof)?;
    let mut record =
        serde_json::to_value(&served.record).map_err(|e| Error::Prove(e.to_string()))?;
    record["label"] = serde_json::to_value(Label::CpuFallback).unwrap_or(Value::Null);
    Ok(record)
}

/// The usage text of a client binary.
pub const CLIENT_USAGE: &str =
    "usage: midnight-gpu-prover-client [--config FILE] [--socket PATH] COMMAND

commands:
  health                         state of the daemon
  stats                          start record and counters
  evict [--tables]               free the resident proving-key copies
  stop                           stop the daemon gracefully
  prove INPUT OUTPUT [--zero-check] [--lock PATH | --lock-fd N] [--no-fallback]
        [--srs FILE | --insecure-test-srs]
                                 prove through the daemon; on the CPU in-process
                                 when the daemon cannot serve

Prints one JSON line. Exit code 0 on success, 1 on an error, 2 on a usage error.";

/// The whole client binary for `relation` (the relation is used by the CPU
/// fallback). Returns the process exit code.
pub fn main<R: ServedRelation>(relation: R) -> i32 {
    crate::report::withhold_panic_messages();
    crate::device::warn_test_seed_build();
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run_cli(relation, &args) {
        Ok(v) => {
            println!("{v}");
            0
        }
        Err(CliError::Usage(m)) => {
            if !m.is_empty() {
                eprintln!("midnight-gpu-prover-client: {m}");
            }
            eprintln!("{CLIENT_USAGE}");
            2
        }
        Err(CliError::Failed(e)) => {
            println!("{}", protocol::error_reply(e.kind(), &e.to_string()));
            1
        }
    }
}

enum CliError {
    Usage(String),
    Failed(Error),
}

impl From<Error> for CliError {
    fn from(e: Error) -> Self {
        CliError::Failed(e)
    }
}

fn run_cli<R: ServedRelation>(relation: R, args: &[String]) -> Result<Value, CliError> {
    let u = |m: &str| CliError::Usage(m.to_string());
    let mut config = None;
    let mut socket = None;
    let mut rest = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--config" => {
                config = Some(PathBuf::from(it.next().ok_or(u("--config needs a value"))?))
            }
            "--socket" => {
                socket = Some(PathBuf::from(it.next().ok_or(u("--socket needs a value"))?))
            }
            "-h" | "--help" => return Err(u("")),
            _ => rest.push(a.clone()),
        }
    }
    let mut cc = ClientConfig::load(config.as_deref())?;
    if let Some(s) = &socket {
        cc.socket = Some(s.clone());
    }
    let client = Client::new(cc);
    let Some((cmd, opts)) = rest.split_first() else {
        return Err(u("no command"));
    };
    match (cmd.as_str(), opts) {
        // a full queue answers `busy` without reading: the daemon is alive
        ("health", []) => match client.send(&Request::Health {}) {
            Err(Error::Busy) => Ok(serde_json::json!({"ok": true, "state": "busy"})),
            r => Ok(r?),
        },
        ("stats", []) => Ok(client.send(&Request::Stats {})?),
        ("stop", []) => Ok(client.send(&Request::Stop {})?),
        ("evict", []) => Ok(client.send(&Request::Evict { tables: false })?),
        ("evict", [t]) if t == "--tables" => Ok(client.send(&Request::Evict { tables: true })?),
        ("prove", [inp, out, more @ ..]) => {
            let (mut zero_check, mut lock_path, mut lock_fd, mut srs, mut test_srs) =
                (false, None, None, None, false);
            let mut no_fallback = false;
            let mut it = more.iter();
            while let Some(a) = it.next() {
                match a.as_str() {
                    "--zero-check" => zero_check = true,
                    "--no-fallback" => no_fallback = true,
                    "--insecure-test-srs" => test_srs = true,
                    "--lock" => {
                        lock_path = Some(PathBuf::from(it.next().ok_or(u("--lock needs a value"))?))
                    }
                    "--srs" => {
                        srs = Some(PathBuf::from(it.next().ok_or(u("--srs needs a value"))?))
                    }
                    "--lock-fd" => {
                        let n: i32 = it
                            .next()
                            .and_then(|v| v.parse().ok())
                            .filter(|n| *n >= 0)
                            .ok_or(u("--lock-fd needs a descriptor number"))?;
                        lock_fd = Some(n);
                    }
                    _ => return Err(u("unknown argument")),
                }
            }
            if lock_path.is_some() && lock_fd.is_some() {
                return Err(u("--lock and --lock-fd exclude each other"));
            }
            // the lock is taken before the request and held until the reply
            let held = match &lock_path {
                Some(p) => Some(lock::lock_exclusive(p).map_err(|e| {
                    Error::Config(format!("cannot take the device lock: {}", e.kind()))
                })?),
                None => None,
            };
            // SAFETY: the caller states that descriptor `n` is open for the
            // life of this process (it is inherited, as with `flock` in a
            // shell).
            let fd = lock_fd.map(|n| unsafe { BorrowedFd::borrow_raw(n) });
            let fd = fd.or_else(|| {
                held.as_ref().map(|f| {
                    use std::os::fd::AsFd;
                    f.as_fd()
                })
            });
            let mut client = client;
            if no_fallback {
                client.cfg.cpu_fallback = false;
            }
            let fallback = |i: &Path, o: &Path| -> Result<Value, Error> {
                let cfg = Config::load(None)?;
                let params = crate::daemon::load_srs(&relation, &cfg, srs.as_deref(), test_srs)?;
                cpu_prove(relation.clone(), params, &cfg, i, o)
            };
            let out = client.prove(Path::new(inp), Path::new(out), zero_check, fd, &fallback)?;
            drop(held);
            Ok(serde_json::json!({
                "ok": true,
                "label": out.label,
                "daemon_error": out.daemon_error,
                "record": out.record,
            }))
        }
        _ => Err(u("unknown command or arguments")),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };

    use super::*;

    #[test]
    fn breaker_opens_after_n_failures_in_window_and_cools_down() {
        let dir = tempfile::tempdir().unwrap();
        let b = Breaker::new(dir.path().join("b"), 3, 600, 600);
        assert!(b.allows(1000));
        assert!(b.failure(1000).is_none());
        assert!(b.failure(1100).is_none());
        let line = b.failure(1200).expect("third failure opens the breaker");
        assert!(line.contains("ALERT"));
        assert!(!b.allows(1300));
        assert!(!b.allows(1799));
        assert!(b.allows(1800));
        // the state survives a new breaker on the same file (a new process)
        let b2 = Breaker::new(dir.path().join("b"), 3, 600, 600);
        assert_eq!(b2.state().open_until, 1800);
        use std::os::unix::fs::MetadataExt;
        assert_eq!(
            std::fs::metadata(dir.path().join("b")).unwrap().mode() & 0o777,
            0o600
        );
    }

    #[test]
    fn breaker_counts_only_failures_inside_the_window_and_resets_on_success() {
        let dir = tempfile::tempdir().unwrap();
        let b = Breaker::new(dir.path().join("b"), 3, 600, 600);
        b.failure(0);
        b.failure(100);
        // 700 s later the first two are outside the window
        assert!(b.failure(800).is_none());
        assert!(b.failure(900).is_none());
        b.success();
        assert!(b.failure(950).is_none());
        assert!(b.failure(960).is_none());
        assert!(b.failure(970).is_some());
    }

    #[test]
    fn absent_daemon_falls_back_and_opens_the_breaker() {
        // the alert starts a child process
        let _g = crate::lock::tests::spawn_guard();
        let dir = tempfile::tempdir().unwrap();
        let cfg = ClientConfig {
            socket: Some(dir.path().join("none.sock")),
            breaker_state: Some(dir.path().join("b")),
            alert_cmd: Some(dir.path().join("no-such-alert-program")),
            ..ClientConfig::default()
        };
        let t = Arc::new(AtomicU64::new(10_000));
        let tc = t.clone();
        let c = Client::with_clock(cfg.clone(), Box::new(move || tc.load(Ordering::SeqCst)));
        let calls = std::cell::Cell::new(0);
        let fb = |_: &Path, _: &Path| {
            calls.set(calls.get() + 1);
            Ok(serde_json::json!({"label": "cpu-fallback"}))
        };
        for i in 0..3 {
            let o = c.prove(Path::new("/in"), Path::new("/out"), false, None, &fb).unwrap();
            assert_eq!(o.label, Label::CpuFallback);
            assert!(o.daemon_error.unwrap().contains("connect"));
            t.fetch_add(1, Ordering::SeqCst);
            assert_eq!(c.breaker().state().open_until > 0, i == 2);
        }
        // open: the daemon is not tried
        let o = c.prove(Path::new("/in"), Path::new("/out"), false, None, &fb).unwrap();
        assert!(o.daemon_error.unwrap().contains("breaker open"));
        assert_eq!(calls.get(), 4);
        // without fallback the error is returned
        let c = Client::with_clock(
            ClientConfig {
                cpu_fallback: false,
                breaker_state: Some(dir.path().join("b2")),
                ..cfg
            },
            Box::new(|| 0),
        );
        assert!(matches!(
            c.prove(Path::new("/i"), Path::new("/o"), false, None, &fb),
            Err(Error::Daemon(_))
        ));
    }

    #[test]
    fn failure_classes() {
        assert!(is_daemon_failure(&Error::Daemon("x".into())));
        assert!(is_daemon_failure(&Error::Verify));
        assert!(is_daemon_failure(&Error::Retired("x".into())));
        assert!(!is_daemon_failure(&Error::Busy));
        assert!(!is_daemon_failure(&Error::Input("x".into())));
        assert!(!is_daemon_failure(&Error::Degraded("x".into())));
        assert_eq!(error_of_reply("busy", String::new()), Error::Busy);
        assert_eq!(error_of_reply("verify", String::new()), Error::Verify);
    }
}
