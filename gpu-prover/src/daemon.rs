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

//! The daemon: one [`ProverService`] on a local Unix socket.
//!
//! - The socket is created with mode 0600 and only peers with the daemon's uid
//!   are served.
//! - An acceptor thread takes connections. Each connection gets a reader thread
//!   (at most [`MAX_READERS`]; above that, `busy` at once) that reads one
//!   request line within the read deadline. `health` and `stop` are answered by
//!   the reader. A queued request takes one of [`QUEUE_PLACES`] places or gets
//!   `busy` at once; a slow client therefore holds no queue place while it
//!   writes.
//! - The worker (the thread that calls [`serve`]) owns the service and serves
//!   queued requests in order.
//! - A `stop` request, `SIGTERM` or `SIGINT` stops the daemon gracefully:
//!   queued requests are served, new ones get `busy`, the socket file is
//!   removed.
//! - When the service retires (an erasure not confirmed), the daemon replies
//!   with the error and exits; it takes no further witness.
//!
//! See [`crate::protocol`] for the wire format.

use std::{
    io::Write,
    os::{
        fd::OwnedFd,
        unix::{
            fs::PermissionsExt,
            net::{UnixListener, UnixStream},
        },
    },
    path::{Path, PathBuf},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering::SeqCst},
        mpsc,
    },
    time::{Duration, Instant},
};

use serde_json::{Value, json};

use crate::{
    Config, Error, ProverService, RequestOptions, ServedRelation, input,
    lock::{self, Lease},
    protocol::{self, MAX_REQUEST, QUEUE_PLACES, QueueRecord, Request},
    service::Retirement,
};

/// Most connections read at the same time.
pub const MAX_READERS: usize = 8;

/// Default read deadline of a request line.
pub const READ_DEADLINE: Duration = Duration::from_secs(10);

static SIGNALLED: AtomicBool = AtomicBool::new(false);

extern "C" fn on_signal(_: libc::c_int) {
    SIGNALLED.store(true, SeqCst);
}

/// Installs `SIGTERM` and `SIGINT` handlers that request a graceful stop.
pub fn install_signal_handlers() {
    // SAFETY: the handler only stores to an atomic, which is
    // async-signal-safe.
    unsafe {
        libc::signal(libc::SIGTERM, on_signal as *const () as libc::sighandler_t);
        libc::signal(libc::SIGINT, on_signal as *const () as libc::sighandler_t);
    }
}

/// How [`serve`] ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServeEnd {
    /// A stop request or signal.
    Stopped,
    /// The service retired because an erasure was not confirmed; the text
    /// says why. The process must not take more witness data (exit 4).
    Retired(String),
    /// The service retired because a request went past a configured memory
    /// bound; the text says why. A fresh process may serve (exit 3, so that
    /// the supervisor restarts it).
    Bound(String),
}

/// State the reader threads share with the worker.
struct Shared {
    stop: AtomicBool,
    places: AtomicUsize,
    readers: AtomicUsize,
    proving: AtomicBool,
    served: AtomicU64,
    retired: Mutex<Option<String>>,
    started: Instant,
    health: Value,
}

impl Shared {
    fn stopping(&self) -> bool {
        self.stop.load(SeqCst) || SIGNALLED.load(SeqCst)
    }

    fn health(&self) -> Value {
        let state = if self.retired.lock().unwrap().is_some() {
            "retired"
        } else if self.stopping() {
            "stopping"
        } else if self.proving.load(SeqCst) {
            "proving"
        } else {
            "ready"
        };
        let mut h = self.health.clone();
        h["ok"] = json!(true);
        h["state"] = json!(state);
        h["queued"] = json!(self.places.load(SeqCst));
        h["served"] = json!(self.served.load(SeqCst));
        h["uptime_s"] = json!(self.started.elapsed().as_secs_f64());
        h["pid"] = json!(std::process::id());
        h
    }
}

struct Job {
    req: Request,
    stream: UnixStream,
    fd: Option<OwnedFd>,
    accepted: Instant,
}

/// Binds the socket: mode 0600, in a directory that exists. A stale socket
/// file (no daemon answers on it) is replaced; a live one is an error.
pub fn bind(path: &Path) -> Result<UnixListener, Error> {
    if path.exists() {
        if UnixStream::connect(path).is_ok() {
            return Err(Error::Refused(format!(
                "a daemon already serves {}",
                path.display()
            )));
        }
        std::fs::remove_file(path)
            .map_err(|e| Error::Config(format!("stale socket {}: {e}", path.display())))?;
    }
    // The mode is set right after the bind. The process umask is not
    // changed (it is process-wide). A connection made in the window between
    // bind and chmod is still refused unless its peer has the daemon's uid.
    let l = UnixListener::bind(path)
        .map_err(|e| Error::Config(format!("bind {}: {e}", path.display())))?;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
        .map_err(|e| Error::Config(format!("chmod {}: {e}", path.display())))?;
    Ok(l)
}

fn write_reply(s: &UnixStream, v: &Value) {
    let _ = s.set_write_timeout(Some(Duration::from_secs(10)));
    let mut w = s;
    let _ = writeln!(w, "{v}");
    let _ = s.shutdown(std::net::Shutdown::Both);
}

fn log(event: &str, v: &Value) {
    eprintln!("{}", json!({"event": event, "data": v}));
}

/// Reads one request line and at most one passed descriptor within
/// `deadline`. Bytes after the newline are ignored.
fn read_request(s: &UnixStream, deadline: Duration) -> Result<(String, Option<OwnedFd>), String> {
    let end = Instant::now() + deadline;
    let mut buf = Vec::new();
    let mut fd = None;
    let mut chunk = [0u8; 4096];
    loop {
        let left = end.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err("no request line within the deadline".into());
        }
        let _ = s.set_read_timeout(Some(left));
        match lock::recv_with_fd(s, &mut chunk) {
            Ok((0, _)) => {
                return Err("the client closed the connection before a request line".into());
            }
            Ok((n, f)) => {
                if fd.is_none() {
                    fd = f;
                }
                buf.extend_from_slice(&chunk[..n]);
                if let Some(i) = buf.iter().position(|b| *b == b'\n') {
                    buf.truncate(i);
                    break;
                }
                if buf.len() > MAX_REQUEST {
                    return Err("request line too long".into());
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => return Err("no request line within the deadline".into()),
        }
    }
    let line = String::from_utf8(buf).map_err(|_| "request line is not UTF-8".to_string())?;
    Ok((line, fd))
}

fn reader(s: UnixStream, shared: Arc<Shared>, tx: mpsc::Sender<Job>, deadline: Duration) {
    let accepted = Instant::now();
    let (line, fd) = match read_request(&s, deadline) {
        Ok(x) => x,
        Err(m) => return write_reply(&s, &protocol::error_reply("bad-request", &m)),
    };
    let req: Request = match serde_json::from_str(&line) {
        Ok(r) => r,
        Err(_) => {
            return write_reply(
                &s,
                &protocol::error_reply("bad-request", "not a valid request"),
            );
        }
    };
    match req {
        Request::Health {} => write_reply(&s, &shared.health()),
        Request::Stop {} => {
            shared.stop.store(true, SeqCst);
            write_reply(&s, &json!({"ok": true, "state": "stopping"}));
        }
        _ => {
            if shared.stopping() {
                return write_reply(&s, &protocol::error_reply("busy", "the daemon is stopping"));
            }
            if shared.places.fetch_add(1, SeqCst) >= QUEUE_PLACES {
                shared.places.fetch_sub(1, SeqCst);
                return write_reply(&s, &protocol::busy_reply());
            }
            if let Err(mpsc::SendError(j)) = tx.send(Job {
                req,
                stream: s,
                fd,
                accepted,
            }) {
                shared.places.fetch_sub(1, SeqCst);
                write_reply(
                    &j.stream,
                    &protocol::error_reply("busy", "the daemon is stopping"),
                );
            }
        }
    }
}

fn refuse_now(s: UnixStream, reply: Value) {
    let _ = s.set_write_timeout(Some(Duration::from_secs(1)));
    let mut w = &s;
    let _ = writeln!(w, "{reply}");
    // nothing of the request is read: the connection is shut down and
    // closed at once
    let _ = s.shutdown(std::net::Shutdown::Both);
}

fn acceptor(l: UnixListener, shared: Arc<Shared>, tx: mpsc::Sender<Job>, deadline: Duration) {
    let _ = l.set_nonblocking(true);
    let me = lock::own_uid();
    while !shared.stopping() {
        match l.accept() {
            Ok((s, _)) => {
                let _ = s.set_nonblocking(false);
                if lock::peer_uid(&s) != Some(me) {
                    refuse_now(
                        s,
                        protocol::error_reply("refused", "peer is not the daemon's user"),
                    );
                    continue;
                }
                // both queue places taken: busy at once, nothing is read
                if shared.places.load(SeqCst) >= QUEUE_PLACES {
                    refuse_now(s, protocol::busy_reply());
                    continue;
                }
                if shared.readers.fetch_add(1, SeqCst) >= MAX_READERS {
                    shared.readers.fetch_sub(1, SeqCst);
                    refuse_now(s, protocol::busy_reply());
                    continue;
                }
                let (sh, tx) = (shared.clone(), tx.clone());
                std::thread::spawn(move || {
                    reader(s, sh.clone(), tx, deadline);
                    sh.readers.fetch_sub(1, SeqCst);
                });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(_) => std::thread::sleep(Duration::from_millis(20)),
        }
    }
}

/// `served`: the proofs the daemon has written to their output files.
fn handle<R: ServedRelation>(svc: &mut ProverService<R>, job: &mut Job, served: u64) -> Value {
    match &job.req {
        Request::Stats {} => json!({
            "ok": true,
            "start": svc.start_record(),
            // the daemon's count: a proof is served once its output file is
            // written (the service counts proofs it returns)
            "served": served,
            "held": svc.held(),
        }),
        Request::Evict { tables } => json!({"ok": true, "evicted_bytes": svc.evict(*tables)}),
        Request::Prove {
            input,
            output,
            zero_check,
        } => {
            let (lease, lease_refused) = match &svc.config().lock_path {
                Some(p) => match Lease::validate(p, job.fd.take()) {
                    Ok(l) => (Some(l), None),
                    Err(e) => (None, Some(e.as_str())),
                },
                None => (None, None),
            };
            // the device phases stop when the client hangs up or the lease is
            // lost; the rest of the proof runs on the CPU
            let peer = job.stream.try_clone().ok();
            let lost = lease.as_ref().map(|l| l.watch());
            let cancel: crate::service::Cancel = std::sync::Arc::new(move || {
                peer.as_ref().is_some_and(lock::peer_hung_up) || lost.as_ref().is_some_and(|f| f())
            });
            let opts = RequestOptions {
                zero_check: *zero_check,
                lease,
                lease_refused,
                cancel: Some(cancel),
            };
            let res = input::read_input(input).and_then(|bytes| svc.prove(&bytes, opts)).and_then(
                |served| {
                    input::write_owner_only(output, &served.proof)?;
                    Ok(served.record)
                },
            );
            match res {
                Ok(record) => json!({"ok": true, "record": record}),
                Err(e) => {
                    let mut r = protocol::error_reply(e.kind(), &e.to_string());
                    if let Some(id) = svc.last_request() {
                        r["request"] = json!(id);
                    }
                    r
                }
            }
        }
        Request::Health {} | Request::Stop {} => unreachable!("answered by the reader"),
    }
}

/// Serves `svc` on `listener` until a stop or a retirement. Returns how it
/// ended.
pub fn serve<R: ServedRelation>(mut svc: ProverService<R>, listener: UnixListener) -> ServeEnd {
    serve_with(&mut svc, listener, READ_DEADLINE)
}

/// As [`serve`], borrowing the service, with an explicit read deadline.
pub fn serve_with<R: ServedRelation>(
    svc: &mut ProverService<R>,
    listener: UnixListener,
    deadline: Duration,
) -> ServeEnd {
    let st = svc.start_record();
    let shared = Arc::new(Shared {
        stop: AtomicBool::new(false),
        places: AtomicUsize::new(0),
        readers: AtomicUsize::new(0),
        proving: AtomicBool::new(false),
        served: AtomicU64::new(0),
        retired: Mutex::new(None),
        started: Instant::now(),
        health: json!({
            "relation": st.relation,
            "k": st.k,
            "vk_sha256": st.vk_sha256,
            "device": st.device.is_some(),
            "phases": st.phases,
        }),
    });
    let (tx, rx) = mpsc::channel::<Job>();
    let acc = {
        let sh = shared.clone();
        std::thread::spawn(move || acceptor(listener, sh, tx, deadline))
    };
    let end = loop {
        match rx.recv_timeout(Duration::from_millis(50)) {
            Ok(mut job) => {
                let wait_s = job.accepted.elapsed().as_secs_f64();
                let start_unix = protocol::unix_s();
                shared.proving.store(true, SeqCst);
                let mut reply = handle(svc, &mut job, shared.served.load(SeqCst));
                shared.proving.store(false, SeqCst);
                // a served proof is a verified one that is returned
                if job.req.op() == "prove" && reply["ok"] == true {
                    shared.served.fetch_add(1, SeqCst);
                }
                reply["queue"] = json!(QueueRecord {
                    wait_s,
                    start_unix,
                    end_unix: protocol::unix_s()
                });
                log(job.req.op(), &reply);
                write_reply(&job.stream, &reply);
                drop(job);
                shared.places.fetch_sub(1, SeqCst);
                if let Some(r) = svc.retirement() {
                    *shared.retired.lock().unwrap() = Some(r.reason().to_string());
                    shared.stop.store(true, SeqCst);
                    break match r {
                        Retirement::Erasure(m) => ServeEnd::Retired(m.clone()),
                        Retirement::Bound(m) => ServeEnd::Bound(m.clone()),
                    };
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if shared.stopping() && shared.places.load(SeqCst) == 0 {
                    break ServeEnd::Stopped;
                }
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => break ServeEnd::Stopped,
        }
    };
    shared.stop.store(true, SeqCst);
    let _ = acc.join();
    // refuse what is left in the channel: after a retirement the caller
    // lost its daemon (its client counts a failure and may fall back); after
    // a stop the daemon is busy stopping
    let left = match end {
        ServeEnd::Stopped => protocol::error_reply("busy", "the daemon is stopping"),
        _ => protocol::error_reply("daemon-lost", "the daemon retired before this request ran"),
    };
    while let Ok(j) = rx.try_recv() {
        write_reply(&j.stream, &left);
    }
    end
}

/// Binds `socket`, installs the signal handlers, serves, and removes the
/// socket file at the end.
pub fn run<R: ServedRelation>(svc: ProverService<R>, socket: &Path) -> Result<ServeEnd, Error> {
    crate::report::withhold_panic_messages();
    let l = bind(socket)?;
    install_signal_handlers();
    log("ready", &json!({"queue_places": QUEUE_PLACES}));
    let end = serve(svc, l);
    let _ = std::fs::remove_file(socket);
    log("end", &json!({"end": format!("{end:?}")}));
    Ok(end)
}

/// Command-line options of a daemon binary.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DaemonArgs {
    /// `--config FILE`.
    pub config: Option<PathBuf>,
    /// `--socket PATH`.
    pub socket: Option<PathBuf>,
    /// `--srs FILE`.
    pub srs: Option<PathBuf>,
    /// `--insecure-test-srs`: generate an SRS with a random toxic waste that
    /// this process knows. For tests and demos only.
    pub insecure_test_srs: bool,
}

/// The usage text of a daemon binary.
pub const DAEMON_USAGE: &str =
    "usage: midnight-gpu-proverd [--config FILE] [--socket PATH] [--srs FILE | --insecure-test-srs]

Serves one relation on a local Unix socket (mode 0600). Configuration comes from the
defaults, the JSON config file and MIDNIGHT_GPU_PROVER_* environment variables.";

/// Parses daemon arguments (without the program name).
pub fn parse_args(args: &[String]) -> Result<DaemonArgs, String> {
    let mut a = DaemonArgs::default();
    let mut it = args.iter();
    while let Some(x) = it.next() {
        let mut val = |n: &str| it.next().map(PathBuf::from).ok_or(format!("{n} needs a value"));
        match x.as_str() {
            "--config" => a.config = Some(val("--config")?),
            "--socket" => a.socket = Some(val("--socket")?),
            "--srs" => a.srs = Some(val("--srs")?),
            "--insecure-test-srs" => a.insecure_test_srs = true,
            "-h" | "--help" => return Err(String::new()),
            // the argument itself is not repeated
            _ => return Err("unknown argument".into()),
        }
    }
    if a.srs.is_some() && a.insecure_test_srs {
        return Err("--srs and --insecure-test-srs exclude each other".into());
    }
    Ok(a)
}

/// Loads the SRS for `relation` as the arguments and the config say.
pub fn load_srs<R: ServedRelation>(
    relation: &R,
    cfg: &Config,
    srs: Option<&Path>,
    insecure_test_srs: bool,
) -> Result<midnight_proofs::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>, Error> {
    if insecure_test_srs {
        let k = relation.k().unwrap_or_else(|| midnight_zk_stdlib::optimal_k(relation));
        eprintln!(
            "midnight-gpu-prover: WARNING: insecure test SRS (k = {k}); its proofs prove nothing"
        );
        return Ok(midnight_proofs::poly::kzg::params::ParamsKZG::unsafe_setup(
            k,
            rand::rngs::OsRng,
        ));
    }
    let p = srs
        .map(Path::to_path_buf)
        .or_else(|| cfg.srs_path.clone())
        .ok_or_else(|| Error::Config("no SRS: set --srs or MIDNIGHT_GPU_PROVER_SRS".into()))?;
    crate::service::read_srs(&p)
}

/// Environment variables that switch on test-only behaviour of the device
/// layer: fault injection and seeded randomness.
pub const TEST_SWITCH_VARS: [&str; 3] = [
    "MIDNIGHT_GPU_FAULT",
    "MIDNIGHT_GPU_TEST_SEED",
    "MIDNIGHT_GPU_PROVER_TEST_SEED",
];

/// In a build without the `test-seed` feature: the refusal when a test
/// switch is set in the environment. A release daemon refuses to start
/// rather than serve with the device turned off.
pub fn test_switch_in_release() -> Option<String> {
    if cfg!(feature = "test-seed") {
        return None;
    }
    let set: Vec<&str> =
        TEST_SWITCH_VARS.into_iter().filter(|v| std::env::var_os(v).is_some()).collect();
    (!set.is_empty()).then(|| {
        format!(
            "refused: {} is set; test switches are not taken by a release build",
            set.join(", ")
        )
    })
}

/// The whole daemon binary for `relation`: parses `std::env::args`, loads
/// the config and the SRS, builds the service, writes the start record to
/// stderr and serves. Returns the process exit code: 0 after a stop, 3 when
/// the service refuses to start, 2 on a usage or config error, 4 after a
/// retirement.
///
/// A daemon for another relation is:
///
/// ```no_run
/// # let relation = midnight_gpu_prover::example::PoseidonPreimage;
/// // in `fn main` of the binary:
/// std::process::exit(midnight_gpu_prover::daemon::main(relation));
/// ```
pub fn main<R: ServedRelation>(relation: R) -> i32 {
    crate::report::withhold_panic_messages();
    crate::device::warn_test_seed_build();
    // no tracing subscriber: dependency events (zkir, midnight_zkir) are dropped
    if let Some(m) = test_switch_in_release() {
        eprintln!("midnight-gpu-proverd: {m}");
        return 2;
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a = match parse_args(&args) {
        Ok(a) => a,
        Err(m) => {
            if !m.is_empty() {
                eprintln!("midnight-gpu-proverd: {m}");
            }
            eprintln!("{DAEMON_USAGE}");
            return 2;
        }
    };
    let mut cfg = match Config::load(a.config.as_deref()) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("midnight-gpu-proverd: {e}");
            return 2;
        }
    };
    if let Some(s) = a.socket {
        cfg.socket = Some(s);
    }
    let socket = cfg.socket_path();
    // the size check comes before any SRS load, key generation or device
    // work; the service constructor checks it again
    let k = relation.k().unwrap_or_else(|| midnight_zk_stdlib::optimal_k(&relation));
    if k > cfg.max_k {
        eprintln!(
            "midnight-gpu-proverd: {}",
            Error::Refused(format!(
                "the circuit has k = {k}, above max_k = {}",
                cfg.max_k
            ))
        );
        return 3;
    }
    let params = match load_srs(&relation, &cfg, a.srs.as_deref(), a.insecure_test_srs) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("midnight-gpu-proverd: {e}");
            return 2;
        }
    };
    let svc = match ProverService::new(relation, params, cfg) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("midnight-gpu-proverd: {e}");
            return if matches!(e, Error::Config(_)) { 2 } else { 3 };
        }
    };
    log(
        "start",
        &serde_json::to_value(svc.start_record()).unwrap_or(Value::Null),
    );
    match run(svc, &socket) {
        Ok(ServeEnd::Stopped) => 0,
        Ok(ServeEnd::Retired(_)) => 4,
        Ok(ServeEnd::Bound(_)) => 3,
        Err(e) => {
            eprintln!("midnight-gpu-proverd: {e}");
            3
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn args() {
        let s = |v: &[&str]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>();
        let a = parse_args(&s(&["--socket", "/x.sock", "--insecure-test-srs"])).unwrap();
        assert_eq!(a.socket, Some(PathBuf::from("/x.sock")));
        assert!(a.insecure_test_srs);
        assert!(parse_args(&s(&["--srs", "a", "--insecure-test-srs"])).is_err());
        assert!(parse_args(&s(&["--bogus"])).is_err());
        assert!(parse_args(&s(&["--srs"])).is_err());
    }

    #[test]
    fn bind_is_owner_only_and_refuses_a_live_socket() {
        use std::os::unix::fs::MetadataExt;
        // the listener must be closed once dropped: no child of another
        // test may hold a copy (see `lock::tests::SPAWN`)
        let _g = crate::lock::tests::spawn_guard();
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("d.sock");
        let l = bind(&p).unwrap();
        assert_eq!(std::fs::metadata(&p).unwrap().mode() & 0o777, 0o600);
        assert!(matches!(bind(&p), Err(Error::Refused(_))));
        drop(l);
        // a stale socket file is replaced
        let _l = bind(&p).unwrap();
    }
}

#[cfg(test)]
#[path = "service/oracle_reader.rs"]
pub(crate) mod oracle_reader;
