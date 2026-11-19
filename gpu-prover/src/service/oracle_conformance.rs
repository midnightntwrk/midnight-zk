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

//! Replay the service vectors through ProverService. The Device trait supplies
//! memory readings, fault counters and wipe confirmations. Two barriers expose
//! the synchronous prover's boundaries without splitting its production logic.

use std::{
    collections::{BTreeSet, VecDeque},
    fs::{self, File},
    io::{BufRead, BufReader, Write},
    os::fd::AsRawFd,
    path::Path,
    process::{Command, Stdio},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, AtomicUsize, Ordering::SeqCst},
        mpsc::{self, Receiver, Sender},
    },
    thread,
    time::Duration,
};

use rand::SeedableRng;
use serde::Deserialize;
use serde_json::{Value, json};

use super::*;
use crate::{
    ClientConfig,
    client::Client,
    config::WslSelect,
    daemon::oracle_reader::reserve_place,
    device::{DeviceCounters, DeviceInfo, Fallback, Held, MemInfo, Pk, Shape, WipeReport},
    example::{PoseidonPreimage, example_input},
    lock::lock_exclusive,
};

#[derive(Deserialize)]
struct Trace {
    format: String,
    name: String,
    config: Value,
    ops: Vec<u64>,
    states: Vec<Value>,
    refused: Vec<Vec<String>>,
}

const REASONS: [&str; 7] = [
    "no-device",
    "below-min-k",
    "shape",
    "unreduced",
    "memory",
    "fault",
    "device-error",
];

impl Trace {
    fn v2(&self) -> bool {
        match self.format.as_str() {
            "midnight-gpu-vectors/1" => false,
            "midnight-gpu-vectors/2" => true,
            other => panic!("unknown service vector format: {other}"),
        }
    }

    fn acceptance(&self) -> bool {
        flag(&self.config, if self.v2() { "acceptance" } else { "bench" })
    }

    fn client_config(&self) -> ClientConfig {
        let mut cfg = ClientConfig::default();
        if self.v2() {
            cfg.breaker_failures = number(&self.config, "brLimit").try_into().unwrap();
            cfg.breaker_window_s = number(&self.config, "brWindow");
            cfg.breaker_cooldown_s = number(&self.config, "brCooldown");
        }
        cfg
    }
}

fn vector_dir() -> std::path::PathBuf {
    std::env::var_os("ORACLE_VECTOR_DIR")
        .map(Into::into)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../gpu-spec/vectors"))
}

/// Keep the live codec here. Forward opaque state records to Lean unchanged.
fn oracle_states(
    binary: &Path,
    initial: &Value,
    ops: &[u64],
    refused: &[Vec<String>],
) -> Vec<Value> {
    let mut child = Command::new(binary)
        .arg("--step")
        .env("LEAN_ABORT_ON_PANIC", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("start ORACLE_BIN --step");
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let mut state = initial.clone();
    let mut states = vec![state.clone()];
    for (i, op) in ops.iter().enumerate() {
        writeln!(input, "{}", json!({"state":{"s":state},"op":op})).unwrap();
        let mut line = String::new();
        output.read_line(&mut line).unwrap();
        let answer: Value = serde_json::from_str(&line).unwrap();
        if refused[i].is_empty() {
            state = answer["state"]["s"].clone();
        } else {
            assert_eq!(answer["refused"], json!(refused[i]));
        }
        assert!(state.is_object(), "oracle step {}: {answer}", i + 1);
        states.push(state.clone());
    }
    drop(input);
    assert!(child.wait().unwrap().success());
    states
}

#[derive(Default)]
struct Hardware {
    free: u64,
    after_wait: u64,
    budget: u64,
    resident: u64,
    held: Held,
    mask: Phases,
    counters: DeviceCounters,
    sampled_peak: u64,
    dirty: bool,
    revoked: bool,
    valid_proof: bool,
    verifier_input_seen: bool,
}

#[derive(PartialEq, Debug)]
enum Event {
    Began(Phases),
    Wiping,
    Returned,
}
#[derive(PartialEq, Debug)]
enum Resume {
    Finish,
    Wipe(bool),
}

struct Port {
    device: bool,
    hw: Arc<Mutex<Hardware>>,
    events: Sender<Event>,
    resume: Arc<Mutex<Receiver<Resume>>>,
}

fn recv<T>(rx: &Receiver<T>) -> T {
    rx.recv_timeout(Duration::from_secs(60)).expect("prover barrier")
}

impl Device for Port {
    fn info(&self) -> Option<DeviceInfo> {
        self.device.then(DeviceInfo::default)
    }

    fn mem(&self) -> Option<MemInfo> {
        let mut h = self.hw.lock().unwrap();
        let free = h.free;
        h.free = h.after_wait;
        Some(MemInfo {
            free,
            total: h.budget,
        })
    }

    fn held(&self) -> Held {
        self.hw.lock().unwrap().held
    }
    fn shape(&self, _: &Pk) -> Option<Shape> {
        Some(Shape::default())
    }

    fn begin_request(&self, phases: Phases) -> Phases {
        {
            let mut h = self.hw.lock().unwrap();
            h.revoked = false;
            h.mask = phases;
            h.dirty = !phases.is_empty();
            if phases.contains(Phases::QUOTIENT) {
                h.held.resident = h.resident;
            }
            if phases.contains(Phases::MSM) {
                h.held.tables = 1;
            }
        }
        phases
    }

    fn observe_proving(&self) {
        let mask = {
            let mut h = self.hw.lock().unwrap();
            // GPU-085: a device phase that starts serves its call, and the
            // counters say so, as the device layer counts each launch.
            for (bit, class) in [
                (Phases::MSM, "msm"),
                (Phases::FFT, "fft"),
                (Phases::IFFT, "ifft"),
                (Phases::QUOTIENT, "quotient"),
            ] {
                if h.mask.contains(bit) {
                    *h.counters.calls.entry(class.into()).or_default() += 1;
                }
            }
            h.mask
        };
        self.events.send(Event::Began(mask)).unwrap();
        assert_eq!(recv(&self.resume.lock().unwrap()), Resume::Finish);
    }

    fn revoke(&self) -> bool {
        let mut h = self.hw.lock().unwrap();
        let revoked = !h.mask.is_empty();
        h.mask = Phases::NONE;
        h.revoked |= revoked;
        revoked
    }

    fn evict(&self, tables: bool) -> u64 {
        let mut h = self.hw.lock().unwrap();
        let freed = std::mem::take(&mut h.held.resident);
        h.free += freed;
        h.after_wait += freed;
        if tables {
            h.held.tables = 0;
        }
        freed
    }

    fn end_request(&self, check: bool) -> Result<WipeReport, String> {
        self.events.send(Event::Wiping).unwrap();
        let Resume::Wipe(confirmed) = recv(&self.resume.lock().unwrap()) else {
            panic!("expected wipe confirmation")
        };
        let mut h = self.hw.lock().unwrap();
        h.mask = Phases::NONE;
        if !confirmed {
            return Err("injected wipe failure".into());
        }
        h.dirty = false;
        // The wire measures device MSM contexts released by end_request.
        // Cached host SRS registrations have a separate lifetime.
        h.held.tables = 0;
        Ok(WipeReport {
            checked: check,
            ..Default::default()
        })
    }

    fn counters(&self) -> DeviceCounters {
        let mut h = self.hw.lock().unwrap();
        h.sampled_peak = h.counters.peak_bytes;
        h.counters.clone()
    }
    fn reset_counters(&self) {
        self.hw.lock().unwrap().counters = DeviceCounters::default();
    }
}

#[derive(Default)]
struct Checks {
    rows: Vec<Value>,
    comparisons: usize,
}

impl Checks {
    fn field(&mut self, t: &Trace, step: usize, field: &str, actual: Value) {
        self.field_as(t, step, field, field, actual);
    }

    fn field_as(&mut self, t: &Trace, step: usize, field: &str, observable: &str, actual: Value) {
        self.observation(t, step, observable, &t.states[step][field], actual);
    }

    fn observation(
        &mut self,
        t: &Trace,
        step: usize,
        observable: &str,
        expected: &Value,
        actual: Value,
    ) {
        self.comparisons += 1;
        assert!(!expected.is_null(), "missing spec field {observable}");
        if *expected != actual {
            self.rows.push(
                json!({"step": step, "op": step.checked_sub(1).map(|i| t.ops[i]),
                "field": observable, "expected": expected, "actual": actual}),
            );
        }
    }
}

fn number(v: &Value, key: &str) -> u64 {
    v[key].as_u64().unwrap()
}
fn flag(v: &Value, key: &str) -> bool {
    v[key].as_bool().unwrap()
}

// Inject at the socket boundary while preserving the production Client::prove
// clock, breaker, fallback and result paths.
struct Exchange {
    contacted: Sender<()>,
    response: Receiver<Result<Value, Error>>,
}

thread_local! {
    static EXCHANGE: std::cell::RefCell<Option<Exchange>> = const { std::cell::RefCell::new(None) };
}

pub(crate) fn take_reply() -> Option<Result<Value, Error>> {
    let exchange = EXCHANGE.take()?;
    exchange.contacted.send(()).unwrap();
    Some(recv(&exchange.response))
}

fn prove_via(
    client: &Client,
    input: &Path,
    output: &Path,
    fallback: crate::client::Fallback<'_>,
    exchange: impl FnOnce() -> Result<Value, Error> + Send,
) -> Result<crate::client::Outcome, Error> {
    let (contacted, contact) = mpsc::channel();
    let (response, reply) = mpsc::channel();
    thread::scope(|scope| {
        scope.spawn(move || {
            if contact.recv().is_ok() {
                response.send(exchange()).unwrap();
            }
        });
        EXCHANGE.set(Some(Exchange {
            contacted,
            response: reply,
        }));
        let outcome = client.prove(input, output, false, None, fallback);
        drop(EXCHANGE.take());
        outcome
    })
}

// flock belongs to an open file description. Explicitly releasing a lease
// must also release the lock on a duplicate still held inside the worker.
fn unlock(lock: &mut Option<File>) {
    if let Some(file) = lock.take() {
        // SAFETY: file stays open throughout the syscall.
        assert_eq!(unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_UN) }, 0);
    }
}

fn breaker_reply(client: &Client, reply: Result<Value, Error>) -> Label {
    let path = Path::new("unused-with-injected-transport");
    let outcome = prove_via(client, path, path, &|_, _| Ok(Value::Null), || reply).unwrap();
    outcome.label
}

// Each accepted caller waits inside the real transport callback. This preserves
// the client's clock sample and breaker decision at arrival even if time passes
// or another caller opens the breaker before the reply.
struct Caller {
    reply: Sender<Result<Value, Error>>,
    worker: thread::JoinHandle<Label>,
}

impl Caller {
    fn finish(self, reply: Result<Value, Error>) -> Label {
        self.reply.send(reply).unwrap();
        self.worker.join().unwrap()
    }
}

fn replay(t: &Trace, params: &ParamsKZG<Bls12>, binary: Option<&Path>, itf: bool) -> Checks {
    let c = &t.config;
    let dir = tempfile::tempdir().unwrap();
    let lock_path = dir.path().join("device.lock");
    let wsl = flag(c, "wsl");
    let hw = Arc::new(Mutex::new(Hardware {
        budget: number(c, "budget"),
        resident: number(c, "resident"),
        ..Default::default()
    }));
    let (tx, events) = mpsc::channel();
    let (resume, rx) = mpsc::channel();
    let rx = Arc::new(Mutex::new(rx));
    let cfg = Config {
        threads: 2,
        max_device_peak_mib: 1,
        mode: if t.acceptance() {
            RunMode::Acceptance
        } else {
            RunMode::Production
        },
        resident: if flag(c, "keep") {
            ResidentPolicy::Keep
        } else {
            ResidentPolicy::Evict
        },
        wsl: if wsl { WslSelect::On } else { WslSelect::Off },
        wsl_reserve_mib: 0,
        lock_path: wsl.then(|| lock_path.clone()),
        ..Config::default()
    };
    let (decisions, admission) = mpsc::channel();
    let start = || {
        let dev = Port {
            device: flag(c, "device"),
            hw: hw.clone(),
            events: tx.clone(),
            resume: rx.clone(),
        };
        let mut svc = ProverService::with_device(
            PoseidonPreimage,
            params.clone(),
            cfg.clone(),
            Box::new(dev),
        )
        .unwrap();
        // One abstract unit is one byte. Tables have a presence sentinel; the
        // oracle does not price them independently of the per-proof need.
        svc.need = DeviceNeed {
            resident: number(c, "resident"),
            quotient: number(c, "perProof") - number(c, "reduced"),
            scratch: number(c, "reduced"),
            ..Default::default()
        };
        svc.observed_admission = Some(decisions.clone());
        svc
    };
    let mut service = Some(start());
    let mut past_served = 0;
    let mut last_reported_served = 0;
    let drain = |event: Option<Event>| {
        // A finite trace or simulated process death can cut a proof between
        // barriers. Let this CPU worker exit before discarding its result.
        let event = if matches!(event, Some(Event::Began(_))) {
            resume.send(Resume::Finish).unwrap();
            Some(recv(&events))
        } else {
            event
        };
        if event == Some(Event::Wiping) {
            resume.send(Resume::Wipe(true)).unwrap();
            assert_eq!(recv(&events), Event::Returned);
        }
    };
    let mut worker = None;
    let clock = Arc::new(AtomicU64::new(0));
    let now = clock.clone();
    let client = Arc::new(Client::with_clock(
        ClientConfig {
            breaker_state: Some(dir.path().join("breaker")),
            ..t.client_config()
        },
        Box::new(move || now.load(SeqCst)),
    ));

    let input = dir.path().join("caller.input");
    crate::input::write_owner_only(&input, &example_input(7)).unwrap();
    let arrive = |id| -> Result<Caller, Label> {
        let output = dir.path().join(format!("caller-{id}.proof"));
        let input = input.clone();
        let params = params.clone();
        let cfg = cfg.clone();
        let client = Arc::clone(&client);
        let (reply, response) = mpsc::channel();
        let (contacted, contact) = mpsc::channel();
        let worker = thread::spawn(move || {
            let fallback = |i: &Path, o: &Path| {
                if itf {
                    Ok(Value::Null)
                } else {
                    crate::client::cpu_prove(PoseidonPreimage, params.clone(), &cfg, i, o)
                }
            };
            let outcome = prove_via(&client, &input, &output, &fallback, move || {
                contacted.send(()).unwrap();
                recv(&response)
            })
            .unwrap();
            if !itf && outcome.label == Label::CpuFallback {
                let bytes = fs::read(&output).unwrap();
                assert!(!bytes.is_empty(), "missing CPU fallback proof");
                assert_eq!(outcome.record["proof_sha256"], report::sha256_hex(&bytes));
                assert_eq!(outcome.record["label"], json!(Label::CpuFallback));
            }
            outcome.label
        });
        match contact.recv_timeout(Duration::from_secs(60)) {
            Ok(()) => Ok(Caller { reply, worker }),
            Err(mpsc::RecvTimeoutError::Disconnected) => Err(worker.join().unwrap()),
            Err(mpsc::RecvTimeoutError::Timeout) => panic!("client arrival timed out"),
        }
    };
    let mut callers = VecDeque::new();

    let places = AtomicUsize::new(0);
    let mut lock: Option<File> = None;
    let mut caller_peer = None;
    let lease_polls = Arc::new(AtomicU64::new(0));
    let mut up = true;
    let mut restarts = Vec::<u64>::new();
    let mut checks = Checks::default();
    let mut requests = 0;
    let mut busy = 0;
    let mut cpu = 0;
    let mut errors = 0;
    let mut successes = 0;
    let mut degraded = 0;
    let mut request_event = None;
    let mut bench_failure = false;
    let mut skips = 0_u64;
    let mut refused_degraded = 0_u64;
    let mut verified = 0_u64;
    let mut unverified = 0_u64;
    let mut decline_counts = [0_u64; 7];
    // Logical copy events on the wire. Device copies are observed by the two-proof
    // gate.
    let mut readbacks = 0_u64;
    let mut bad_readbacks = 0_u64;
    let mut wire_ops = t.ops.clone();
    let mut finish_index = None;
    let mut reply_checks = Vec::new();
    let v2 = t.v2();
    let mut result = None;
    // Step zero uses the same field projection as the post-operation snapshots.
    for (step, op) in std::iter::once(0).chain(t.ops.iter().copied()).enumerate() {
        let a = op / 100 % 100;
        let b = op / 10000;
        let code = op % 100;
        // A refused event changes no hardware or client state. In particular the
        // acceptance fast path may be followed by a refused finish operation.
        let refused = step != 0 && !t.refused[step - 1].is_empty();
        if v2 && code == 4 && b == 0 && a < 4 && request_event == Some(Event::Wiping) {
            // While the worker waits at the wipe barrier, only the zero-check
            // counter can cross the wire. Check refusals before skipping them.
            if a == 2 {
                assert!(!refused, "{} step {step}: counter read refused", t.name);
            } else {
                assert_eq!(
                    t.refused[step - 1],
                    ["not-enabled"],
                    "{} step {step}",
                    t.name
                );
            }
        }
        if refused {
            let reason = &t.refused[step - 1];
            assert_eq!(t.states[step], t.states[step - 1]);
            if code == 4 && a >= if v2 { 4 } else { 3 } {
                assert_eq!(reason, &["readback-not-permitted"]);
            } else if v2 && code == 3 && a >= REASONS.len() as u64 {
                assert_eq!(reason, &["bad-argument"]);
            }
        }
        match code {
            _ if refused => {}
            0 if step == 0 => {
                let svc = service.as_ref().unwrap();
                checks.field(
                    t,
                    step,
                    "device",
                    json!(svc.start_record().device.is_some()),
                );
                checks.field(
                    t,
                    step,
                    "keep",
                    json!(svc.config.resident == ResidentPolicy::Keep),
                );
                checks.field(t, step, "wsl", json!(svc.wsl));
                checks.field(
                    t,
                    step,
                    if v2 { "acceptance" } else { "bench" },
                    json!(svc.config.mode == RunMode::Acceptance),
                );
                checks.field(t, step, "up", json!(svc.retired().is_none()));
                checks.field(t, step, "served", json!(svc.served()));
                checks.field(
                    t,
                    step,
                    "devWork",
                    json!(!hw.lock().unwrap().mask.is_empty()),
                );
            }
            1 => {
                requests += 1;
                match arrive(requests) {
                    Err(label) => {
                        assert_eq!(label, Label::CpuFallback);
                        skips += 1;
                        cpu += 1;
                    }
                    Ok(caller) if !up => {
                        assert_eq!(
                            caller.finish(Err(Error::Daemon("down".into()))),
                            Label::CpuFallback
                        );
                        cpu += 1;
                    }
                    Ok(caller) if !reserve_place(&places) => {
                        assert_eq!(caller.finish(Err(Error::Busy)), Label::CpuFallback);
                        busy += 1;
                        cpu += 1;
                    }
                    Ok(caller) => callers.push_back(caller),
                }
            }
            2 => {
                let mut svc = service.take().unwrap();
                let lease = lock.as_ref().filter(|_| cfg.lock_path.is_some()).and_then(|f| {
                    Lease::validate(&lock_path, Some(f.try_clone().unwrap().into())).ok()
                });
                let (server, peer) = std::os::unix::net::UnixStream::pair().unwrap();
                caller_peer = Some(peer);
                let lost = lease.as_ref().map(Lease::watch);
                let polls = lease_polls.clone();
                let cancel = Arc::new(move || {
                    let lost =
                        crate::lock::peer_hung_up(&server) || lost.as_ref().is_some_and(|f| f());
                    polls.fetch_add(1, SeqCst);
                    lost
                });
                let opts = RequestOptions {
                    cancel: Some(cancel),
                    lease,
                    zero_check: true,
                    ..Default::default()
                };
                // One deterministic post-wait reading; do not sleep through a
                // failing memory poll when the trace supplies the same reading.
                let held_before = hw.lock().unwrap().held.resident;
                let full_need =
                    number(c, "perProof") + number(c, "resident").saturating_sub(held_before);
                svc.config.wait_s = if a < full_need && b >= full_need {
                    1.0
                } else {
                    0.0
                };
                {
                    let mut h = hw.lock().unwrap();
                    h.free = a;
                    h.after_wait = b;
                    h.verifier_input_seen = false;
                }
                let finished = tx.clone();
                let proof_status = hw.clone();
                worker = Some(thread::spawn(move || {
                    let proof = |p: &[u8]| {
                        let mut probe = proof_status.lock().unwrap();
                        probe.verifier_input_seen = true;
                        if probe.valid_proof {
                            p.to_vec()
                        } else {
                            Vec::new()
                        }
                    };
                    let result = svc.prove_with(
                        &SecretBytes::new(example_input(7)),
                        opts,
                        OsRng,
                        Some(&proof),
                    );
                    finished.send(Event::Returned).unwrap();
                    (svc, result)
                }));
                let adm = recv(&admission);
                let numeric = match adm.step {
                    Step::None => 0,
                    Step::Gpu => 1,
                    Step::Wait => 2,
                    Step::Evict => 3,
                    Step::Cpu => 4,
                };
                checks.field(t, step, "step", json!(numeric));
                checks.field(t, step, "admNeed", json!(adm.need));
                checks.field(t, step, "admFree", json!(adm.free));
                if v2 && !wsl && matches!(adm.step, Step::Wait | Step::Evict | Step::Cpu) {
                    // b is the free reading before returning any resident key memory.
                    let freed = if matches!(adm.step, Step::Evict | Step::Cpu) {
                        held_before
                    } else {
                        0
                    };
                    let before_eviction = adm.free.checked_sub(freed).expect("free after eviction");
                    wire_ops[step - 1] = 2 + 100 * a + 10000 * before_eviction;
                }
                request_event = Some(recv(&events));
                let device_started =
                    matches!(request_event, Some(Event::Began(p)) if !p.is_empty());
                checks.field(t, step, "devWork", json!(device_started));
                checks.field(t, step, "degraded", json!(adm.step.degraded()));
                if request_event == Some(Event::Returned) {
                    let (svc, reply) = worker.take().unwrap().join().unwrap();
                    assert!(t.acceptance() && matches!(&reply, Err(Error::Degraded(_))));
                    checks.field(t, step, "phase", json!(4));
                    checks.field(t, step, "wipeOk", json!(!hw.lock().unwrap().dirty));
                    result = Some((reply, false));
                    service = Some(svc);
                    request_event = None;
                }
            }
            3 => {
                let mut h = hw.lock().unwrap();
                let decline = Fallback {
                    phase: "ntt".into(),
                    reason: if v2 { REASONS[a as usize] } else { "fault" }.into(),
                    count: 1,
                };
                if !v2 || a >= 2 {
                    h.counters.fallbacks.push(decline.clone());
                }
                h.counters.declines.push(decline);
                let row = h.counters.declines.last().unwrap();
                let index = REASONS.iter().position(|reason| *reason == row.reason).unwrap();
                decline_counts[index] += row.count;
                checks.field(t, step, "fallbacks", json!(h.counters.fallback_count()));
            }
            // Physical transfers have no Device API. The independently instrumented
            // GPU-038 proof gate checks this op on the box.
            4 => {
                readbacks += 1;
                bad_readbacks += u64::from(a >= if v2 { 4 } else { 3 });
            }
            5 => {
                unlock(&mut lock);
                if !wsl {
                    // Outside WSL the lease is the client connection.
                    drop(caller_peer.take());
                }
                // Leave the proof paused while the stock watcher samples the
                // actual lock. A second sample brackets callback completion.
                let after = lease_polls.load(SeqCst) + 2;
                let deadline = std::time::Instant::now() + Duration::from_secs(1);
                while lease_polls.load(SeqCst) < after && !hw.lock().unwrap().revoked {
                    if std::time::Instant::now() >= deadline {
                        break;
                    }
                    thread::sleep(Duration::from_millis(1));
                }
                checks.field(
                    t,
                    step,
                    "devWork",
                    json!(!hw.lock().unwrap().mask.is_empty()),
                );
                checks.field(t, step, "fallbacks", {
                    let h = hw.lock().unwrap();
                    json!(h.counters.fallback_count() + u64::from(h.revoked))
                });
            }
            6 => {
                hw.lock().unwrap().valid_proof = a == 1;
                if matches!(request_event, Some(Event::Began(_))) {
                    resume.send(Resume::Finish).unwrap();
                    request_event = Some(recv(&events));
                    assert_eq!(request_event, Some(Event::Wiping));
                }
                // The existing proof-transform hook is immediately before the stock
                // verifier. Its absence proves verification has not yet started.
                finish_index = Some(step - 1);
                if !v2 {
                    let h = hw.lock().unwrap();
                    checks.field(
                        t,
                        step,
                        "verifyOk",
                        json!(h.verifier_input_seen && h.valid_proof),
                    );
                }
            }
            7 => {
                let wipe_called = request_event == Some(Event::Wiping);
                if wipe_called {
                    resume.send(Resume::Wipe(a == 1)).unwrap();
                    assert_eq!(recv(&events), Event::Returned);
                }
                let (svc, reply) = worker.take().unwrap().join().unwrap();
                checks.field(
                    t,
                    step,
                    "wipeOk",
                    json!(wipe_called && !matches!(svc.retirement(), Some(Retirement::Erasure(_)))),
                );
                let mut accepts = false;
                if v2 {
                    // The proof transform runs before the verifier and also before a
                    // degraded refusal. Only a served record certifies verifier success.
                    let index = finish_index.take().unwrap();
                    accepts = reply.as_ref().is_ok_and(|served| {
                        let (instance, _) =
                            PoseidonPreimage.decode_input(&example_input(7)).unwrap();
                        svc.verify(&[instance], &served.proof).is_ok()
                    });
                    if matches!(&reply, Ok(_) | Err(Error::Verify)) {
                        checks.field(t, index + 1, "verifyOk", json!(accepts));
                        wire_ops[index] = if accepts { 106 } else { 6 };
                    }
                } else {
                    checks.field(t, step, "verifyOk", json!(reply.is_ok()));
                }
                if wipe_called && a == 0 {
                    assert!(matches!(&reply, Err(Error::Retired(_))));
                } else if !t.acceptance() && !hw.lock().unwrap().valid_proof {
                    assert!(matches!(&reply, Err(Error::Verify)));
                }
                if let Ok(s) = &reply {
                    let r = &s.record;
                    assert!(hw.lock().unwrap().verifier_input_seen);
                    assert_eq!(r.declines, hw.lock().unwrap().counters.declines);
                    let h = hw.lock().unwrap();
                    assert_eq!(
                        r.fallback_count,
                        h.counters.fallback_count() + u64::from(h.revoked)
                    );
                    assert!(r.fallbacks.starts_with(&h.counters.fallbacks));
                    drop(h);
                    if !v2 {
                        checks.field(t, step, "fallbacks", json!(r.fallback_count));
                        checks.field(t, step, "degraded", json!(!r.degraded_reasons.is_empty()));
                    }
                    assert_eq!(r.device_peak_bytes, hw.lock().unwrap().sampled_peak);
                    // GPU-085: cpu when nothing was admitted or no call ran
                    // on the device; GPU-012: gpu-degraded only with a
                    // counted fallback, never for the admission alone
                    let ran = r.device_calls.values().sum::<u64>() > 0;
                    let label = if r.admitted.is_empty() || !ran {
                        Label::Cpu
                    } else if r.fallback_count > 0 {
                        Label::GpuDegraded
                    } else {
                        Label::Gpu
                    };
                    assert_eq!(r.label, label);
                    assert!(r.wipe.checked);
                } else if matches!(&reply, Err(Error::Verify)) {
                    assert!(hw.lock().unwrap().verifier_input_seen);
                    assert!(!hw.lock().unwrap().valid_proof);
                } else {
                    assert!(
                        matches!(&reply, Err(Error::Retired(_) | Error::Degraded(_))),
                        "unexpected service reply: {reply:?}"
                    );
                }
                request_event = None;
                result = Some((reply, accepts));
                service = Some(svc);
            }
            8 => {
                places.fetch_sub(1, SeqCst);
                let (reply, accepts) = result.take().unwrap();
                let outcome = match reply {
                    Ok(s) => {
                        assert!(!s.proof.is_empty());
                        successes += 1;
                        if v2 {
                            verified += u64::from(accepts);
                            unverified += u64::from(!accepts);
                        }
                        if v2 && flag(c, "bench") && !s.record.degraded_reasons.is_empty() {
                            bench_failure = true;
                        }
                        degraded += u64::from(!s.record.degraded_reasons.is_empty());
                        Ok(json!({"record": s.record}))
                    }
                    Err(e) => {
                        errors += 1;
                        let refused = matches!(&e, Error::Degraded(_));
                        refused_degraded += u64::from(refused);
                        bench_failure |= !v2 && refused;
                        Err(e)
                    }
                };
                cpu +=
                    u64::from(callers.pop_front().unwrap().finish(outcome) == Label::CpuFallback);
                up = service.as_ref().unwrap().retired().is_none();
                if !up {
                    for _ in 0..places.swap(0, SeqCst) {
                        assert_eq!(
                            callers
                                .pop_front()
                                .unwrap()
                                .finish(Err(Error::Daemon("daemon-lost".into()))),
                            Label::CpuFallback
                        );
                        cpu += 1;
                    }
                }
                if v2 && binary.is_some() {
                    // At this boundary both wipe and verify have completed. The live
                    // oracle receives their observations in its own op 6/7/8 order.
                    reply_checks.push((step, verified));
                }
                checks.field(t, step, "up", json!(up));
                // The public stats counter and the number of successful replies
                // are separate observables. The oracle calls both "served".
                last_reported_served = service.as_ref().unwrap().served();
                checks.field(t, step, "served", json!(past_served + last_reported_served));
                checks.field_as(t, step, "served", "successReplies", json!(successes));
            }
            // Process exit and supervisor decisions are external to ProverService.
            9 => {
                up = false;
                for _ in 0..places.swap(0, SeqCst) {
                    cpu += u64::from(
                        callers
                            .pop_front()
                            .unwrap()
                            .finish(Err(Error::Daemon("process exited".into())))
                            == Label::CpuFallback,
                    );
                }
                if let Some(w) = worker.take() {
                    drain(request_event.take());
                    service = Some(w.join().unwrap().0);
                }
                finish_index = None;
                result = None;
            }
            10 => {
                // Supply a supervisor which takes the full permitted retry budget.
                // A deployment may stop earlier. Compare stopped only when the
                // upper bound forces it; the shipped service-manager harness
                // separately tests the real manager against its own configuration.
                let now = clock.load(SeqCst);
                let window = number(c, "window");
                restarts.retain(|at| window == 0 || now - *at < window);
                up = (restarts.len() as u64) < number(c, "limit");
                if flag(&t.states[step], "stopped") {
                    checks.field(t, step, "stopped", json!(!up));
                }
                if up {
                    restarts.push(now);
                    // Teardown after a crash can finish a blocked CPU proof.
                    // Only counts visible at replies survive the old process.
                    past_served += last_reported_served;
                    last_reported_served = 0;
                    *hw.lock().unwrap() = Hardware {
                        budget: number(c, "budget"),
                        resident: number(c, "resident"),
                        ..Default::default()
                    };
                    service = Some(start());
                }
            }
            11 => {
                clock.fetch_add(op / 100, SeqCst);
            }
            12 => {
                if a == 0 {
                    unlock(&mut lock);
                } else if lock.is_none() {
                    lock = Some(lock_exclusive(&lock_path).unwrap());
                }
            }
            13 => {
                service.as_ref().unwrap().evict(true);
            }
            // Inject a peak above the configured one-MiB device limit.
            14 => {
                hw.lock().unwrap().counters.peak_bytes = u64::MAX;
            }
            _ => panic!("new service op {op} in {} step {step}", t.name),
        }
        if v2 {
            let breaker = client.breaker().state();
            checks.field(t, step, "brFails", json!(breaker.failures));
            checks.field(t, step, "brOpenUntil", json!(breaker.open_until));
            checks.field(t, step, "breakerSkips", json!(skips));
            checks.field(t, step, "degradedRefused", json!(refused_degraded));
            checks.field(t, step, "declines", json!(decline_counts));
            checks.field(
                t,
                step,
                "declined",
                json!(decline_counts.iter().sum::<u64>()),
            );
            checks.field(t, step, "readbacks", json!(readbacks));
            checks.field(t, step, "badReadbacks", json!(bad_readbacks));
            checks.field(t, step, "verifyAccepts", json!(verified));
            checks.field(t, step, "unverifiedReturned", json!(unverified));
        }
        checks.field(t, step, "runFailed", json!(bench_failure));
        checks.field(t, step, "clock", json!(clock.load(SeqCst)));
        checks.field(t, step, "requests", json!(requests));
        checks.field(
            t,
            step,
            "waiting",
            json!(places.load(SeqCst).saturating_sub(1)),
        );
        checks.field(t, step, "busyReplies", json!(busy));
        checks.field(t, step, "clientCpu", json!(cpu));
        checks.field(t, step, "errors", json!(errors));
        checks.field(t, step, "degradedServed", json!(degraded));
        checks.field(t, step, "lockHeld", json!(lock.is_some()));
        if (up || (v2 && code == 8)) && !(v2 && matches!(code, 6 | 7)) {
            let h = hw.lock().unwrap();
            // ORACLE-18: residency is observable at the reply following a
            // failed wipe. Op 8 consumes the pending result and updates up.
            let awaiting_erasure_reply = v2
                && matches!(result, Some((Err(Error::Retired(_)), _)))
                && matches!(
                    service.as_ref().and_then(ProverService::retirement),
                    Some(Retirement::Erasure(_))
                );
            if !awaiting_erasure_reply {
                checks.field(t, step, "onDev", json!(up && h.held.resident != 0));
                checks.field(t, step, "tables", json!(up && h.held.tables != 0));
            }
            checks.field(t, step, "dirty", json!(up && h.dirty));
        }
    }
    // Some directed traces end with a connection still waiting for admission.
    // Close it and join its CPU worker after the last observed state.
    for caller in callers {
        assert_eq!(
            caller.finish(Err(Error::Daemon("end of trace".into()))),
            Label::CpuFallback
        );
    }
    if let Some(w) = worker {
        drain(request_event);
        drop(w.join().unwrap());
    }
    if let Some(b) = binary.filter(|_| v2) {
        let states = oracle_states(b, &t.states[0], &wire_ops, &t.refused);
        for (step, accepts) in reply_checks {
            checks.observation(
                t,
                step,
                "liveVerifyAccepts",
                &states[step]["verifyAccepts"],
                json!(accepts),
            );
        }
    }
    checks
}

#[test]
fn service_oracle_vectors() {
    let binary = std::env::var_os("ORACLE_BIN");
    let dir = vector_dir().join("service");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|s| s == "json"))
        .collect();
    paths.sort();
    let params = ParamsKZG::unsafe_setup(
        midnight_zk_stdlib::optimal_k(&PoseidonPreimage),
        rand_chacha::ChaCha8Rng::seed_from_u64(9),
    );
    let mut ops = BTreeSet::new();
    let mut differences = Vec::new();
    let mut clean = 0;
    let mut mismatching_steps = 0;
    let mut steps = 0;
    let mut versions = BTreeSet::new();
    for p in &paths {
        let t: Trace = serde_json::from_slice(&fs::read(p).unwrap()).unwrap();
        assert_eq!(t.states.len(), t.ops.len() + 1);
        assert_eq!(t.refused.len(), t.ops.len());
        ops.extend(t.ops.iter().map(|op| op % 100));
        if let Some(bin) = &binary {
            assert_eq!(
                oracle_states(bin.as_ref(), &t.states[0], &t.ops, &t.refused),
                t.states,
                "{}",
                t.name
            );
        }
        steps += t.ops.len();
        versions.insert(t.v2());
        let checks = replay(&t, &params, binary.as_deref().map(Path::new), false);
        clean += usize::from(checks.rows.is_empty());
        mismatching_steps +=
            checks.rows.iter().map(|r| number(r, "step")).collect::<BTreeSet<_>>().len();
        differences.extend(checks.rows.iter().map(|row| {
            format!(
                "{} {} {} {} {}",
                t.name,
                row["step"],
                row["field"].as_str().unwrap(),
                row["expected"],
                row["actual"]
            )
        }));
    }
    assert_eq!(ops, (1..=14).collect());
    eprintln!(
        "{} service traces, {clean} clean, {steps} transitions, {mismatching_steps} mismatching transitions, {} operation codes, live oracle: {}",
        paths.len(),
        ops.len(),
        binary.is_some()
    );
    assert_eq!(versions.len(), 1, "mixed service vector formats");
    let inventory = if versions.contains(&true) {
        (29, 261)
    } else {
        (15, 122)
    };
    assert_eq!((paths.len(), steps), inventory, "incomplete service corpus");
    assert!(
        differences.is_empty(),
        "trace step field expected actual:\n{}",
        differences.join("\n")
    );
}

#[test]
fn service_oracle_breaker_cooldown() {
    let path = vector_dir().join("service/restart-limit.json");
    let t: Trace = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let clock = Arc::new(AtomicU64::new(0));
    let now = clock.clone();
    let client = Client::with_clock(
        ClientConfig {
            breaker_state: Some(dir.path().join("breaker")),
            ..t.client_config()
        },
        Box::new(move || now.load(SeqCst)),
    );
    let threshold = client.config().breaker_failures.max(1);
    let cooldown = client.config().breaker_cooldown_s;
    for _ in 0..threshold {
        assert_eq!(
            breaker_reply(&client, Err(Error::Daemon("process exited".into()))),
            Label::CpuFallback
        );
    }
    let exchanges = AtomicUsize::new(0);
    let try_recovered_daemon = || {
        let path = Path::new("unused");
        prove_via(&client, path, path, &|_, _| Ok(Value::Null), || {
            exchanges.fetch_add(1, SeqCst);
            Ok(json!({"record":{"label":"gpu"}}))
        })
        .unwrap()
        .label
    };
    assert_eq!(client.breaker().state().open_until, cooldown);
    assert_eq!(try_recovered_daemon(), Label::CpuFallback);
    assert_eq!(exchanges.load(SeqCst), 0);
    clock.store(cooldown, SeqCst);
    assert_eq!(try_recovered_daemon(), Label::Gpu);
    assert_eq!(exchanges.load(SeqCst), 1);
    if let Some(binary) = std::env::var_os("ORACLE_BIN") {
        let mut ops = vec![9];
        ops.extend(std::iter::repeat_n(1, threshold as usize));
        ops.extend([10, 1, 11 + 100 * cooldown, 1]);
        let states = oracle_states(
            binary.as_ref(),
            &t.states[0],
            &ops,
            &vec![vec![]; ops.len()],
        );
        let recovery = &states[threshold as usize + 3];
        // V1 accepts the first arrival after restart. V2 keeps the breaker open
        // until cooldown, including across a supervisor restart.
        assert_eq!(
            recovery["clientCpu"],
            threshold + 1,
            "breaker-recovery first arrival after restart"
        );
        assert_eq!(recovery["phase"], 0);
    }
}

/// Move the clock inside a real client exchange. This places a verifier refusal
/// just outside the window that contained the previous two daemon failures.
#[test]
fn in_flight_failure_time_vs_oracle() {
    let Some(binary) = std::env::var_os("ORACLE_BIN") else {
        return;
    };
    let t: Trace =
        serde_json::from_slice(&fs::read(vector_dir().join("service/restart-limit.json")).unwrap())
            .unwrap();
    if !t.v2() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let clock = Arc::new(AtomicU64::new(0));
    let now = clock.clone();
    let config = t.client_config();
    let end = config.breaker_window_s + 1;
    let failures = config.breaker_failures.max(1) - 1;
    let client = Client::with_clock(
        ClientConfig {
            breaker_state: Some(dir.path().join("breaker")),
            ..config
        },
        Box::new(move || now.load(SeqCst)),
    );
    let mut ops = vec![9];
    for _ in 0..failures {
        assert_eq!(
            breaker_reply(&client, Err(Error::Daemon("absent".into()))),
            Label::CpuFallback
        );
        ops.push(1);
    }
    // Restart, accept an in-flight request, advance the clock, refuse its
    // proof, confirm its wipe and deliver the verification error.
    ops.extend([10, 1, 202002, 11 + 100 * end, 6, 107, 8]);
    let path = Path::new("unused-with-injected-transport");
    let refusal = prove_via(&client, path, path, &|_, _| Ok(Value::Null), || {
        clock.store(end, SeqCst);
        Err(Error::Verify)
    })
    .unwrap();
    assert_eq!(refusal.label, Label::CpuFallback);
    let actual = client.breaker().state();
    let states = oracle_states(
        binary.as_ref(),
        &t.states[0],
        &ops,
        &vec![vec![]; ops.len()],
    );
    let expected = states.last().unwrap();
    eprintln!(
        "in-flight failure at {end}: model failures {} openUntil {}, client failures {:?} openUntil {}",
        expected["brFails"], expected["brOpenUntil"], actual.failures, actual.open_until
    );
    assert_eq!(expected["brFails"], json!(actual.failures));
    assert_eq!(expected["brOpenUntil"], actual.open_until);
}

#[path = "oracle_itf.rs"]
mod itf;
