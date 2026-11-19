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

//! The resident prover: SRS, keys and device state held between requests.

use std::time::Instant;

use ff::PrimeField;
use midnight_curves::Bls12;
use midnight_proofs::{
    poly::kzg::params::{ParamsKZG, ParamsVerifierKZG},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{KZG, MidnightPK, MidnightVK, Relation};
use rand::{CryptoRng, RngCore, rngs::OsRng};

use crate::{
    Error,
    admission::{self, Admission, Ladder, Step},
    config::{Config, ResidentPolicy, RunMode},
    device::{self, Device, Phases},
    input::SecretBytes,
    lock::Lease,
    need::DeviceNeed,
    report::{self, Label, MsmRecord, PolicyRecord, ProofRecord, StartRecord},
};

/// A relation the service can serve: a ZK standard library [`Relation`]
/// plus the decoding of a request's input bytes into its instance and
/// witness.
pub trait ServedRelation:
    Relation<Instance: Send + Sync, Witness: Send, Error: Send> + Send + Sync + 'static
{
    /// A short name for the start record (no secret, no path).
    fn name(&self) -> String;

    /// Decodes the input bytes of a request. The bytes hold witness data:
    /// an implementation must not log them or keep a copy beyond the
    /// returned values. An error text must not quote the bytes.
    fn decode_input(&self, input: &[u8]) -> Result<(Self::Instance, Self::Witness), String>;

    /// The circuit size (log2 of the row count) to use, or `None` for
    /// [`midnight_zk_stdlib::optimal_k`].
    fn k(&self) -> Option<u32> {
        None
    }
}

/// A predicate the service polls while it proves: `true` means the request
/// lost its reason to use the device (the client hung up, or the lease was
/// lost).
pub type Cancel = std::sync::Arc<dyn Fn() -> bool + Send + Sync>;

/// How often the service polls [`RequestOptions::cancel`] during a proof.
pub const CANCEL_POLL: std::time::Duration = std::time::Duration::from_millis(20);

/// Options of one request.
#[derive(Default)]
pub struct RequestOptions {
    /// Read every wiped device region back (in addition to the config).
    pub zero_check: bool,
    /// The caller's hold of the device lock, if it passed one.
    pub lease: Option<Lease>,
    /// The reason the lease was refused, for the record.
    pub lease_refused: Option<&'static str>,
    /// Polled every [`CANCEL_POLL`] while the proof runs. When it returns
    /// `true`, the device phases are withdrawn ([`Device::revoke`]), the rest
    /// of the proof runs on the CPU, one fallback is counted, and the
    /// erasure still runs.
    pub cancel: Option<Cancel>,
}

impl std::fmt::Debug for RequestOptions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RequestOptions")
            .field("zero_check", &self.zero_check)
            .field("lease", &self.lease)
            .field("lease_refused", &self.lease_refused)
            .field("cancel", &self.cancel.is_some())
            .finish()
    }
}

/// Why a service stopped serving.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Retirement {
    /// The erasure of a request could not be confirmed. The process must not
    /// take more witness data.
    Erasure(String),
    /// A request went past a configured memory bound. A restarted process
    /// may serve again.
    Bound(String),
}

impl Retirement {
    /// The reason text.
    pub fn reason(&self) -> &str {
        match self {
            Retirement::Erasure(r) | Retirement::Bound(r) => r,
        }
    }
}

/// A served proof: the bytes and the record.
#[derive(Clone, Debug)]
pub struct Served {
    /// The proof, verified.
    pub proof: Vec<u8>,
    /// The record.
    pub record: ProofRecord,
}

/// The resident prover of one relation.
///
/// Built once: it loads the SRS (passed in), generates the keys, checks the
/// verifying key against the configured pin, computes the device memory
/// need, and writes nothing to the device. Each request then admits its
/// device phases, proves, wipes, verifies the proof with the stock verifier
/// and returns it with a record.
pub struct ProverService<R: ServedRelation> {
    config: Config,
    relation: R,
    params: ParamsKZG<Bls12>,
    verifier_params: ParamsVerifierKZG<Bls12>,
    vk: MidnightVK<KZG>,
    pk: MidnightPK<R, KZG>,
    device: Box<dyn Device>,
    pool: rayon::ThreadPool,
    wsl: bool,
    phases: Phases,
    need: DeviceNeed,
    start: StartRecord,
    served: u64,
    requests: u64,
    current: Option<u64>,
    retired: Option<Retirement>,
    #[cfg(test)]
    observed_admission: Option<std::sync::mpsc::Sender<Admission>>,
}

impl<R: ServedRelation> std::fmt::Debug for ProverService<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProverService")
            .field("relation", &self.start.relation)
            .field("k", &self.start.k)
            .field("served", &self.served)
            .finish_non_exhaustive()
    }
}

/// The SHA-256 of a verifying key in `SerdeFormat::RawBytes`.
pub fn vk_sha256(vk: &MidnightVK<KZG>) -> String {
    let mut buf = Vec::new();
    vk.vk()
        .write(&mut buf, SerdeFormat::RawBytes)
        .expect("writing to a Vec does not fail");
    report::sha256_hex(&buf)
}

/// Reads an SRS file (`SerdeFormat::RawBytesUnchecked`).
pub fn read_srs(path: &std::path::Path) -> Result<ParamsKZG<Bls12>, Error> {
    // the path and the reader's message are not repeated: a client passes
    // its own SRS path to the in-process fallback
    let f = std::fs::File::open(path)
        .map_err(|e| Error::Config(format!("the SRS file cannot be opened: {}", e.kind())))?;
    ParamsKZG::read_custom(
        &mut std::io::BufReader::new(f),
        SerdeFormat::RawBytesUnchecked,
    )
    .map_err(|_| Error::Config("the SRS file is not an SRS in raw format".into()))
}

fn public_inputs_sha256(pi: &[midnight_curves::Fq]) -> String {
    let mut b = Vec::with_capacity(32 * pi.len());
    for x in pi {
        b.extend_from_slice(x.to_repr().as_ref());
    }
    report::sha256_hex(&b)
}

impl<R: ServedRelation> ProverService<R> {
    /// Builds the service with the device of [`device::detect`].
    pub fn new(relation: R, params: ParamsKZG<Bls12>, config: Config) -> Result<Self, Error> {
        let d = device::detect(config.device);
        Self::with_device(relation, params, config, d)
    }

    /// Builds the service with an explicit device layer.
    pub fn with_device(
        relation: R,
        mut params: ParamsKZG<Bls12>,
        config: Config,
        device: Box<dyn Device>,
    ) -> Result<Self, Error> {
        config.validate()?;
        let k = relation.k().unwrap_or_else(|| midnight_zk_stdlib::optimal_k(&relation));
        if k > config.max_k {
            return Err(Error::Refused(format!(
                "the circuit has k = {k}, above max_k = {}",
                config.max_k
            )));
        }
        if params.max_k() < k {
            return Err(Error::Refused(format!(
                "the SRS has k = {}, below the circuit's k = {k}",
                params.max_k()
            )));
        }
        let wsl = config.wsl_active();
        if wsl && config.resident == ResidentPolicy::Keep {
            return Err(Error::Refused(
                "resident = keep under the WSL2 profile: the device is exclusive only under the lock, so nothing may stay on it between requests".into(),
            ));
        }
        if params.max_k() > k {
            params.downsize(k);
        }
        let threads = config.thread_count();
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .thread_name(|i| format!("prover-{i}"))
            .build()
            .map_err(|e| Error::Config(format!("thread pool: {e}")))?;
        let t = Instant::now();
        let (vk, pk) = pool.install(|| {
            let vk = midnight_zk_stdlib::setup_vk::<R, KZG>(&params, &relation);
            let pk = midnight_zk_stdlib::setup_pk::<R, KZG>(&relation, &vk);
            (vk, pk)
        });
        let keygen_s = t.elapsed().as_secs_f64();
        let vk_hash = vk_sha256(&vk);
        if let Some(pin) = &config.vk_sha256
            && *pin != vk_hash
        {
            return Err(Error::Refused(format!(
                "the verifying key has SHA-256 {vk_hash}, the configured pin is {pin}"
            )));
        }
        let cs = pk.pk().get_vk().cs();
        let ext_k = pk.pk().get_vk().get_domain().extended_k();
        let info = device.info();
        device.set_keep(config.resident == ResidentPolicy::Keep);
        let shape = info.as_ref().and_then(|_| device.shape(pk.pk()));
        let margin = config.margin_mib << 20;
        let (phases, need) = match (&info, &shape) {
            (None, _) => (Phases::NONE, DeviceNeed::default()),
            (Some(_), Some(s)) => (Phases::ALL, DeviceNeed::of(s, margin)),
            (Some(_), None) => (
                Phases::ALL.without(Phases::QUOTIENT),
                DeviceNeed::without_quotient(k, ext_k, margin),
            ),
        };
        let held_none = device::Held::default();
        let held_all = device::Held {
            resident: need.resident,
            tables: 2 * need.table_points(),
        };
        let start = StartRecord {
            relation: relation.name(),
            k,
            extended_k: ext_k,
            degree: cs.degree(),
            advice_columns: cs.num_advice_columns(),
            fixed_columns: cs.num_fixed_columns(),
            instance_columns: cs.num_instance_columns(),
            lookups: cs.lookups().len(),
            trashcans: cs.trashcans().len(),
            permutation_columns: cs.permutation().get_columns().len(),
            shape,
            resident_polys: shape.map(|s| s.resident_polys).unwrap_or(0),
            device: info,
            cuda_visible_devices: std::env::var("CUDA_VISIBLE_DEVICES").ok(),
            features: device::build_features(),
            binary_sha256: report::binary_sha256(),
            phases,
            policy: PolicyRecord {
                resident: config.resident,
                mode: config.mode,
                wait_s: config.wait_s,
                margin_mib: config.margin_mib,
                lock: config.lock_path.is_some(),
                wsl,
                wsl_reserve_mib: config.wsl_reserve_mib,
                zero_check: config.zero_check,
            },
            need,
            need_cold: need.of_phases(phases, held_none),
            need_warm: need.of_phases(phases, held_all),
            threads,
            vk_sha256: vk_hash,
            keygen_s,
        };
        let verifier_params = params.verifier_params();
        Ok(ProverService {
            config,
            relation,
            params,
            verifier_params,
            vk,
            pk,
            device,
            pool,
            wsl,
            phases,
            need,
            start,
            served: 0,
            requests: 0,
            current: None,
            retired: None,
            #[cfg(test)]
            observed_admission: None,
        })
    }

    /// The start record.
    pub fn start_record(&self) -> &StartRecord {
        &self.start
    }

    /// The configuration.
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// The verifying key.
    pub fn vk(&self) -> &MidnightVK<KZG> {
        &self.vk
    }

    /// The verifier parameters.
    pub fn verifier_params(&self) -> &ParamsVerifierKZG<Bls12> {
        &self.verifier_params
    }

    /// The relation.
    pub fn relation(&self) -> &R {
        &self.relation
    }

    /// Proofs served so far: verified and returned.
    pub fn served(&self) -> u64 {
        self.served
    }

    /// The id of the last request that got one (ids are given after the
    /// input decodes), `None` before.
    pub fn last_request(&self) -> Option<u64> {
        self.current
    }

    /// Why the service stopped serving, if it did (an erasure that could
    /// not be confirmed).
    pub fn retired(&self) -> Option<&str> {
        self.retired.as_ref().map(Retirement::reason)
    }

    /// Why the service retired, if it did.
    pub fn retirement(&self) -> Option<&Retirement> {
        self.retired.as_ref()
    }

    /// Device bytes held now.
    pub fn held(&self) -> device::Held {
        self.device.held()
    }

    /// Frees the resident proving-key copies (and with `tables` the MSM
    /// tables). Returns the bytes freed.
    pub fn evict(&self, tables: bool) -> u64 {
        self.device.evict(tables)
    }

    /// Proves one request with fresh randomness from the operating system.
    pub fn prove(&mut self, input: &SecretBytes, opts: RequestOptions) -> Result<Served, Error> {
        self.prove_with(input, opts, OsRng, None)
    }

    /// Proves with a seeded RNG. For byte-identity tests only: a seeded proof
    /// is not zero knowledge. The feature turns on the test switches of the
    /// hook layer, which seed the quotient limb blinding too, so equal inputs
    /// and seeds give equal proof bytes.
    #[cfg(feature = "test-seed")]
    pub fn prove_seeded(
        &mut self,
        input: &SecretBytes,
        opts: RequestOptions,
        seed: u64,
    ) -> Result<Served, Error> {
        use rand::SeedableRng;
        let rng = rand_chacha::ChaCha20Rng::seed_from_u64(seed);
        // the stock quotient limb blinding draws from the operating system;
        // the hook layer's test switch seeds it
        midnight_proofs::gpu::test_switches::set_quotient_blinding_seed(Some(seed));
        let r = self.prove_with(input, opts, rng, None);
        midnight_proofs::gpu::test_switches::set_quotient_blinding_seed(None);
        r
    }

    fn admit(&self, opts: &RequestOptions) -> Admission {
        if self.phases.is_empty() {
            return admission::no_lease(Phases::NONE);
        }
        let leased = opts.lease.is_some();
        if self.config.lock_path.is_some() && !leased {
            return admission::no_lease(self.phases);
        }
        let dev = &*self.device;
        if !self.wsl {
            // measure the free memory: before the context exists the device
            // layer cannot read it (another process may hold it)
            dev.activate();
        }
        let free = || dev.mem().map(|m| m.free).unwrap_or(0);
        let held = || dev.held();
        let evict = |t: bool| {
            dev.evict(t);
        };
        let l = Ladder {
            need: &self.need,
            phases: self.phases,
            wait_s: self.config.wait_s,
            poll: std::time::Duration::from_millis(250),
            free: &free,
            held: &held,
            evict: &evict,
        };
        if self.wsl {
            let total = dev.mem().map(|m| m.total).unwrap_or(0);
            admission::admit_wsl(
                &l,
                leased,
                admission::wsl_budget(total, self.config.wsl_reserve_mib),
            )
        } else {
            admission::admit(&l)
        }
    }

    /// The request path. `prover` replaces the stock prover in tests of the
    /// verify-before-return rule.
    #[allow(clippy::type_complexity)]
    pub(crate) fn prove_with(
        &mut self,
        input: &SecretBytes,
        opts: RequestOptions,
        rng: impl RngCore + CryptoRng + Send,
        prover: Option<&dyn Fn(&[u8]) -> Vec<u8>>,
    ) -> Result<Served, Error> {
        if let Some(r) = &self.retired {
            return Err(Error::Retired(r.reason().to_string()));
        }
        self.current = None;
        // fixed texts: the decoder's own error or panic may carry witness data
        let decoded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.relation.decode_input(input.as_slice())
        }));
        let (instance, witness) = match decoded {
            Ok(Ok(v)) => v,
            Ok(Err(_)) => {
                return Err(Error::Input(
                    "the input does not decode to an instance and a witness of the relation".into(),
                ));
            }
            Err(_) => return Err(Error::Input("the relation's input decoder panicked".into())),
        };
        if R::format_committed_instances(&witness).is_some() {
            return Err(Error::Input(
                "relations with a committed instance are not supported by the service".into(),
            ));
        }
        // fixed texts: a relation's own error may carry witness data
        let pi = R::format_instance(&instance)
            .map_err(|_| Error::Input("the instance cannot be formatted".into()))?;
        self.requests += 1;
        let request = self.requests;
        self.current = Some(request);
        let adm = self.admit(&opts);
        #[cfg(test)]
        if let Some(observer) = &self.observed_admission {
            observer.send(adm).expect("observe admission");
        }
        let mut reasons: Vec<String> = Vec::new();
        if let Some(r) =
            opts.lease_refused.filter(|_| adm.reason == Some(admission::NO_LEASE_REASON))
        {
            reasons.push(format!("{}: {r}", admission::NO_LEASE_REASON));
        } else if let Some(r) = adm.reason {
            reasons.push(r.to_string());
        }
        if self.start.device.is_some() && !self.phases.contains(Phases::QUOTIENT) {
            reasons.push("the device quotient does not take this key: quotient on the CPU".into());
        }
        // acceptance mode: any phase off the device fails the request
        // before any device work
        let acceptance = self.config.mode == RunMode::Acceptance;
        if acceptance && !reasons.is_empty() {
            return Err(Error::Degraded(reasons.join("; ")));
        }

        self.device.reset_counters();
        let check = opts.zero_check || self.config.zero_check;
        // every request starts its own erasure counters, also one admitted
        // to the CPU (which skips the preparation)
        self.device.begin_wipe(check);
        if !adm.phases.is_empty() {
            self.device.prepare(&self.params, self.pk.pk(), check);
        }
        // the request's cancel check runs before each device phase launch
        self.device.set_gate(opts.cancel.clone());
        let admitted = self.device.begin_request(adm.phases);
        if admitted != adm.phases {
            reasons.push("the device layer took fewer phases than admitted".into());
        }
        report::reset_host_hwm();
        let t = Instant::now();
        let cancelled = std::sync::atomic::AtomicBool::new(false);
        let done = std::sync::atomic::AtomicBool::new(false);
        let result = std::thread::scope(|scope| {
            let (device, cancel) = (&self.device, opts.cancel.clone());
            let (done_ref, cancelled_ref) = (&done, &cancelled);
            if let Some(cancel) = cancel.filter(|_| !admitted.is_empty()) {
                // a client that hung up before the proof starts: no device
                // phase runs
                if cancel() {
                    if device.revoke() {
                        cancelled_ref.store(true, std::sync::atomic::Ordering::Release);
                    }
                    // withdrawn once: no watcher
                } else {
                    scope.spawn(move || {
                        use std::sync::atomic::Ordering::{Acquire, Release};
                        while !done_ref.load(Acquire) {
                            if cancel() {
                                if device.revoke() {
                                    cancelled_ref.store(true, Release);
                                }
                                return;
                            }
                            std::thread::sleep(CANCEL_POLL);
                        }
                    });
                }
            }
            #[cfg(test)]
            self.device.observe_proving();
            let (params, pk, relation) = (&self.params, &self.pk, &self.relation);
            let r = self.pool.install(move || {
                // a panic in the relation's circuit code is a failed proof;
                // its message never leaves the process (see
                // `report::withhold_panic_messages`)
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    midnight_zk_stdlib::prove::<R, blake2b_simd::State, KZG>(
                        params, pk, relation, &instance, witness, rng,
                    )
                }))
                .map_err(|_| ())
                .and_then(|r| r.map_err(|_| ()))
            });
            done.store(true, std::sync::atomic::Ordering::Release);
            r
        });
        let prove_s = t.elapsed().as_secs_f64();
        self.device.set_gate(None);
        if self.device.withdrawn() {
            cancelled.store(true, std::sync::atomic::Ordering::Release);
        }
        let mut counters = self.device.counters();
        if admitted.is_empty() {
            // no device phase ran: a peak the device layer still reports is
            // an earlier request's (it resets only when a request starts on
            // the device)
            counters.peak_bytes = 0;
        }
        if cancelled.load(std::sync::atomic::Ordering::Acquire) {
            counters.fallbacks.push(device::Fallback {
                phase: "request".into(),
                reason: "the client hung up or the lease was lost: the rest ran on the CPU".into(),
                count: 1,
            });
        }
        // the erasure runs whatever the prover returned
        let wipe = self.device.end_request(opts.zero_check || self.config.zero_check);
        let evicted = match self.config.resident {
            ResidentPolicy::Evict => self.device.evict(true),
            ResidentPolicy::Keep => 0,
        };
        let host_hwm = report::host_hwm_bytes();
        drop(opts.lease);
        let wipe = match wipe {
            Ok(w) => w,
            Err(e) => {
                let msg =
                    format!("the erasure of the request's device buffers was not confirmed: {e}");
                self.retired = Some(Retirement::Erasure(msg.clone()));
                return Err(Error::Retired(msg));
            }
        };
        // the memory bounds hold on every completed outcome: the reply of
        // the outcome goes out, then the daemon retires
        if let Some(b) = self.bound_overrun(request, counters.peak_bytes, host_hwm) {
            self.retired = Some(Retirement::Bound(b));
        }
        let mut proof = result.map_err(|_| Error::Prove("the prover failed".into()))?;
        if let Some(p) = prover {
            proof = p(&proof);
        }
        if counters.fallback_count() > 0 {
            reasons.push(format!(
                "{} device call(s) fell back to the CPU",
                counters.fallback_count()
            ));
        }
        if acceptance && !reasons.is_empty() {
            return Err(Error::Degraded(reasons.join("; ")));
        }

        let verify_s = match self.verify(&pi, &proof) {
            Ok(v) => v,
            Err(e) => {
                eprintln!(
                    "{}",
                    serde_json::json!({"event": "verify-failed", "data": {"request": request}})
                );
                return Err(e);
            }
        };

        // GPU-085 with GPU-012: no call served on the device is `cpu`; a
        // served call and a real fallback (shape, unreduced, memory, fault,
        // device-error, or a withdrawn request) is `gpu-degraded`; else
        // `gpu`. Expected declines (below the size threshold, no device) are
        // no fallback, and the admission alone never marks the label: its
        // reasons stay in `degraded_reasons` (GPU-023)
        let ran = counters.calls.values().sum::<u64>() > 0;
        let label = if admitted.is_empty() || !ran {
            Label::Cpu
        } else if counters.fallback_count() > 0 {
            Label::GpuDegraded
        } else {
            Label::Gpu
        };
        let step = if admitted.is_empty() && !adm.phases.is_empty() {
            Step::Cpu
        } else {
            adm.step
        };
        let record = ProofRecord {
            request,
            label,
            step,
            configured: self.phases,
            admitted,
            degraded_reasons: reasons,
            need: adm.need,
            free: adm.free,
            admission_wait_s: adm.waited_s,
            prove_s,
            phase_s: counters.phase_seconds.clone(),
            verify_s,
            msm: MsmRecord {
                count: counters.msm_count,
                seconds: counters.msm_seconds,
            },
            device_calls: counters.calls.clone(),
            fallback_count: counters.fallback_count(),
            fallbacks: counters.fallbacks.clone(),
            device_peak_bytes: counters.peak_bytes,
            host_hwm_bytes: host_hwm,
            evicted_bytes: evicted,
            // the first proof this process serves (a failed request before
            // it does not warm the process)
            cold: self.served == 0,
            declines: counters.declines.clone(),
            wipe,
            proof_bytes: proof.len(),
            proof_sha256: report::sha256_hex(&proof),
            public_inputs_sha256: public_inputs_sha256(&pi),
        };
        self.served += 1;
        Ok(Served { proof, record })
    }

    /// The configured memory bound `record` went past, if any.
    fn bound_overrun(&self, request: u64, device_peak: u64, host_hwm: u64) -> Option<String> {
        let mib = |b: u64| b.div_ceil(1 << 20);
        let (dev, host) = (
            self.config.max_device_peak_mib,
            self.config.max_host_hwm_mib,
        );
        if dev > 0 && mib(device_peak) > dev {
            return Some(format!(
                "request {} reached {} MiB of device memory, above the bound of {dev} MiB",
                request,
                mib(device_peak)
            ));
        }
        if host > 0 && mib(host_hwm) > host {
            return Some(format!(
                "request {} reached a host high-water mark of {} MiB, above the bound of {host} MiB",
                request,
                mib(host_hwm)
            ));
        }
        None
    }

    /// Verifies `proof` for the public inputs `pi` with the stock verifier.
    /// Returns the verifier seconds.
    fn verify(&self, pi: &[midnight_curves::Fq], proof: &[u8]) -> Result<f64, Error> {
        use midnight_proofs::{
            plonk::prepare,
            poly::commitment::Guard,
            transcript::{CircuitTranscript, Transcript},
        };
        let t = Instant::now();
        // the instance layout of `midnight_zk_stdlib::prove` without a
        // committed instance: an empty first column, then the public inputs
        let instances: [&[midnight_curves::Fq]; 2] = [&[], pi];
        let mut transcript = CircuitTranscript::<blake2b_simd::State>::init_from_bytes(proof);
        let ok =
            prepare::<midnight_curves::Fq, KZG, _>(self.vk.vk(), &[], &instances, &mut transcript)
                .ok()
                .filter(|_| transcript.assert_empty().is_ok())
                .map(|g| g.verify(&self.verifier_params).is_ok())
                .unwrap_or(false);
        if !ok {
            return Err(Error::Verify);
        }
        Ok(t.elapsed().as_secs_f64())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::example::{PoseidonPreimage, example_input};

    fn service() -> ProverService<PoseidonPreimage> {
        use rand::SeedableRng;
        let r = PoseidonPreimage;
        let k = midnight_zk_stdlib::optimal_k(&r);
        let params = ParamsKZG::unsafe_setup(k, rand_chacha::ChaCha8Rng::seed_from_u64(1));
        let cfg = Config {
            threads: 2,
            ..Config::default()
        };
        ProverService::with_device(r, params, cfg, Box::new(device::NoDevice)).unwrap()
    }

    #[test]
    fn verify_before_return_refuses_a_bad_proof() {
        let mut s = service();
        let input = SecretBytes::new(example_input(3));
        let ok = s.prove_with(&input, RequestOptions::default(), OsRng, None).unwrap();
        assert_eq!(ok.record.label, Label::Cpu);
        assert_eq!(ok.record.proof_sha256, report::sha256_hex(&ok.proof));
        // a prover that flips one byte: the verifier refuses, nothing is
        // returned
        let flip = |p: &[u8]| {
            let mut v = p.to_vec();
            v[10] ^= 1;
            v
        };
        let e = s.prove_with(&input, RequestOptions::default(), OsRng, Some(&flip)).unwrap_err();
        assert!(matches!(e, Error::Verify), "{e}");
        let trunc = |p: &[u8]| p[..p.len() - 1].to_vec();
        assert!(matches!(
            s.prove_with(&input, RequestOptions::default(), OsRng, Some(&trunc)),
            Err(Error::Verify)
        ));
    }

    /// QA4 ORACLE-03: a memory bound is checked on a verify failure too: the
    /// error goes out, then the service retires.
    #[test]
    fn bound_is_checked_when_verification_fails() {
        let mut s = service();
        s.config.max_host_hwm_mib = 1;
        let input = SecretBytes::new(example_input(3));
        let flip = |p: &[u8]| {
            let mut v = p.to_vec();
            v[10] ^= 1;
            v
        };
        let e = s.prove_with(&input, RequestOptions::default(), OsRng, Some(&flip)).unwrap_err();
        assert!(matches!(e, Error::Verify), "{e}");
        assert!(matches!(s.retirement(), Some(Retirement::Bound(_))));
    }

    /// Minor 9 and 13: a proof that fails verification is not served, and
    /// its request id is known for the failure log.
    #[test]
    fn served_counts_only_verified_proofs() {
        let mut s = service();
        let input = SecretBytes::new(example_input(3));
        let flip = |p: &[u8]| {
            let mut v = p.to_vec();
            v[10] ^= 1;
            v
        };
        let e = s.prove_with(&input, RequestOptions::default(), OsRng, Some(&flip)).unwrap_err();
        assert!(matches!(e, Error::Verify), "{e}");
        assert_eq!(s.served(), 0);
        assert_eq!(s.last_request(), Some(1));
        s.prove(&input, RequestOptions::default()).unwrap();
        assert_eq!(s.served(), 1);
    }
}

#[cfg(test)]
pub(crate) mod oracle_conformance;
