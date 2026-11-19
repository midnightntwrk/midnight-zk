// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `compact-bench`: proves Compact proof preimages through the proof-server call
//! path (key material -> `midnight_zkir::IrSource::prove` -> zk-stdlib ->
//! `midnight_proofs::plonk::create_proof`), verifies each proof with the stock
//! verifier and appends one row per repetition to a TSV file.
//!
//! ```text
//! compact-bench info
//! compact-bench check     --jobs JOBS --params DIR
//! compact-bench prove     --jobs JOBS --params DIR --raw RAW.tsv [--reps N] [--warmup N]
//!                         [--lock FILE] [--max-load L] [--filter TEXT] [--dump DIR]
//!                         [--max-prove-s S] [--max-device-bytes B] [--max-host-bytes B]
//!                         [--yield-foreign C] [--rep R]
//! compact-bench verify    --jobs JOBS --params DIR --dump DIR --statements DIR --out OUT.tsv
//! compact-bench summarize --raw RAW.tsv --out SUMMARY.tsv [--exclude P1,P2] [--binary SHA]
//! ```
//!
//! `prove --dump DIR` writes each proof and its statement (public inputs) to
//! `DIR`. `verify` checks dumped proofs with this binary's verifier: build it
//! stock to check the proofs of a hooked build. It verifies each proof against
//! the statement in `--statements` (a dump of a stock run) and compares the
//! statements and the proof bytes.
//!
//! `prove` is resumable: it skips every (binary, job, repetition) that the raw
//! file already holds. With `--lock`, it takes the lock file before each proof
//! and releases it after; when another process holds the lock, it exits with
//! code 75 at that proof boundary, and a rerun continues from there.
//!
//! `--rep R` runs only repetition `R` (0 is the first run, which is reported
//! apart) of each job, so that a wrapper can split a timed set into one process
//! per repetition. For a timed repetition, the first proof of each job runs
//! first and is not recorded.
//!
//! `--max-load L` waits for a 1-minute load below `L` before the first proof
//! and labels each row `quiet` or `busy` by the load before that proof
//! (`quiet_gate`). `--max-prove-s`, `--max-device-bytes` and `--max-host-bytes`
//! are bounds: a row that exceeds one is written and the run stops with exit
//! code 3. A repetition in which a hook fell back to the CPU (`fallbacks` > 0)
//! writes no row and stops the run with exit code 5. `--yield-foreign C` stops with exit code 75 after a proof (all its
//! repetitions, at least 1 s) during which other processes kept more than `C`
//! CPU cores busy on average, so that a wrapper can wait for a quiet machine
//! outside the lock and resume. (The 1-minute load cannot serve for this check:
//! it includes this process's own threads.) With this option the start check
//! does not wait either: a 1-minute load at or above `--max-load` ends the run
//! with exit 75.

mod dump;
mod gpu;
mod host;
mod jobs;
mod params;
mod summary;

use std::{
    collections::{BTreeMap, HashSet},
    fs::{File, OpenOptions},
    io::{Cursor, Write},
    path::PathBuf,
    time::{Duration, Instant},
};

use futures_executor::block_on;
use midnight_serialize::tagged_deserialize;
use midnight_transient_crypto::{
    curve::Fr,
    proofs::{PARAMS_VERIFIER, Proof, VerifierKey, Zkir},
};
use midnight_zkir::IrSource;
use rand_chacha::{ChaCha20Rng, rand_core::SeedableRng};
use sha2::{Digest, Sha256};

/// Exit code when another process holds the lock (`EX_TEMPFAIL`).
const EXIT_YIELD: i32 = 75;

/// Exit code when a row exceeds a configured bound.
const EXIT_BOUND: i32 = 3;
/// Exit code when a hook fell back to the CPU during a repetition.
const EXIT_DEGRADED: i32 = 5;

/// Writes one repetition's row. A repetition in which a hook fell back to the
/// CPU is degraded: it is not a measurement of the device path, so no row is
/// written and the run fails.
fn write_rep(
    out: &mut impl Write,
    fixed: &[String],
    row: &[String],
    fallbacks: u64,
) -> Result<(), String> {
    if fallbacks > 0 {
        return Err(format!(
            "{fallbacks} hook call(s) fell back to the CPU: degraded repetition, no row written"
        ));
    }
    writeln!(out, "{}\t{}", fixed.join("\t"), row.join("\t")).map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())
}

/// Columns of the raw TSV, one row per proof repetition.
pub const RAW_HEADER: &[&str] = &[
    "backend",
    "proofs_source",
    "binary_sha256",
    "rustc",
    "cpu_model",
    "gpu_model",
    "threads",
    "job",
    "program",
    "circuit",
    "key_program",
    "k",
    "rep",
    "key_load_s",
    "prove_s",
    "verify_s",
    "verified",
    "proof_bytes",
    "proof_sha256",
    "load1_before",
    "foreign_cores",
    "unix_time",
    "hooks_device",
    "hits_msm",
    "hits_ntt",
    "hits_coset",
    "hits_quotient",
    "fallbacks",
    "load1_after",
    "quiet_gate",
    "gpu_driver",
    "ready_s",
    "device_peak_bytes",
    "host_hwm_bytes",
];

/// Columns that every raw file has, also files written before the hook
/// columns were added.
pub const BASE_COLUMNS: usize = 22;

/// The backend label of the result rows, from what was installed: `stock`
/// without the `gpu` feature, `hooked` when the backend installed its hooks on a
/// device, `hooked-inactive` when a `gpu` build installed none.
fn backend(device: &Option<String>) -> &'static str {
    match (cfg!(feature = "gpu"), device) {
        (false, _) => "stock",
        (true, Some(_)) => "hooked",
        (true, None) => "hooked-inactive",
    }
}

struct Args(BTreeMap<String, String>);

impl Args {
    fn parse(v: &[String]) -> Self {
        let mut m = BTreeMap::new();
        let mut it = v.iter();
        while let Some(a) = it.next() {
            let key = a.strip_prefix("--").unwrap_or_else(|| panic!("unexpected argument {a}"));
            let val = it.next().unwrap_or_else(|| panic!("--{key} needs a value"));
            m.insert(key.to_string(), val.clone());
        }
        Args(m)
    }
    fn get(&self, k: &str) -> Option<&str> {
        self.0.get(k).map(String::as_str)
    }
    fn req(&self, k: &str) -> &str {
        self.get(k).unwrap_or_else(|| panic!("missing --{k}"))
    }
    fn num<T: std::str::FromStr>(&self, k: &str, d: T) -> T {
        self.get(k)
            .map(|v| v.parse().unwrap_or_else(|_| panic!("bad --{k}")))
            .unwrap_or(d)
    }
}

/// Key material of one circuit, decoded as the proof server decodes a
/// `ProvingKeyMaterial`.
struct Material {
    ir: IrSource,
    pk: midnight_transient_crypto::proofs::ProverKey<IrSource>,
    vk: VerifierKey,
    k: u8,
}

fn load_material(job: &jobs::Job) -> Material {
    let read =
        |p: &PathBuf| std::fs::read(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
    let ir = IrSource::load_ir_from_tagged(Cursor::new(read(&job.ir))).expect("decode ZKIR");
    let pk = IrSource::load_prover_key_from_tagged(Cursor::new(read(&job.prover_key)))
        .expect("decode prover key");
    let vk: VerifierKey =
        tagged_deserialize(&mut &read(&job.verifier_key)[..]).expect("decode verifier key");
    let k = pk.init().expect("init prover key").k();
    vk.init().expect("init verifier key");
    Material { ir, pk, vk, k }
}

fn seed(job: &str) -> [u8; 32] {
    Sha256::digest(format!("compact-bench/{job}").as_bytes()).into()
}

fn cmd_info() {
    let device = gpu::install();
    println!("backend\t{}", backend(&device));
    println!("hooks_device\t{}", device.as_deref().unwrap_or("-"));
    println!("proofs_source\t{}", env!("BENCH_PROOFS_SOURCE"));
    println!("rustc\t{}", env!("BENCH_RUSTC"));
    println!("binary_sha256\t{}", host::binary_sha256());
    println!("cpu_model\t{}", host::cpu_model());
    println!("gpu_model\t{}", host::gpu_model());
    println!("threads\t{}", rayon::current_num_threads());
}

/// Runs the stock ZKIR check on every job, and a control with a wrong
/// commitment randomness that must be refused.
fn cmd_check(a: &Args) -> i32 {
    let jobs = jobs::read_jobs(a.req("jobs"));
    let mut bad = 0;
    for job in &jobs {
        let m = load_material(job);
        let pre = job.load_preimage();
        let ok = m.ir.check(&pre).is_ok();
        let control = match pre.communications_commitment {
            Some((c, r)) => {
                let mut wrong = pre.clone();
                wrong.communications_commitment = Some((c, r + Fr::from(1u64)));
                if m.ir.check(&wrong).is_err() {
                    "refused"
                } else {
                    "ACCEPTED"
                }
            }
            None => "no-comm",
        };
        if !ok || control == "ACCEPTED" {
            bad += 1;
        }
        println!(
            "{}\tk={}\tcheck={}\tcontrol={control}",
            job.job,
            m.k,
            if ok { "ok" } else { "FAIL" }
        );
    }
    println!("{} jobs, {} failed", jobs.len(), bad);
    i32::from(bad > 0)
}

fn done_rows(raw: &str, binary: &str) -> HashSet<(String, u32)> {
    let mut done = HashSet::new();
    let Ok(s) = std::fs::read_to_string(raw) else {
        return done;
    };
    let header = s.lines().next().unwrap_or("");
    assert!(
        s.is_empty() || header == RAW_HEADER.join("\t"),
        "{raw} has another column set; write to a new file"
    );
    let col = |n: &str| RAW_HEADER.iter().position(|h| *h == n).unwrap();
    let (cb, cj, cr) = (col("binary_sha256"), col("job"), col("rep"));
    for l in s.lines().skip(1) {
        let f: Vec<&str> = l.split('\t').collect();
        if f.len() == RAW_HEADER.len() && f[cb] == binary {
            done.insert((f[cj].to_string(), f[cr].parse().unwrap_or(u32::MAX)));
        }
    }
    done
}

fn cmd_prove(a: &Args) -> i32 {
    let jobs = jobs::read_jobs(a.req("jobs"));
    let params = params::ParamsCache::new(PathBuf::from(a.req("params")));
    let raw = a.req("raw");
    let reps: u32 = a.num("reps", 5);
    let warmup: u32 = a.num("warmup", 1);
    let max_load: f64 = a.num("max-load", f64::INFINITY);
    let max_prove_s: f64 = a.num("max-prove-s", f64::INFINITY);
    let yield_foreign: f64 = a.num("yield-foreign", f64::INFINITY);
    let max_device: u64 = a.num("max-device-bytes", u64::MAX);
    let max_host: u64 = a.num("max-host-bytes", u64::MAX);
    let started = Instant::now();
    let driver = host::gpu_driver();
    let mut ready_s: Option<f64> = None;
    let filter = a.get("filter").unwrap_or("");
    let dump_dir = a.get("dump").map(PathBuf::from);
    if let Some(d) = &dump_dir {
        std::fs::create_dir_all(d).expect("create dump directory");
    }
    let device = gpu::install();
    let hooks_device = device.clone().unwrap_or_else(|| "-".into()).replace('\t', " ");
    if cfg!(feature = "gpu") && device.is_none() {
        eprintln!("warning: gpu build, but the backend installed no hooks (hooked-inactive)");
    }

    let binary = host::binary_sha256();
    let fixed = [
        backend(&device).to_string(),
        env!("BENCH_PROOFS_SOURCE").to_string(),
        binary.clone(),
        env!("BENCH_RUSTC").to_string(),
        host::cpu_model(),
        host::gpu_model(),
        rayon::current_num_threads().to_string(),
    ];
    let done = done_rows(raw, &binary);
    let new_file = std::fs::metadata(raw).map(|m| m.len() == 0).unwrap_or(true);
    let mut out = OpenOptions::new().create(true).append(true).open(raw).expect("open raw TSV");
    if new_file {
        writeln!(out, "{}", RAW_HEADER.join("\t")).unwrap();
    }

    // With --yield-foreign the caller gates on load outside the lock: a busy
    // machine at start ends the run with exit 75 instead of a wait under the lock.
    let l = if yield_foreign.is_finite() {
        let l = host::load1();
        if l >= max_load {
            eprintln!("load {l:.2} >= {max_load:.2} at start: stopping (exit 75)");
            return EXIT_YIELD;
        }
        l
    } else {
        host::wait_quiet(max_load, Duration::from_secs(15))
    };
    eprintln!(
        "start: load {l:.2}, {} threads, backend {}",
        fixed[6], fixed[0]
    );

    let total = warmup + reps;
    let wanted: Vec<u32> = match a.get("rep") {
        None => (0..total).collect(),
        Some(_) => {
            let r: u32 = a.num("rep", 0);
            assert!(
                r < total,
                "--rep {r} is not below --warmup + --reps ({total})"
            );
            vec![r]
        }
    };
    let only_timed = wanted.len() == 1 && wanted[0] >= warmup && total > 1;
    for job in jobs.iter().filter(|j| j.job.contains(filter)) {
        if wanted.iter().all(|&r| done.contains(&(job.job.clone(), r))) {
            continue;
        }
        let _lock = match a.get("lock") {
            None => None,
            Some(p) => {
                let f = File::options().create(true).append(true).open(p).expect("open lock");
                match f.try_lock() {
                    Ok(()) => Some(f),
                    Err(_) => {
                        eprintln!(
                            "lock {p} is held by another process: stopping before {}",
                            job.job
                        );
                        return EXIT_YIELD;
                    }
                }
            }
        };
        let job_t = Instant::now();
        let job_s0 = host::CpuSample::now();
        let t = Instant::now();
        let m = load_material(job);
        let pre = job.load_preimage();
        params.prover(m.k).expect("read prover params");
        let pv = params.verifier(m.k).expect("read verifier params");
        let key_load_s = t.elapsed().as_secs_f64();

        if only_timed && warmup > 0 {
            // A timed repetition alone in this process: run the first proof
            // first, unrecorded, so that the timed one sees the same warm state
            // as in a full run.
            let rng = ChaCha20Rng::from_seed(seed(&job.job));
            if let Err(e) = block_on(m.ir.prove(rng, &params, m.pk.clone(), &pre)) {
                panic!("prove {}: {e:#}", job.job);
            }
        }

        for &rep in &wanted {
            if done.contains(&(job.job.clone(), rep)) {
                continue;
            }
            let load_before = host::load1();
            let s0 = host::CpuSample::now();
            let rng = ChaCha20Rng::from_seed(seed(&job.job));
            let ready = *ready_s.get_or_insert(started.elapsed().as_secs_f64());
            gpu::reset();
            host::reset_hwm();
            let t = Instant::now();
            let res = block_on(m.ir.prove(rng, &params, m.pk.clone(), &pre));
            let prove_s = t.elapsed().as_secs_f64();
            let s1 = host::CpuSample::now();
            let hits = gpu::hits();
            let host_hwm = host::hwm_bytes();
            let load_after = host::load1();
            let gate = if max_load.is_infinite() {
                "off"
            } else if load_before < max_load {
                "quiet"
            } else {
                "busy"
            };
            let (proof, pis): (Proof, Vec<Fr>) = match res {
                Ok((p, pis, _)) => (p, pis),
                Err(e) => panic!("prove {}: {e:#}", job.job),
            };
            let t = Instant::now();
            // The proof server's self-check (verifier parameters from the k file)
            // and the ledger's verifier parameters.
            let v_server = m.vk.verify(&pv, &proof, pis.iter().copied()).is_ok();
            let verify_s = t.elapsed().as_secs_f64();
            let v_ledger = m.vk.verify(&PARAMS_VERIFIER, &proof, pis.iter().copied()).is_ok();
            let verified = v_server && v_ledger;
            let row = [
                job.job.clone(),
                job.program.clone(),
                job.circuit.clone(),
                job.key_program.clone(),
                m.k.to_string(),
                rep.to_string(),
                format!("{key_load_s:.4}"),
                format!("{prove_s:.4}"),
                format!("{verify_s:.4}"),
                verified.to_string(),
                proof.0.len().to_string(),
                hex::encode(Sha256::digest(&proof.0)),
                format!("{load_before:.2}"),
                format!("{:.3}", s0.foreign_cores(&s1, prove_s)),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_secs())
                    .unwrap_or(0)
                    .to_string(),
                hooks_device.clone(),
                hits.msm.to_string(),
                hits.ntt.to_string(),
                hits.coset.to_string(),
                hits.quotient.to_string(),
                hits.fallbacks.to_string(),
                format!("{load_after:.2}"),
                format!("{gate}<{max_load}"),
                driver.clone(),
                format!("{ready:.3}"),
                hits.device_peak_bytes.to_string(),
                host_hwm.to_string(),
            ];
            if let Err(e) = write_rep(&mut out, &fixed, &row, hits.fallbacks) {
                eprintln!("{} rep {rep}: {e}", job.job);
                return EXIT_DEGRADED;
            }
            if let Some(d) = &dump_dir {
                dump::write(d, &job.job, rep, m.k, &proof, &pis);
            }
            eprintln!(
                "{}\tk={}\trep={rep}\t{prove_s:.3}s\tverified={verified}",
                job.job, m.k
            );
            if !verified {
                eprintln!("verification failed: {}", job.job);
                return 1;
            }
            if prove_s > max_prove_s || hits.device_peak_bytes > max_device || host_hwm > max_host {
                eprintln!(
                    "bound exceeded by {} rep {rep}: prove {prove_s:.3} s (max {max_prove_s}), \
                     device peak {} B (max {max_device}), host high-water {host_hwm} B (max {max_host})",
                    job.job, hits.device_peak_bytes
                );
                return EXIT_BOUND;
            }
        }
        // Other processes became busy during this proof: stop at the proof
        // boundary so that the caller can wait for a quiet machine (outside any
        // lock) and resume.
        let wall = job_t.elapsed().as_secs_f64();
        let foreign = job_s0.foreign_cores(&host::CpuSample::now(), wall);
        if wall >= 1.0 && foreign > yield_foreign {
            eprintln!(
                "other processes used {foreign:.2} cores during {}: stopping (exit 75)",
                job.job
            );
            return EXIT_YIELD;
        }
    }
    0
}

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    let cmd = argv.get(1).map(String::as_str).unwrap_or("info");
    let a = Args::parse(argv.get(2..).unwrap_or(&[]));
    let code = match cmd {
        "info" => {
            cmd_info();
            0
        }
        "check" => cmd_check(&a),
        "prove" => cmd_prove(&a),
        "summarize" => summary::run(&a),
        "verify" => dump::verify(&a),
        _ => {
            eprintln!("usage: compact-bench info|check|prove|verify|summarize [--option value]...");
            2
        }
    };
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::write_rep;

    fn strings(v: &[&str]) -> Vec<String> {
        v.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn degraded_rep_writes_no_row_and_fails() {
        let mut out = Vec::new();
        let r = write_rep(&mut out, &strings(&["hooked"]), &strings(&["job", "1"]), 1);
        assert!(r.is_err(), "a rep with a CPU fallback must fail");
        assert!(
            out.is_empty(),
            "a rep with a CPU fallback must write no row"
        );
    }

    #[test]
    fn clean_rep_writes_its_row() {
        let mut out = Vec::new();
        write_rep(&mut out, &strings(&["hooked"]), &strings(&["job", "1"]), 0).unwrap();
        assert_eq!(String::from_utf8(out).unwrap(), "hooked\tjob\t1\n");
    }
}
