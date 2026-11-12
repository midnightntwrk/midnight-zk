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

//! Runs workloads and collects [`crate::results`] records.

use std::{fmt, process::Command, thread, time::Instant};

use midnight_proofs::profiling;

use crate::{
    report::format_duration,
    results::{Breakdown, CaseResult, Environment, RunResult, SCHEMA_VERSION},
    stats::Stats,
    workload::{Pcs, Prepared, Workload},
};

/// What to run and how to measure it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    /// Substrings of workload names. A workload is selected if its name
    /// contains any of them, and all are if the list is empty.
    pub filter: Vec<String>,
    /// The schemes to run under, or `None` for all those each workload
    /// supports. Unsupported combinations are skipped.
    pub pcs: Option<Vec<Pcs>>,
    /// The sizes of the rayon pools to prove in. Repetitions are ignored.
    pub threads: Vec<usize>,
    /// The number of timed proofs per case.
    pub samples: usize,
    /// The number of untimed proofs that precede the timed ones.
    pub warmup: usize,
    /// Whether to verify the last proof of each case.
    pub verify: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            filter: Vec::new(),
            pcs: None,
            threads: vec![1, max_threads()],
            samples: 5,
            warmup: 1,
            verify: true,
        }
    }
}

/// The reason a run produced no result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// The configuration cannot be run as given.
    InvalidConfig(String),
    /// No workload matched the filter under any of the requested schemes.
    NothingToRun,
    /// The thread pool of a case could not be built.
    ThreadPool {
        /// The requested number of threads.
        threads: usize,
        /// The error reported by rayon.
        reason: String,
    },
    /// A workload produced a proof that its own verifier rejects.
    VerificationFailed {
        /// The name of the workload.
        workload: String,
        /// The scheme it ran under.
        pcs: Pcs,
        /// The number of threads of the pool.
        threads: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidConfig(reason) => write!(f, "invalid configuration: {reason}"),
            Error::NothingToRun => f.write_str("no workloads matched"),
            Error::ThreadPool { threads, reason } => {
                write!(f, "cannot build a pool of {threads} threads: {reason}")
            }
            Error::VerificationFailed {
                workload,
                pcs,
                threads,
            } => write!(
                f,
                "the proof of {workload} under {pcs} with {threads} threads does not verify"
            ),
        }
    }
}

impl std::error::Error for Error {}

/// The number of logical cores available to this process.
pub fn max_threads() -> usize {
    thread::available_parallelism().map_or(1, usize::from)
}

/// The workloads of `workloads` selected by `config`, each with the schemes
/// to run it under. Requested schemes a workload does not support are
/// reported on stderr and left out.
pub fn select<'a>(
    config: &Config,
    workloads: &'a [Box<dyn Workload>],
) -> Vec<(&'a dyn Workload, Vec<Pcs>)> {
    let matches = |name: &str| {
        config.filter.is_empty() || config.filter.iter().any(|f| name.contains(f.as_str()))
    };
    let mut selected = Vec::new();
    for workload in workloads.iter().filter(|w| matches(w.name())) {
        let supported = workload.supported_pcs();
        let pcs: Vec<Pcs> = match &config.pcs {
            None => supported,
            Some(requested) => {
                let mut pcs = Vec::new();
                for p in requested {
                    if !supported.contains(p) {
                        eprintln!("skipping {} under {p}: not supported", workload.name());
                    } else if !pcs.contains(p) {
                        pcs.push(*p);
                    }
                }
                pcs
            }
        };
        if !pcs.is_empty() {
            selected.push((workload.as_ref(), pcs));
        }
    }
    selected
}

/// Times the prover of the selected `workloads` as `config` describes.
///
/// Progress goes to stderr. Each case proves inside a dedicated rayon pool,
/// so the global pool does not affect the measurements.
pub fn run(config: &Config, workloads: Vec<Box<dyn Workload>>) -> Result<RunResult, Error> {
    if config.samples == 0 {
        return Err(Error::InvalidConfig(
            "at least one sample is required".into(),
        ));
    }
    if config.threads.is_empty() || config.threads.contains(&0) {
        return Err(Error::InvalidConfig(
            "thread counts must be positive integers".into(),
        ));
    }
    let mut threads = Vec::new();
    for t in &config.threads {
        if !threads.contains(t) {
            threads.push(*t);
        }
    }

    let selected = select(config, &workloads);
    let nb_cases = selected.iter().map(|(_, pcs)| pcs.len()).sum::<usize>() * threads.len();
    if nb_cases == 0 {
        return Err(Error::NothingToRun);
    }

    if profiling::ENABLED {
        eprintln!(
            "warning: this build records the kernel breakdown, which slows the prover down; \
             its timings are not reference numbers"
        );
    }

    let mut cases = Vec::with_capacity(nb_cases);
    for (workload, pcs_list) in selected {
        for pcs in pcs_list {
            eprintln!("{} {pcs}: setup", workload.name());
            let mut prepared = workload.setup(pcs);
            let (k, vk_hash) = (prepared.k(), prepared.vk_hash());
            let scheme = prepared.scheme();
            for &threads in &threads {
                eprint!(
                    "[{}/{nb_cases}] {} {scheme} k={k} threads={threads}: ",
                    cases.len() + 1,
                    workload.name(),
                );
                let measured = measure(prepared.as_mut(), threads, config)?.ok_or_else(|| {
                    eprintln!("verification failed");
                    Error::VerificationFailed {
                        workload: workload.name().to_owned(),
                        pcs,
                        threads,
                    }
                })?;
                let stats = Stats::of(&measured.samples_ns).expect("there is a sample");
                eprintln!(
                    "median {} (±{:.1}%)",
                    format_duration(stats.median),
                    stats.mad_percent()
                );
                cases.push(CaseResult {
                    workload: workload.name().to_owned(),
                    pcs,
                    scheme: scheme.clone(),
                    threads,
                    k,
                    vk_hash: vk_hash.clone(),
                    proof_bytes: measured.proof_bytes,
                    samples_ns: measured.samples_ns,
                    breakdown: measured.breakdown,
                });
            }
        }
    }

    Ok(RunResult {
        schema_version: SCHEMA_VERSION,
        environment: environment(),
        cases,
    })
}

/// The measurements of one case.
struct Measured {
    samples_ns: Vec<u64>,
    proof_bytes: usize,
    breakdown: Option<Breakdown>,
}

/// Proves `config.warmup + config.samples` times in a pool of `threads`
/// threads, timing the latter. Returns `None` if the last proof is checked
/// and does not verify.
fn measure(
    prepared: &mut dyn Prepared,
    threads: usize,
    config: &Config,
) -> Result<Option<Measured>, Error> {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().map_err(|e| {
        Error::ThreadPool {
            threads,
            reason: e.to_string(),
        }
    })?;
    Ok(pool.install(move || {
        for _ in 0..config.warmup {
            prepared.prove();
        }
        let mut samples_ns = Vec::with_capacity(config.samples);
        let mut proof = Vec::new();
        let mut breakdown = None;
        for _ in 0..config.samples {
            profiling::reset();
            let start = Instant::now();
            let new_proof = prepared.prove();
            let elapsed = start.elapsed();
            let report = profiling::take_report();
            samples_ns.push(elapsed.as_nanos() as u64);
            // Assigned after the clock stops so that freeing the previous
            // proof is not measured.
            proof = new_proof;
            if profiling::ENABLED {
                breakdown = Some(Breakdown::from(&report));
            }
        }
        if config.verify && !prepared.verify(&proof) {
            return None;
        }
        Some(Measured {
            samples_ns,
            proof_bytes: proof.len(),
            breakdown,
        })
    }))
}

/// Describes the machine and the build.
pub fn environment() -> Environment {
    Environment {
        commit: git_commit(),
        cpu: std::fs::read_to_string("/proc/cpuinfo").ok().and_then(|s| cpu_model(&s)),
        logical_cores: max_threads(),
        os: format!("{} {}", std::env::consts::OS, std::env::consts::ARCH),
        profiling: profiling::ENABLED,
    }
}

/// The CPU model in the contents of `/proc/cpuinfo`.
fn cpu_model(cpuinfo: &str) -> Option<String> {
    cpuinfo.lines().find_map(|line| {
        let (key, value) = line.split_once(':')?;
        (key.trim() == "model name").then(|| value.trim().to_owned())
    })
}

/// The commit of the source tree this binary was built from, with a `-dirty`
/// suffix if the tree has uncommitted changes.
fn git_commit() -> Option<String> {
    let git = |args: &[&str]| {
        let output = Command::new("git")
            .args(["-C", env!("CARGO_MANIFEST_DIR")])
            .args(args)
            .output()
            .ok()?;
        output
            .status
            .success()
            .then(|| String::from_utf8_lossy(&output.stdout).into_owned())
    };
    let commit = git(&["rev-parse", "--short=12", "HEAD"])?;
    let dirty = !git(&["status", "--porcelain"])?.trim().is_empty();
    Some(format!(
        "{}{}",
        commit.trim(),
        if dirty { "-dirty" } else { "" }
    ))
}

#[cfg(test)]
mod tests {
    use std::{
        sync::{Arc, Mutex},
        time::Duration,
    };

    use super::*;
    use crate::report;

    /// What a fake workload was asked to do.
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Event {
        Setup(Pcs),
        /// A proof, with the size of the pool it ran in.
        Prove(usize),
        Verify,
    }

    type Log = Arc<Mutex<Vec<Event>>>;

    /// A workload whose prover sleeps.
    struct Fake {
        name: &'static str,
        pcs: Vec<Pcs>,
        sound: bool,
        log: Log,
    }

    impl Fake {
        fn boxed(name: &'static str, pcs: &[Pcs], log: &Log) -> Box<dyn Workload> {
            Box::new(Fake {
                name,
                pcs: pcs.to_vec(),
                sound: true,
                log: log.clone(),
            })
        }
    }

    impl Workload for Fake {
        fn name(&self) -> &'static str {
            self.name
        }

        fn supported_pcs(&self) -> Vec<Pcs> {
            self.pcs.clone()
        }

        fn setup(&self, pcs: Pcs) -> Box<dyn Prepared> {
            self.log.lock().unwrap().push(Event::Setup(pcs));
            Box::new(FakePrepared {
                proof_bytes: if pcs == Pcs::Kzg { 100 } else { 60 },
                sound: self.sound,
                nb_proofs: 0,
                log: self.log.clone(),
            })
        }
    }

    struct FakePrepared {
        proof_bytes: usize,
        sound: bool,
        nb_proofs: u8,
        log: Log,
    }

    impl Prepared for FakePrepared {
        fn k(&self) -> u32 {
            7
        }

        fn scheme(&self) -> String {
            "fake".to_owned()
        }

        fn vk_hash(&self) -> String {
            "ab".repeat(32)
        }

        fn prove(&mut self) -> Vec<u8> {
            thread::sleep(Duration::from_millis(1));
            self.log.lock().unwrap().push(Event::Prove(rayon::current_num_threads()));
            self.nb_proofs += 1;
            vec![self.nb_proofs; self.proof_bytes]
        }

        fn verify(&self, proof: &[u8]) -> bool {
            self.log.lock().unwrap().push(Event::Verify);
            self.sound && proof == vec![self.nb_proofs; self.proof_bytes]
        }
    }

    fn config(threads: &[usize]) -> Config {
        Config {
            threads: threads.to_vec(),
            samples: 2,
            warmup: 1,
            ..Config::default()
        }
    }

    #[test]
    fn end_to_end() {
        let log = Log::default();
        let workloads = vec![
            Fake::boxed("alpha", &Pcs::ALL, &log),
            Fake::boxed("beta", &[Pcs::Kzg], &log),
        ];
        let result = run(&config(&[1, 2, 1]), workloads).unwrap();

        assert_eq!(result.schema_version, SCHEMA_VERSION);
        assert_eq!(result.environment.profiling, profiling::ENABLED);
        assert_eq!(result.environment.logical_cores, max_threads());
        assert!(result.environment.os.contains(std::env::consts::ARCH));

        let shape: Vec<_> =
            result.cases.iter().map(|c| (c.workload.as_str(), c.pcs, c.threads)).collect();
        assert_eq!(
            shape,
            [
                ("alpha", Pcs::Kzg, 1),
                ("alpha", Pcs::Kzg, 2),
                ("alpha", Pcs::Fflonk, 1),
                ("alpha", Pcs::Fflonk, 2),
                ("beta", Pcs::Kzg, 1),
                ("beta", Pcs::Kzg, 2),
            ]
        );
        for case in &result.cases {
            assert_eq!(case.k, 7);
            assert_eq!(case.vk_hash, "ab".repeat(32));
            assert_eq!(
                case.proof_bytes,
                if case.pcs == Pcs::Kzg { 100 } else { 60 }
            );
            assert_eq!(case.samples_ns.len(), 2);
            assert!(case.samples_ns.iter().all(|&ns| ns >= 1_000_000));
            assert_eq!(case.breakdown.is_some(), profiling::ENABLED);
        }

        // One setup per workload and scheme, then for each pool one warmup
        // proof, two samples and one verification.
        let case = |threads| [vec![Event::Prove(threads); 3], vec![Event::Verify]].concat();
        let per_pcs = |pcs| [vec![Event::Setup(pcs)], case(1), case(2)].concat();
        let expected = [per_pcs(Pcs::Kzg), per_pcs(Pcs::Fflonk), per_pcs(Pcs::Kzg)].concat();
        assert_eq!(*log.lock().unwrap(), expected);

        let json = serde_json::to_string(&result).unwrap();
        assert_eq!(serde_json::from_str::<RunResult>(&json).unwrap(), result);

        let summary = report::render_summary(&result);
        let markdown = report::render_markdown(&result, "2026-01-01");
        for name in ["alpha", "beta"] {
            assert_eq!(
                summary.lines().filter(|l| l.starts_with(name)).count(),
                result.cases.iter().filter(|c| c.workload == name).count()
            );
            assert!(markdown.contains(&format!("| {name}")));
        }
        assert!(markdown.contains("## 1 thread\n"));
        assert!(markdown.contains("## 2 threads\n"));
        assert_eq!(markdown.contains("## Breakdown"), profiling::ENABLED);
    }

    #[test]
    fn filter_and_pcs_selection() {
        let log = Log::default();
        let workloads = || {
            vec![
                Fake::boxed("alpha", &Pcs::ALL, &log),
                Fake::boxed("beta", &[Pcs::Kzg], &log),
                Fake::boxed("gamma", &Pcs::ALL, &log),
            ]
        };
        let names = |config: &Config| -> Vec<(String, Pcs)> {
            let result = run(config, workloads()).unwrap();
            result.cases.into_iter().map(|c| (c.workload, c.pcs)).collect()
        };

        let filtered = Config {
            filter: vec!["lph".into(), "amm".into()],
            pcs: Some(vec![Pcs::Fflonk]),
            verify: false,
            ..config(&[1])
        };
        assert_eq!(
            names(&filtered),
            [
                ("alpha".to_owned(), Pcs::Fflonk),
                ("gamma".to_owned(), Pcs::Fflonk)
            ]
        );
        assert!(!log.lock().unwrap().contains(&Event::Verify));

        // The only scheme `beta` supports is not requested.
        let fflonk_only = Config {
            pcs: Some(vec![Pcs::Fflonk]),
            ..config(&[1])
        };
        assert!(names(&fflonk_only).iter().all(|(name, _)| name != "beta"));
    }

    #[test]
    fn nothing_to_run() {
        let log = Log::default();
        assert_eq!(run(&config(&[1]), vec![]), Err(Error::NothingToRun));

        let no_match = Config {
            filter: vec!["delta".into()],
            ..config(&[1])
        };
        let workloads = vec![Fake::boxed("alpha", &Pcs::ALL, &log)];
        assert_eq!(run(&no_match, workloads), Err(Error::NothingToRun));
        assert!(log.lock().unwrap().is_empty());
    }

    #[test]
    fn invalid_config() {
        let log = Log::default();
        let workloads = || vec![Fake::boxed("alpha", &Pcs::ALL, &log)];
        let no_samples = Config {
            samples: 0,
            ..config(&[1])
        };
        for bad in [no_samples, config(&[]), config(&[1, 0])] {
            assert!(matches!(
                run(&bad, workloads()),
                Err(Error::InvalidConfig(_))
            ));
        }
    }

    #[test]
    fn failed_verification_names_the_case() {
        let log = Log::default();
        let unsound = || -> Vec<Box<dyn Workload>> {
            vec![Box::new(Fake {
                name: "broken",
                pcs: vec![Pcs::Fflonk],
                sound: false,
                log: log.clone(),
            })]
        };
        let error = run(&config(&[2]), unsound()).unwrap_err();
        assert_eq!(
            error,
            Error::VerificationFailed {
                workload: "broken".into(),
                pcs: Pcs::Fflonk,
                threads: 2
            }
        );
        let message = error.to_string();
        assert!(message.contains("broken") && message.contains("fflonk"));

        let unverified = Config {
            verify: false,
            ..config(&[2])
        };
        assert!(run(&unverified, unsound()).is_ok());
    }

    #[test]
    fn cpu_model_from_cpuinfo() {
        let cpuinfo = "processor\t: 0\nmodel\t\t: 97\nmodel name\t: Some CPU 9000 @ 3GHz\n\
                       processor\t: 1\nmodel name\t: Another\n";
        assert_eq!(cpu_model(cpuinfo).as_deref(), Some("Some CPU 9000 @ 3GHz"));
        assert_eq!(cpu_model("Processor : ARMv8\n"), None);
    }
}
