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

//! Compares two result files.
//!
//! Cases are matched on (workload, pcs, threads). For every matched case the
//! comparison reports the median of each side and the change of the head
//! median relative to the base median, where a negative change means that
//! the head is faster.
//!
//! # Significance rule
//!
//! A change is reported as `faster` or `slower` only if its magnitude exceeds
//! both the threshold ([`DEFAULT_THRESHOLD_PERCENT`] unless overridden) and
//! the noise of the two sample sets; otherwise it is `within noise`. The
//! noise test depends on the number of samples:
//!
//! - With at least [`MIN_SAMPLES_FOR_MAD`] samples on both sides, the noise is
//!   `2 * sqrt(s_base^2 + s_head^2)`, where `s = 1.4826 * MAD / median` is the
//!   robust relative standard deviation of one side. This is the spread of
//!   single samples and not the smaller standard error of the median: samples
//!   of one run share the state of the machine, so they are not independent and
//!   the standard error would understate the noise.
//! - With fewer samples (but at least two per side), the change must separate
//!   the two sets completely: their `[min, max]` ranges must not overlap. The
//!   noise shown is then the wider of the two relative ranges.
//! - With a single sample on either side there is no noise estimate. The
//!   threshold alone decides, and the report says so.
//!
//! # Warnings
//!
//! The comparison warns when the two files do not describe like-for-like
//! measurements: a different verifying key, `k` or proof size for a case, or
//! a different machine.

use std::{
    collections::{HashMap, hash_map::Entry},
    fmt, fs,
    process::ExitCode,
};

use crate::{
    results::{CaseResult, Environment, RunResult, SCHEMA_VERSION},
    workload::Pcs,
};

/// The smallest change, in percent, that is reported as significant by
/// default.
pub const DEFAULT_THRESHOLD_PERCENT: f64 = 2.0;

/// The number of samples per side from which the noise is estimated with the
/// median absolute deviation instead of the sample ranges.
pub const MIN_SAMPLES_FOR_MAD: usize = 5;

// Scales a median absolute deviation into an estimate of the standard
// deviation of normally distributed data.
const MAD_TO_SIGMA: f64 = 1.4826;

const USAGE: &str = "\
Usage: midnight-benchmarks compare <base.json> <head.json> [options]

Options:
  --threshold <percent>   smallest change reported as significant (default 2)
  --markdown              print GitHub-flavoured markdown instead of plain text
  --fail-on-regression    exit with status 1 if a case is significantly slower
  -h, --help              print this help

Exit status: 0 on success, 1 on a significant regression with
--fail-on-regression, 2 if the arguments or the files are invalid.";

/// What identifies a case across result files.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CaseKey {
    /// The name of the workload.
    pub workload: String,
    /// The polynomial commitment scheme.
    pub pcs: Pcs,
    /// The number of threads of the rayon pool.
    pub threads: usize,
}

impl CaseKey {
    fn of(case: &CaseResult) -> Self {
        CaseKey {
            workload: case.workload.clone(),
            pcs: case.pcs,
            threads: case.threads,
        }
    }
}

impl fmt::Display for CaseKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let plural = if self.threads == 1 { "" } else { "s" };
        write!(
            f,
            "{} / {} / {} thread{plural}",
            self.workload, self.pcs, self.threads
        )
    }
}

/// The classification of the change of one case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The head is significantly faster than the base.
    Faster,
    /// The head is significantly slower than the base.
    Slower,
    /// The change is below the threshold or the noise.
    WithinNoise,
    /// One side has no samples, or the base median is zero.
    NoData,
}

impl Verdict {
    /// The name used in the table.
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Faster => "faster",
            Verdict::Slower => "slower",
            Verdict::WithinNoise => "within noise",
            Verdict::NoData => "no data",
        }
    }
}

/// How the noise of a case was estimated, see the [module docs](self).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoiseRule {
    /// From the median absolute deviations of both sides.
    Mad,
    /// From the `[min, max]` ranges of both sides.
    Range,
    /// Not estimated, because a side has a single sample.
    Unknown,
}

/// The timings of one matched case.
#[derive(Clone, Debug, PartialEq)]
pub struct Timing {
    /// The median of the base samples, in nanoseconds.
    pub base_median_ns: f64,
    /// The median of the head samples, in nanoseconds.
    pub head_median_ns: f64,
    /// The change of the head median relative to the base median, in percent.
    /// Negative means that the head is faster.
    pub delta_percent: f64,
    /// The noise estimate in percent, or `None` under [`NoiseRule::Unknown`].
    pub noise_percent: Option<f64>,
    /// How the noise was estimated.
    pub noise_rule: NoiseRule,
}

/// The comparison of one case present in both files.
#[derive(Clone, Debug, PartialEq)]
pub struct CaseComparison {
    /// The identity of the case.
    pub key: CaseKey,
    /// `k` in the base and in the head.
    pub k: (u32, u32),
    /// The proof size in bytes in the base and in the head.
    pub proof_bytes: (usize, usize),
    /// The verifying key digest in the base and in the head.
    pub vk_hash: (String, String),
    /// The number of samples in the base and in the head.
    pub samples: (usize, usize),
    /// The timings, or `None` under [`Verdict::NoData`].
    pub timing: Option<Timing>,
    /// The classification of the change.
    pub verdict: Verdict,
}

impl CaseComparison {
    /// Whether the two builds produced different verifying keys, so that the
    /// timings are not of the same circuit.
    pub fn vk_differs(&self) -> bool {
        self.vk_hash.0 != self.vk_hash.1
    }
}

/// The comparison of two runs.
#[derive(Clone, Debug, PartialEq)]
pub struct Comparison {
    /// The conditions of the base run.
    pub base_environment: Environment,
    /// The conditions of the head run.
    pub head_environment: Environment,
    /// The threshold in percent the verdicts were computed with.
    pub threshold_percent: f64,
    /// The cases present in both runs, in the order of the base.
    pub cases: Vec<CaseComparison>,
    /// The cases present in the base only.
    pub only_base: Vec<CaseKey>,
    /// The cases present in the head only.
    pub only_head: Vec<CaseKey>,
    /// Reasons why the comparison may not be like for like.
    pub warnings: Vec<String>,
}

impl Comparison {
    /// The number of cases with the given verdict.
    pub fn count(&self, verdict: Verdict) -> usize {
        self.cases.iter().filter(|c| c.verdict == verdict).count()
    }

    /// Whether some case is significantly slower in the head.
    pub fn has_regression(&self) -> bool {
        self.count(Verdict::Slower) > 0
    }
}

/// Order statistics of one sample set.
struct Spread {
    n: usize,
    median: f64,
    min: f64,
    max: f64,
    // The robust relative standard deviation, `1.4826 * MAD / median`.
    rel_sigma: f64,
}

fn median(sorted: &[f64]) -> f64 {
    let mid = sorted.len() / 2;
    if sorted.len() % 2 == 1 {
        sorted[mid]
    } else {
        (sorted[mid - 1] + sorted[mid]) / 2.0
    }
}

/// Returns `None` if there are no samples.
fn spread(samples_ns: &[u64]) -> Option<Spread> {
    let mut sorted: Vec<f64> = samples_ns.iter().map(|&s| s as f64).collect();
    sorted.sort_by(f64::total_cmp);
    let (&min, &max) = (sorted.first()?, sorted.last()?);
    let median_ns = median(&sorted);
    let mut deviations: Vec<f64> = sorted.iter().map(|s| (s - median_ns).abs()).collect();
    deviations.sort_by(f64::total_cmp);
    let rel_sigma = if median_ns > 0.0 {
        MAD_TO_SIGMA * median(&deviations) / median_ns
    } else {
        0.0
    };
    Some(Spread {
        n: sorted.len(),
        median: median_ns,
        min,
        max,
        rel_sigma,
    })
}

fn classify(base: &[u64], head: &[u64], threshold_percent: f64) -> (Option<Timing>, Verdict) {
    let (Some(b), Some(h)) = (spread(base), spread(head)) else {
        return (None, Verdict::NoData);
    };
    if b.median <= 0.0 {
        return (None, Verdict::NoData);
    }
    let delta_percent = (h.median - b.median) / b.median * 100.0;

    let (noise_rule, noise_percent, beyond_noise) = if b.n < 2 || h.n < 2 {
        (NoiseRule::Unknown, None, true)
    } else if b.n < MIN_SAMPLES_FOR_MAD || h.n < MIN_SAMPLES_FOR_MAD {
        let rel_range = |s: &Spread| (s.max - s.min) / s.median.max(1.0) * 100.0;
        let disjoint = h.max < b.min || h.min > b.max;
        (
            NoiseRule::Range,
            Some(rel_range(&b).max(rel_range(&h))),
            disjoint,
        )
    } else {
        let noise = 2.0 * (b.rel_sigma.powi(2) + h.rel_sigma.powi(2)).sqrt() * 100.0;
        (NoiseRule::Mad, Some(noise), delta_percent.abs() > noise)
    };

    let verdict = if delta_percent.abs() > threshold_percent && beyond_noise {
        if delta_percent < 0.0 {
            Verdict::Faster
        } else {
            Verdict::Slower
        }
    } else {
        Verdict::WithinNoise
    };
    let timing = Timing {
        base_median_ns: b.median,
        head_median_ns: h.median,
        delta_percent,
        noise_percent,
        noise_rule,
    };
    (Some(timing), verdict)
}

fn index<'a>(
    run: &'a RunResult,
    side: &str,
    warnings: &mut Vec<String>,
) -> HashMap<CaseKey, &'a CaseResult> {
    let mut map = HashMap::new();
    for case in &run.cases {
        match map.entry(CaseKey::of(case)) {
            Entry::Vacant(e) => {
                e.insert(case);
            }
            Entry::Occupied(e) => warnings.push(format!(
                "{} appears more than once in the {side} file; only its first entry is compared",
                e.key()
            )),
        }
    }
    map
}

fn environment_warnings(base: &Environment, head: &Environment, warnings: &mut Vec<String>) {
    if base.cpu != head.cpu {
        let name = |cpu: &Option<String>| cpu.clone().unwrap_or_else(|| "unknown".to_owned());
        warnings.push(format!(
            "DIFFERENT CPU: base ran on `{}`, head on `{}`; the timings are not comparable",
            name(&base.cpu),
            name(&head.cpu)
        ));
    }
    if base.logical_cores != head.logical_cores {
        warnings.push(format!(
            "DIFFERENT CORE COUNT: base ran with {} logical cores, head with {}",
            base.logical_cores, head.logical_cores
        ));
    }
    if base.os != head.os {
        warnings.push(format!(
            "DIFFERENT OS: base ran on `{}`, head on `{}`",
            base.os, head.os
        ));
    }
}

fn short_hash(hash: &str) -> &str {
    hash.get(..12).unwrap_or(hash)
}

/// Compares two runs with the [`DEFAULT_THRESHOLD_PERCENT`].
pub fn compare(base: &RunResult, head: &RunResult) -> Comparison {
    compare_with_threshold(base, head, DEFAULT_THRESHOLD_PERCENT)
}

/// Compares two runs, reporting as significant only the changes that exceed
/// `threshold_percent` and the noise, see the [module docs](self).
pub fn compare_with_threshold(
    base: &RunResult,
    head: &RunResult,
    threshold_percent: f64,
) -> Comparison {
    let mut warnings = Vec::new();
    environment_warnings(&base.environment, &head.environment, &mut warnings);
    let base_cases = index(base, "base", &mut warnings);
    let head_cases = index(head, "head", &mut warnings);

    let mut cases = Vec::new();
    let mut only_base = Vec::new();
    let mut seen = Vec::new();
    for b in &base.cases {
        let key = CaseKey::of(b);
        if seen.contains(&key) {
            continue;
        }
        seen.push(key.clone());
        let Some(h) = head_cases.get(&key) else {
            only_base.push(key);
            continue;
        };

        if b.vk_hash != h.vk_hash {
            warnings.push(format!(
                "VK HASH MISMATCH for {key}: base {}, head {}; the two builds do not prove the \
                 same circuit, so the delta is not a like-for-like comparison",
                short_hash(&b.vk_hash),
                short_hash(&h.vk_hash)
            ));
        }
        if b.k != h.k {
            warnings.push(format!("DIFFERENT K for {key}: base {}, head {}", b.k, h.k));
        }
        if b.proof_bytes != h.proof_bytes {
            warnings.push(format!(
                "DIFFERENT PROOF SIZE for {key}: base {} bytes, head {} bytes",
                b.proof_bytes, h.proof_bytes
            ));
        }

        let (timing, verdict) = classify(&b.samples_ns, &h.samples_ns, threshold_percent);
        match &timing {
            None => warnings.push(format!("NO DATA for {key}: a side has no usable samples")),
            Some(t) if t.noise_rule == NoiseRule::Unknown => warnings.push(format!(
                "SINGLE SAMPLE for {key}: the noise cannot be estimated, the verdict rests on \
                 the threshold alone"
            )),
            Some(_) => {}
        }
        cases.push(CaseComparison {
            key,
            k: (b.k, h.k),
            proof_bytes: (b.proof_bytes, h.proof_bytes),
            vk_hash: (b.vk_hash.clone(), h.vk_hash.clone()),
            samples: (b.samples_ns.len(), h.samples_ns.len()),
            timing,
            verdict,
        });
    }

    let mut only_head = Vec::new();
    for h in &head.cases {
        let key = CaseKey::of(h);
        if !base_cases.contains_key(&key) && !only_head.contains(&key) {
            only_head.push(key);
        }
    }

    Comparison {
        base_environment: base.environment.clone(),
        head_environment: head.environment.clone(),
        threshold_percent,
        cases,
        only_base,
        only_head,
        warnings,
    }
}

/// A table that renders as aligned text or as markdown.
struct Table {
    // The name of each column and whether it is right-aligned.
    columns: Vec<(&'static str, bool)>,
    rows: Vec<Vec<String>>,
}

impl Table {
    fn render(&self, markdown: bool, indent: &str, out: &mut String) {
        // Counts characters, not bytes, so that non-ASCII cells stay aligned.
        let width = |s: &str| s.chars().count();
        let widths: Vec<usize> = (0..self.columns.len())
            .map(|i| {
                let cells = self.rows.iter().map(|row| width(&row[i]));
                cells.chain([width(self.columns[i].0), 3]).max().unwrap()
            })
            .collect();
        let pad = |cell: &str, i: usize| {
            let fill = " ".repeat(widths[i] - width(cell));
            if self.columns[i].1 {
                format!("{fill}{cell}")
            } else {
                format!("{cell}{fill}")
            }
        };
        let mut line = |cells: Vec<String>| {
            let text = if markdown {
                format!("| {} |", cells.join(" | "))
            } else {
                cells.join("  ")
            };
            out.push_str(indent);
            out.push_str(text.trim_end());
            out.push('\n');
        };

        let header = self.columns.iter().enumerate();
        line(header.map(|(i, (name, _))| pad(name, i)).collect());
        let rule = self.columns.iter().enumerate().map(|(i, (_, right))| {
            let dashes = "-".repeat(widths[i] - 1);
            match (markdown, right) {
                (true, true) => format!("{dashes}:"),
                (true, false) => format!(":{dashes}"),
                (false, _) => format!("{dashes}-"),
            }
        });
        line(rule.collect());
        for row in &self.rows {
            line(row.iter().enumerate().map(|(i, c)| pad(c, i)).collect());
        }
    }
}

fn format_time(ns: f64) -> String {
    if ns >= 1e10 {
        format!("{:.3} s", ns / 1e9)
    } else {
        format!("{:.2} ms", ns / 1e6)
    }
}

fn describe_environment(env: &Environment) -> String {
    format!(
        "{} ({}, {} logical cores, {})",
        env.commit.as_deref().unwrap_or("unknown commit"),
        env.cpu.as_deref().unwrap_or("unknown CPU"),
        env.logical_cores,
        env.os
    )
}

fn notes(case: &CaseComparison) -> String {
    let mut notes = Vec::new();
    if case.vk_differs() {
        notes.push("VK MISMATCH".to_owned());
    }
    if case.k.0 != case.k.1 {
        notes.push(format!("k {} -> {}", case.k.0, case.k.1));
    }
    if case.proof_bytes.0 != case.proof_bytes.1 {
        notes.push(format!(
            "proof {} -> {} B",
            case.proof_bytes.0, case.proof_bytes.1
        ));
    }
    notes.join(", ")
}

fn cases_table(comparison: &Comparison) -> Table {
    let rows = comparison.cases.iter().map(|case| {
        let dash = || "-".to_owned();
        let (base, head, delta, noise) = match &case.timing {
            Some(t) => {
                let noise = match (t.noise_rule, t.noise_percent) {
                    (NoiseRule::Mad, Some(n)) => format!("{n:.2}% (mad)"),
                    (NoiseRule::Range, Some(n)) => format!("{n:.2}% (range)"),
                    _ => "unknown".to_owned(),
                };
                (
                    format_time(t.base_median_ns),
                    format_time(t.head_median_ns),
                    format!("{:+.2}%", t.delta_percent),
                    noise,
                )
            }
            None => (dash(), dash(), dash(), dash()),
        };
        vec![
            case.key.workload.clone(),
            case.key.pcs.to_string(),
            case.key.threads.to_string(),
            case.k.1.to_string(),
            format!("{}/{}", case.samples.0, case.samples.1),
            base,
            head,
            delta,
            noise,
            case.verdict.name().to_owned(),
            notes(case),
        ]
    });
    Table {
        columns: vec![
            ("workload", false),
            ("pcs", false),
            ("threads", true),
            ("k", true),
            ("samples", true),
            ("base median", true),
            ("head median", true),
            ("delta", true),
            ("noise", true),
            ("verdict", false),
            ("notes", false),
        ],
        rows: rows.collect(),
    }
}

fn rule_text(threshold_percent: f64) -> String {
    format!(
        "delta is the head median relative to the base median; negative is faster. A change is \
         `faster` or `slower` only if the size of delta exceeds both the threshold of {threshold_percent}% \
         and the noise. With at least {MIN_SAMPLES_FOR_MAD} samples per side (mad), the noise is \
         2 * sqrt(s_base^2 + s_head^2) with s = 1.4826 * MAD / median. With fewer samples \
         (range), the [min, max] ranges of the two sides must not overlap, and the noise shown \
         is the wider relative range. With a single sample the noise is unknown and the \
         threshold alone decides."
    )
}

/// Renders a comparison as an aligned plain-text table, or as GitHub-flavoured
/// markdown if `markdown` is set.
pub fn render(comparison: &Comparison, markdown: bool) -> String {
    let mut out = String::new();
    let c = comparison;

    if markdown {
        out.push_str("### Benchmark comparison\n\n");
        out.push_str(&format!(
            "- **base**: {}\n- **head**: {}\n\n",
            describe_environment(&c.base_environment),
            describe_environment(&c.head_environment)
        ));
        for warning in &c.warnings {
            out.push_str(&format!("> [!WARNING]\n> {warning}\n\n"));
        }
    } else {
        out.push_str("Benchmark comparison\n");
        out.push_str(&format!(
            "  base: {}\n  head: {}\n\n",
            describe_environment(&c.base_environment),
            describe_environment(&c.head_environment)
        ));
        for warning in &c.warnings {
            out.push_str(&format!("WARNING: {warning}\n"));
        }
        if !c.warnings.is_empty() {
            out.push('\n');
        }
    }

    if c.cases.is_empty() {
        out.push_str("No case is present in both files.\n");
    } else {
        cases_table(c).render(markdown, "", &mut out);
    }
    out.push_str(&format!(
        "\nSummary: {} faster, {} slower, {} within noise",
        c.count(Verdict::Faster),
        c.count(Verdict::Slower),
        c.count(Verdict::WithinNoise)
    ));
    match c.count(Verdict::NoData) {
        0 => out.push_str(".\n"),
        n => out.push_str(&format!(", {n} without data.\n")),
    }

    for (side, keys) in [("base", &c.only_base), ("head", &c.only_head)] {
        if keys.is_empty() {
            continue;
        }
        let title = format!("Only in {side} (not compared)");
        if markdown {
            out.push_str(&format!("\n**{title}**\n\n"));
        } else {
            out.push_str(&format!("\n{title}:\n"));
        }
        for key in keys {
            let bullet = if markdown { "-" } else { "  -" };
            out.push_str(&format!("{bullet} {key}\n"));
        }
    }

    let rule = rule_text(c.threshold_percent);
    if markdown {
        out.push_str(&format!("\n<sub>{rule}</sub>\n"));
    } else {
        out.push_str(&format!("\nRule: {rule}\n"));
    }
    out
}

/// Parses the contents of a result file, rejecting any schema version other
/// than [`SCHEMA_VERSION`].
pub fn parse(json: &str) -> Result<RunResult, String> {
    // The version is read from the untyped document first, so that a file of
    // another version is reported as such and not as a missing field.
    let value: serde_json::Value =
        serde_json::from_str(json).map_err(|e| format!("not valid JSON: {e}"))?;
    match value.get("schema_version").and_then(|v| v.as_u64()) {
        Some(v) if v == u64::from(SCHEMA_VERSION) => {}
        Some(v) => {
            return Err(format!(
                "schema version {v} is not supported, this build reads version \
                 {SCHEMA_VERSION}; produce both files with the same version of the runner"
            ));
        }
        None => return Err("not a result file: no `schema_version` field".to_owned()),
    }
    serde_json::from_value(value).map_err(|e| format!("not a valid result file: {e}"))
}

fn load(path: &str) -> Result<RunResult, String> {
    let json = fs::read_to_string(path).map_err(|e| format!("cannot read {path}: {e}"))?;
    parse(&json).map_err(|e| format!("{path}: {e}"))
}

/// What the command line asks for.
#[derive(Debug, PartialEq)]
enum Command {
    Help,
    Compare {
        base: String,
        head: String,
        threshold_percent: f64,
        markdown: bool,
        fail_on_regression: bool,
    },
}

fn parse_args(args: &[String]) -> Result<Command, String> {
    let mut paths = Vec::new();
    let mut threshold_percent = DEFAULT_THRESHOLD_PERCENT;
    let mut markdown = false;
    let mut fail_on_regression = false;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => return Ok(Command::Help),
            "--markdown" => markdown = true,
            "--fail-on-regression" => fail_on_regression = true,
            "--threshold" => {
                let value = args.next().ok_or("--threshold needs a value")?;
                threshold_percent = match value.parse::<f64>() {
                    Ok(t) if t.is_finite() && t >= 0.0 => t,
                    _ => return Err(format!("invalid threshold `{value}`")),
                };
            }
            option if option.starts_with('-') => {
                return Err(format!("unknown option `{option}`"));
            }
            path => paths.push(path.to_owned()),
        }
    }
    match <[String; 2]>::try_from(paths) {
        Ok([base, head]) => Ok(Command::Compare {
            base,
            head,
            threshold_percent,
            markdown,
            fail_on_regression,
        }),
        Err(_) => Err("expected exactly two result files".to_owned()),
    }
}

/// Runs the `compare` subcommand on the arguments that follow its name:
/// `<base.json> <head.json> [--threshold <percent>] [--markdown]
/// [--fail-on-regression]`.
///
/// Prints the comparison to the standard output and problems to the standard
/// error. Fails with status 2 if the arguments or the files are invalid and,
/// under `--fail-on-regression`, with status 1 if a case is significantly
/// slower.
pub fn run(args: &[String]) -> ExitCode {
    let command = match parse_args(args) {
        Ok(command) => command,
        Err(e) => {
            eprintln!("error: {e}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let Command::Compare {
        base,
        head,
        threshold_percent,
        markdown,
        fail_on_regression,
    } = command
    else {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    };
    let (base, head) = match (load(&base), load(&head)) {
        (Ok(base), Ok(head)) => (base, head),
        (base, head) => {
            for e in [base.err(), head.err()].into_iter().flatten() {
                eprintln!("error: {e}");
            }
            return ExitCode::from(2);
        }
    };

    let comparison = compare_with_threshold(&base, &head, threshold_percent);
    print!("{}", render(&comparison, markdown));
    if fail_on_regression && comparison.has_regression() {
        eprintln!(
            "error: {} case(s) significantly slower",
            comparison.count(Verdict::Slower)
        );
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    const MS: u64 = 1_000_000;

    fn environment() -> Environment {
        Environment {
            commit: Some("0123abcd".to_owned()),
            cpu: Some("Test CPU".to_owned()),
            logical_cores: 16,
            os: "linux x86_64".to_owned(),
        }
    }

    fn case(workload: &str, pcs: Pcs, threads: usize, samples_ms: &[u64]) -> CaseResult {
        CaseResult {
            workload: workload.to_owned(),
            pcs,
            threads,
            k: 13,
            vk_hash: "aa".repeat(32),
            proof_bytes: 4000,
            samples_ns: samples_ms.iter().map(|s| s * MS).collect(),
            verify_ns: vec![],
        }
    }

    fn run_of(cases: Vec<CaseResult>) -> RunResult {
        RunResult {
            schema_version: SCHEMA_VERSION,
            environment: environment(),
            cases,
        }
    }

    const STEADY: [u64; 7] = [1000, 1004, 998, 1001, 1003, 999, 1002];

    fn single(base: &[u64], head: &[u64]) -> CaseComparison {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, base)]);
        let head = run_of(vec![case("poseidon", Pcs::Kzg, 8, head)]);
        let comparison = compare(&base, &head);
        assert_eq!(comparison.cases.len(), 1);
        comparison.cases[0].clone()
    }

    #[test]
    fn clear_speedup() {
        let c = single(&STEADY, &[900, 903, 899, 901, 902, 898, 904]);
        assert_eq!(c.verdict, Verdict::Faster);
        let t = c.timing.unwrap();
        assert_eq!(t.base_median_ns, 1001.0 * MS as f64);
        assert_eq!(t.head_median_ns, 901.0 * MS as f64);
        assert!((t.delta_percent + 9.99).abs() < 0.01);
        assert_eq!(t.noise_rule, NoiseRule::Mad);
        assert!(t.noise_percent.unwrap() < 1.0);
    }

    #[test]
    fn clear_slowdown() {
        let c = single(&STEADY, &[1100, 1103, 1099, 1101, 1102, 1098, 1104]);
        assert_eq!(c.verdict, Verdict::Slower);
        assert!(c.timing.unwrap().delta_percent > 9.0);
    }

    #[test]
    fn below_threshold_is_within_noise() {
        // 1% slower with tight samples: beyond the noise, below the threshold.
        let c = single(&STEADY, &[1010, 1014, 1008, 1011, 1013, 1009, 1012]);
        assert_eq!(c.verdict, Verdict::WithinNoise);
        let t = c.timing.unwrap();
        assert!(t.delta_percent.abs() > t.noise_percent.unwrap());
    }

    #[test]
    fn below_noise_is_within_noise() {
        // 5% slower, but each side scatters by far more than that.
        let base = [1000, 1100, 900, 1050, 950, 1150, 850];
        let head = [1050, 1150, 950, 1100, 1000, 1200, 900];
        let c = single(&base, &head);
        assert_eq!(c.verdict, Verdict::WithinNoise);
        let t = c.timing.unwrap();
        assert!(t.delta_percent > DEFAULT_THRESHOLD_PERCENT);
        assert!(t.noise_percent.unwrap() > t.delta_percent);
    }

    #[test]
    fn threshold_is_configurable() {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let head = run_of(vec![case(
            "poseidon",
            Pcs::Kzg,
            8,
            &[1010, 1014, 1008, 1011, 1013, 1009, 1012],
        )]);
        let comparison = compare_with_threshold(&base, &head, 0.5);
        assert_eq!(comparison.cases[0].verdict, Verdict::Slower);
        assert!(comparison.has_regression());
    }

    #[test]
    fn few_samples_use_ranges() {
        let disjoint = single(&[1000, 1010, 990], &[900, 910, 890]);
        assert_eq!(disjoint.verdict, Verdict::Faster);
        assert_eq!(disjoint.timing.unwrap().noise_rule, NoiseRule::Range);

        let overlapping = single(&[1000, 1010, 920], &[950, 960, 890]);
        assert_eq!(overlapping.verdict, Verdict::WithinNoise);
        assert!(overlapping.timing.unwrap().delta_percent < -2.0);
    }

    #[test]
    fn single_sample_is_flagged() {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, &[1000])]);
        let head = run_of(vec![case("poseidon", Pcs::Kzg, 8, &[900])]);
        let comparison = compare(&base, &head);
        assert_eq!(comparison.cases[0].verdict, Verdict::Faster);
        let timing = comparison.cases[0].timing.as_ref().unwrap();
        assert_eq!(timing.noise_rule, NoiseRule::Unknown);
        assert!(comparison.warnings.iter().any(|w| w.contains("SINGLE SAMPLE")));
        assert!(render(&comparison, false).contains("unknown"));
    }

    #[test]
    fn empty_samples_have_no_verdict() {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, &[])]);
        let head = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let comparison = compare(&base, &head);
        assert_eq!(comparison.cases[0].verdict, Verdict::NoData);
        assert!(comparison.cases[0].timing.is_none());
        assert!(comparison.warnings.iter().any(|w| w.contains("NO DATA")));
        assert!(render(&comparison, false).contains("1 without data"));
    }

    #[test]
    fn unmatched_cases_are_listed() {
        let base = run_of(vec![
            case("poseidon", Pcs::Kzg, 8, &STEADY),
            case("poseidon", Pcs::Kzg, 1, &STEADY),
            case("ecdsa", Pcs::Kzg, 8, &STEADY),
        ]);
        let head = run_of(vec![
            case("poseidon", Pcs::Kzg, 8, &STEADY),
            case("poseidon", Pcs::FflonkT4, 8, &STEADY),
        ]);
        let comparison = compare(&base, &head);
        assert_eq!(comparison.cases.len(), 1);
        assert_eq!(comparison.only_base.len(), 2);
        assert_eq!(comparison.only_head.len(), 1);
        assert_eq!(comparison.only_head[0].pcs, Pcs::FflonkT4);

        for markdown in [false, true] {
            let text = render(&comparison, markdown);
            assert!(text.contains("Only in base (not compared)"));
            assert!(text.contains("poseidon / kzg / 1 thread\n"));
            assert!(text.contains("ecdsa / kzg / 8 threads"));
            assert!(text.contains("Only in head (not compared)"));
            assert!(text.contains("poseidon / fflonk-t4 / 8 threads"));
        }
    }

    #[test]
    fn duplicate_cases_are_reported() {
        let base = run_of(vec![
            case("poseidon", Pcs::Kzg, 8, &STEADY),
            case("poseidon", Pcs::Kzg, 8, &[1, 2, 3]),
        ]);
        let head = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let comparison = compare(&base, &head);
        assert_eq!(comparison.cases.len(), 1);
        assert_eq!(comparison.cases[0].samples, (7, 7));
        assert!(comparison.warnings.iter().any(|w| w.contains("more than once in the base")));
    }

    #[test]
    fn vk_hash_mismatch_is_flagged() {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let mut head = base.clone();
        head.cases[0].vk_hash = "bb".repeat(32);
        let comparison = compare(&base, &head);
        assert!(comparison.cases[0].vk_differs());
        assert!(comparison.warnings.iter().any(|w| {
            w.contains("VK HASH MISMATCH for poseidon / kzg / 8 threads")
                && w.contains("aaaaaaaaaaaa")
                && w.contains("bbbbbbbbbbbb")
        }));
        let plain = render(&comparison, false);
        assert!(plain.contains("WARNING: VK HASH MISMATCH"));
        assert!(plain.contains("VK MISMATCH"));
        assert!(render(&comparison, true).contains("> [!WARNING]\n> VK HASH MISMATCH"));

        assert!(compare(&base, &base).warnings.is_empty());
    }

    #[test]
    fn k_and_proof_size_changes_show_both_values() {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let mut head = base.clone();
        head.cases[0].k = 14;
        head.cases[0].proof_bytes = 4200;
        let comparison = compare(&base, &head);
        let warnings = comparison.warnings.join("\n");
        assert!(warnings.contains("DIFFERENT K for poseidon / kzg / 8 threads: base 13, head 14"));
        assert!(warnings.contains("base 4000 bytes, head 4200 bytes"));
        let plain = render(&comparison, false);
        assert!(plain.contains("k 13 -> 14, proof 4000 -> 4200 B"));
    }

    #[test]
    fn machine_differences_are_flagged() {
        let base = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let mut head = base.clone();
        head.environment.cpu = Some("Other CPU".to_owned());
        head.environment.logical_cores = 8;
        let warnings = compare(&base, &head).warnings.join("\n");
        assert!(warnings.contains("DIFFERENT CPU: base ran on `Test CPU`, head on `Other CPU`"));
        assert!(warnings.contains("DIFFERENT CORE COUNT: base ran with 16 logical cores"));
    }

    #[test]
    fn schema_mismatch_is_rejected() {
        let run = run_of(vec![case("poseidon", Pcs::Kzg, 8, &STEADY)]);
        let json = serde_json::to_string(&run).unwrap();
        assert_eq!(parse(&json), Ok(run.clone()));

        let mut other = run;
        other.schema_version = SCHEMA_VERSION + 1;
        let error = parse(&serde_json::to_string(&other).unwrap()).unwrap_err();
        assert!(error.contains(&format!("schema version {}", SCHEMA_VERSION + 1)));
        assert!(error.contains("not supported"));

        // A file of another version is reported as such even if its shape
        // has changed.
        let error = parse(r#"{"schema_version": 99, "runs": []}"#).unwrap_err();
        assert!(error.contains("schema version 99"));
        assert!(parse(r#"{"cases": []}"#).unwrap_err().contains("schema_version"));
        assert!(parse("not json").unwrap_err().contains("not valid JSON"));
        let error = parse(&format!(r#"{{"schema_version": {SCHEMA_VERSION}}}"#)).unwrap_err();
        assert!(error.contains("not a valid result file"));
    }

    fn mixed() -> Comparison {
        let base = run_of(vec![
            case("poseidon", Pcs::Kzg, 8, &STEADY),
            case("ecdsa", Pcs::Kzg, 8, &STEADY),
            case("zswap_output", Pcs::FflonkT4, 1, &STEADY),
        ]);
        let head = run_of(vec![
            case(
                "poseidon",
                Pcs::Kzg,
                8,
                &[900, 903, 899, 901, 902, 898, 904],
            ),
            case(
                "ecdsa",
                Pcs::Kzg,
                8,
                &[1100, 1103, 1099, 1101, 1102, 1098, 1104],
            ),
            case("zswap_output", Pcs::FflonkT4, 1, &STEADY),
        ]);
        compare(&base, &head)
    }

    #[test]
    fn renders_plain_text() {
        let text = render(&mixed(), false);
        assert!(text.starts_with("Benchmark comparison\n  base: 0123abcd (Test CPU, 16 logical"));
        assert!(text.contains("workload      pcs        threads    k  samples  base median"));
        assert!(text.contains("-9.99%  0.89% (mad)  faster"));
        assert!(text.contains("+9.99%  0.80% (mad)  slower"));
        assert!(text.contains("+0.00%  0.84% (mad)  within noise"));
        assert!(text.contains("1001.00 ms"));
        assert!(text.contains("Summary: 1 faster, 1 slower, 1 within noise.\n"));
        assert!(text.contains("Rule: delta is the head median relative to the base median"));
        assert!(text.contains("threshold of 2%"));
        assert!(!text.contains('|'));
        assert!(!text.contains("WARNING"));
        // No line carries trailing whitespace.
        assert!(text.lines().all(|l| l == l.trim_end()));
    }

    #[test]
    fn renders_markdown() {
        let text = render(&mixed(), true);
        assert!(text.starts_with("### Benchmark comparison\n\n- **base**: 0123abcd"));
        assert!(text.contains("| workload     | pcs       | threads |   k | samples |"));
        assert!(text.contains("| :----------- | :-------- | ------: | --: |"));
        assert!(text.contains("| -9.99% | 0.89% (mad) | faster       |"));
        assert!(text.contains("| +9.99% | 0.80% (mad) | slower       |"));
        assert!(text.contains("| within noise |"));
        assert!(text.contains("Summary: 1 faster, 1 slower, 1 within noise."));
        assert!(text.contains("<sub>delta is the head median"));
    }

    #[test]
    fn long_proofs_are_shown_in_seconds() {
        assert_eq!(format_time(12_345.0 * MS as f64), "12.345 s");
        assert_eq!(format_time(412.345 * MS as f64), "412.35 ms");
    }

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|a| (*a).to_owned()).collect()
    }

    #[test]
    fn parses_arguments() {
        let parsed = parse_args(&strings(&[
            "b.json",
            "--threshold",
            "3.5",
            "h.json",
            "--markdown",
            "--fail-on-regression",
        ]));
        let expected = Command::Compare {
            base: "b.json".to_owned(),
            head: "h.json".to_owned(),
            threshold_percent: 3.5,
            markdown: true,
            fail_on_regression: true,
        };
        assert_eq!(parsed, Ok(expected));
        assert_eq!(parse_args(&strings(&["--help"])), Ok(Command::Help));

        assert!(parse_args(&strings(&["b.json"])).is_err());
        assert!(parse_args(&strings(&["a", "b", "c"])).is_err());
        assert!(parse_args(&strings(&["a", "b", "--threshold"])).is_err());
        assert!(parse_args(&strings(&["a", "b", "--threshold", "-1"])).is_err());
        assert!(parse_args(&strings(&["a", "b", "--threshold", "x"])).is_err());
        assert!(parse_args(&strings(&["a", "b", "--verbose"])).is_err());
    }

    #[test]
    fn missing_files_are_reported() {
        let error = load("/nonexistent/base.json").unwrap_err();
        assert!(error.contains("cannot read /nonexistent/base.json"));
    }
}
