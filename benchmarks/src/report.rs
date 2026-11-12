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

//! Renders results as terminal tables and markdown.

use std::fmt::Write;

use crate::{
    results::{Breakdown, CaseResult, RunResult},
    stats::Stats,
};

/// The warning attached to results of builds with profiling.
const PROFILING_WARNING: &str =
    "built with the `profiling` feature: these timings are not reference numbers";

/// The caveat on reading the kernel columns of a breakdown.
const OVERLAP_NOTE: &str = "Kernel columns are wall times and kernels can run concurrently, so \
                            they may add up to more than the phase total minus `other`.";

/// A table of text cells.
struct Table {
    /// The column titles, each with whether the column is right-aligned.
    columns: Vec<(String, bool)>,
    rows: Vec<Vec<String>>,
}

impl Table {
    fn new(columns: &[(&str, bool)]) -> Self {
        Table {
            columns: columns.iter().map(|(title, right)| (title.to_string(), *right)).collect(),
            rows: Vec::new(),
        }
    }

    fn widths(&self) -> Vec<usize> {
        let width = |s: &String| s.chars().count();
        (self.columns.iter().enumerate())
            .map(|(i, (title, _))| {
                let cells = self.rows.iter().map(|row| width(&row[i]));
                cells.chain([width(title)]).max().unwrap_or(0)
            })
            .collect()
    }

    fn pad(&self, column: usize, cell: &str, width: usize) -> String {
        if self.columns[column].1 {
            format!("{cell:>width$}")
        } else {
            format!("{cell:<width$}")
        }
    }

    fn line<'a>(
        &self,
        cells: impl Iterator<Item = &'a String>,
        widths: &[usize],
        (start, sep, end): (&str, &str, &str),
    ) -> String {
        let cells: Vec<String> =
            cells.enumerate().map(|(i, cell)| self.pad(i, cell, widths[i])).collect();
        format!("{start}{}{end}", cells.join(sep)).trim_end().to_owned() + "\n"
    }

    /// Columns separated by two spaces, with a rule under the titles.
    fn render_text(&self) -> String {
        let widths = self.widths();
        let borders = ("", "  ", "");
        let rule: Vec<String> = widths.iter().map(|w| "-".repeat(*w)).collect();
        let mut out = self.line(self.columns.iter().map(|(t, _)| t), &widths, borders);
        out += &self.line(rule.iter(), &widths, borders);
        for row in &self.rows {
            out += &self.line(row.iter(), &widths, borders);
        }
        out
    }

    /// A GitHub-flavoured markdown table, padded to read well as plain text.
    fn render_markdown(&self) -> String {
        // The alignment row needs three characters per column.
        let widths: Vec<usize> = self.widths().into_iter().map(|w| w.max(3)).collect();
        let borders = ("| ", " | ", " |");
        let rule: Vec<String> = (self.columns.iter().zip(&widths))
            .map(|((_, right), w)| {
                if *right {
                    "-".repeat(w - 1) + ":"
                } else {
                    "-".repeat(*w)
                }
            })
            .collect();
        let mut out = self.line(self.columns.iter().map(|(t, _)| t), &widths, borders);
        out += &self.line(rule.iter(), &widths, borders);
        for row in &self.rows {
            out += &self.line(row.iter(), &widths, borders);
        }
        out
    }
}

/// A duration in nanoseconds, in the largest unit that keeps it above one.
pub fn format_duration(ns: u64) -> String {
    let ns = ns as f64;
    if ns >= 1e9 {
        format!("{:.3} s", ns / 1e9)
    } else if ns >= 1e6 {
        format!("{:.2} ms", ns / 1e6)
    } else {
        format!("{:.1} µs", ns / 1e3)
    }
}

fn threads_label(threads: usize) -> String {
    format!("{threads} thread{}", if threads == 1 { "" } else { "s" })
}

/// The summary table of `cases`, with a column for the thread count unless
/// all cases share it.
fn summary_table<'a>(cases: impl Iterator<Item = &'a CaseResult>, with_threads: bool) -> Table {
    let mut columns = vec![("workload", false), ("pcs", false), ("k", true)];
    if with_threads {
        columns.push(("threads", true));
    }
    columns.extend([
        ("median", true),
        ("min", true),
        ("±MAD%", true),
        ("proof bytes", true),
    ]);
    let mut table = Table::new(&columns);
    for case in cases {
        let mut row = vec![
            case.workload.clone(),
            case.scheme.clone(),
            case.k.to_string(),
        ];
        if with_threads {
            row.push(case.threads.to_string());
        }
        match Stats::of(&case.samples_ns) {
            Some(stats) => row.extend([
                format_duration(stats.median),
                format_duration(stats.min),
                format!("{:.1}", stats.mad_percent()),
            ]),
            None => row.extend(["-".to_owned(), "-".to_owned(), "-".to_owned()]),
        }
        row.push(case.proof_bytes.to_string());
        table.rows.push(row);
    }
    table
}

/// The names of the kernels of `breakdown`, in order of first appearance.
fn kernel_names(breakdown: &Breakdown) -> Vec<&str> {
    let mut names = Vec::new();
    for kernel in breakdown.phases.iter().flat_map(|p| &p.kernels) {
        if !names.contains(&kernel.kernel.as_str()) {
            names.push(kernel.kernel.as_str());
        }
    }
    names
}

/// The table of a breakdown: a row per phase and a column per kernel, each
/// cell with its share of the wall time of the proof.
fn breakdown_table(breakdown: &Breakdown) -> Table {
    let kernels = kernel_names(breakdown);
    let cell = |ns: u64| {
        let percent = match breakdown.total_ns {
            0 => 0.0,
            total => 100.0 * ns as f64 / total as f64,
        };
        format!("{:.2} ms ({percent:.1}%)", ns as f64 / 1e6)
    };

    let mut columns = vec![("phase", false)];
    columns.extend(kernels.iter().map(|name| (*name, true)));
    columns.extend([("other", true), ("phase total", true)]);
    let mut table = Table::new(&columns);

    let mut kernel_totals = vec![0u64; kernels.len()];
    let mut covered_total = 0u64;
    for phase in &breakdown.phases {
        let mut row = vec![phase.phase.clone()];
        for (name, total) in kernels.iter().zip(&mut kernel_totals) {
            let wall: u64 =
                phase.kernels.iter().filter(|k| k.kernel == *name).map(|k| k.wall_ns).sum();
            *total += wall;
            row.push(cell(wall));
        }
        covered_total += phase.covered_ns;
        row.push(cell(phase.wall_ns.saturating_sub(phase.covered_ns)));
        row.push(cell(phase.wall_ns));
        table.rows.push(row);
    }

    let mut row = vec!["total".to_owned()];
    row.extend(kernel_totals.into_iter().map(cell));
    row.push(cell(breakdown.total_ns.saturating_sub(covered_total)));
    row.push(cell(breakdown.total_ns));
    table.rows.push(row);
    table
}

/// For each kernel that ran, the ratio of the time summed over its calls to
/// its wall time, which tells how many threads it kept busy.
fn parallelism_hint(breakdown: &Breakdown) -> Option<String> {
    let hints: Vec<String> = kernel_names(breakdown)
        .into_iter()
        .filter_map(|name| {
            let calls = || breakdown.phases.iter().flat_map(|p| &p.kernels);
            let calls = || calls().filter(|k| k.kernel == name);
            let wall: u64 = calls().map(|k| k.wall_ns).sum();
            let busy: u64 = calls().map(|k| k.busy_ns).sum();
            (wall > 0).then(|| format!("{name} {:.1}x", busy as f64 / wall as f64))
        })
        .collect();
    (!hints.is_empty()).then(|| format!("Parallelism (busy/wall): {}.", hints.join(", ")))
}

fn case_title(case: &CaseResult) -> String {
    format!(
        "{}, {}, k={}, {}",
        case.workload,
        case.scheme,
        case.k,
        threads_label(case.threads)
    )
}

/// The summary of `result` for a terminal: a row per case with the median
/// and spread of its samples.
pub fn render_summary(result: &RunResult) -> String {
    let mut out = String::new();
    if result.environment.profiling {
        writeln!(out, "warning: {PROFILING_WARNING}\n").unwrap();
    }
    out += &summary_table(result.cases.iter(), true).render_text();
    out
}

/// The breakdowns of the cases of `result` that have one, for a terminal. It
/// is empty if no case does.
pub fn render_breakdowns(result: &RunResult) -> String {
    let mut out = String::new();
    for case in &result.cases {
        let Some(breakdown) = &case.breakdown else {
            continue;
        };
        if !out.is_empty() {
            out.push('\n');
        }
        writeln!(out, "{}", case_title(case)).unwrap();
        out += &breakdown_table(breakdown).render_text();
        if let Some(hint) = parallelism_hint(breakdown) {
            writeln!(out, "{hint}").unwrap();
        }
    }
    if !out.is_empty() {
        writeln!(out, "\n{OVERLAP_NOTE}").unwrap();
    }
    out
}

/// The reference tables of `result` in markdown: the environment, a summary
/// table per thread count and the breakdowns, if any. `date` is the day of
/// the run.
pub fn render_markdown(result: &RunResult, date: &str) -> String {
    let env = &result.environment;
    let mut out = String::from("# Prover benchmarks\n\n");
    let unknown = || "unknown".to_owned();
    let commit = env.commit.as_ref().map_or_else(unknown, |c| format!("`{c}`"));
    writeln!(out, "- Commit: {commit}").unwrap();
    writeln!(out, "- CPU: {}", env.cpu.clone().unwrap_or_else(unknown)).unwrap();
    writeln!(out, "- Logical cores: {}", env.logical_cores).unwrap();
    writeln!(out, "- OS: {}", env.os).unwrap();
    writeln!(out, "- Date: {date}").unwrap();
    if env.profiling {
        writeln!(out, "\n**Warning**: {PROFILING_WARNING}.").unwrap();
    }

    let mut thread_counts = Vec::new();
    for case in &result.cases {
        if !thread_counts.contains(&case.threads) {
            thread_counts.push(case.threads);
        }
    }
    for threads in thread_counts {
        writeln!(out, "\n## {}\n", threads_label(threads)).unwrap();
        let cases = result.cases.iter().filter(|c| c.threads == threads);
        out += &summary_table(cases, false).render_markdown();
    }

    let mut breakdowns = result
        .cases
        .iter()
        .filter_map(|case| Some((case, case.breakdown.as_ref()?)))
        .peekable();
    if breakdowns.peek().is_some() {
        writeln!(out, "\n## Breakdown\n").unwrap();
        writeln!(
            out,
            "Time of the last proof of each case by prover phase and kernel, with its share of \
             the wall time of the proof. {OVERLAP_NOTE}"
        )
        .unwrap();
    }
    for (case, breakdown) in breakdowns {
        writeln!(out, "\n### {}\n", case_title(case)).unwrap();
        out += &breakdown_table(breakdown).render_markdown();
        if let Some(hint) = parallelism_hint(breakdown) {
            writeln!(out, "\n{hint}").unwrap();
        }
    }
    out
}

/// The UTC date, as `YYYY-MM-DD`, of a time in seconds since the Unix epoch.
pub fn utc_date(unix_seconds: u64) -> String {
    // The civil-from-days conversion on years starting in March, so that the
    // leap day is the last of the year.
    let days = unix_seconds / 86_400 + 719_468;
    let (era, day_of_era) = (days / 146_097, days % 146_097);
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let shifted_month = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * shifted_month + 2) / 5 + 1;
    let month = if shifted_month < 10 {
        shifted_month + 3
    } else {
        shifted_month - 9
    };
    let year = year_of_era + era * 400 + u64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        results::{Environment, KernelBreakdown, PhaseBreakdown, SCHEMA_VERSION},
        workload::Pcs,
    };

    fn kernel(kernel: &str, wall_ns: u64, busy_ns: u64) -> KernelBreakdown {
        KernelBreakdown {
            kernel: kernel.to_owned(),
            wall_ns,
            busy_ns,
            calls: 1,
        }
    }

    fn breakdown() -> Breakdown {
        Breakdown {
            total_ns: 200_000_000,
            phases: vec![
                PhaseBreakdown {
                    phase: "synthesis".into(),
                    wall_ns: 50_000_000,
                    covered_ns: 0,
                    kernels: vec![
                        kernel("msm", 0, 0),
                        kernel("fft", 0, 0),
                        kernel("poly_eval", 0, 0),
                    ],
                },
                PhaseBreakdown {
                    phase: "quotient".into(),
                    wall_ns: 140_000_000,
                    covered_ns: 120_000_000,
                    kernels: vec![
                        kernel("msm", 40_000_000, 60_000_000),
                        kernel("fft", 60_000_000, 240_000_000),
                        kernel("poly_eval", 30_000_000, 30_000_000),
                    ],
                },
            ],
        }
    }

    fn case(
        workload: &str,
        pcs: Pcs,
        threads: usize,
        samples_ns: &[u64],
        breakdown: Option<Breakdown>,
    ) -> CaseResult {
        CaseResult {
            workload: workload.to_owned(),
            pcs,
            scheme: pcs.to_string(),
            threads,
            k: 14,
            vk_hash: "00".repeat(32),
            proof_bytes: 4_512,
            samples_ns: samples_ns.to_vec(),
            breakdown,
        }
    }

    fn fixture(profiling: bool) -> RunResult {
        let breakdown = || profiling.then(breakdown);
        RunResult {
            schema_version: SCHEMA_VERSION,
            environment: Environment {
                commit: Some("0123456789ab-dirty".into()),
                cpu: Some("Some CPU 9000".into()),
                logical_cores: 32,
                os: "linux x86_64".into(),
                profiling,
            },
            cases: vec![
                case(
                    "poseidon",
                    Pcs::Kzg,
                    1,
                    &[1_500_000_000, 1_600_000_000, 1_400_000_000],
                    breakdown(),
                ),
                case("poseidon", Pcs::Kzg, 32, &[200_000_000, 220_000_000], None),
                case("sha_preimage", Pcs::Fflonk, 1, &[900_000], breakdown()),
            ],
        }
    }

    #[test]
    fn durations() {
        assert_eq!(format_duration(0), "0.0 µs");
        assert_eq!(format_duration(999_949), "999.9 µs");
        assert_eq!(format_duration(1_000_000), "1.00 ms");
        assert_eq!(format_duration(12_345_678), "12.35 ms");
        assert_eq!(format_duration(1_234_567_890), "1.235 s");
    }

    #[test]
    fn dates() {
        assert_eq!(utc_date(0), "1970-01-01");
        assert_eq!(utc_date(86_399), "1970-01-01");
        assert_eq!(utc_date(951_782_400), "2000-02-29");
        assert_eq!(utc_date(951_868_800), "2000-03-01");
        assert_eq!(utc_date(1_700_000_000), "2023-11-14");
        assert_eq!(utc_date(1_735_689_599), "2024-12-31");
    }

    #[test]
    fn summary() {
        let expected = "\
workload      pcs      k  threads     median        min  ±MAD%  proof bytes
------------  ------  --  -------  ---------  ---------  -----  -----------
poseidon      kzg     14        1    1.500 s    1.400 s    6.7         4512
poseidon      kzg     14       32  210.00 ms  200.00 ms    4.8         4512
sha_preimage  fflonk  14        1   900.0 µs   900.0 µs    0.0         4512
";
        assert_eq!(render_summary(&fixture(false)), expected);
        assert_eq!(render_breakdowns(&fixture(false)), "");

        let with_profiling = render_summary(&fixture(true));
        assert!(with_profiling.starts_with("warning: built with the `profiling` feature"));
        assert!(with_profiling.ends_with(expected));
    }

    #[test]
    fn breakdowns() {
        let expected_table = "\
phase                   msm               fft         poly_eval             other         phase total
---------  ----------------  ----------------  ----------------  ----------------  ------------------
synthesis    0.00 ms (0.0%)    0.00 ms (0.0%)    0.00 ms (0.0%)  50.00 ms (25.0%)    50.00 ms (25.0%)
quotient   40.00 ms (20.0%)  60.00 ms (30.0%)  30.00 ms (15.0%)  20.00 ms (10.0%)   140.00 ms (70.0%)
total      40.00 ms (20.0%)  60.00 ms (30.0%)  30.00 ms (15.0%)  80.00 ms (40.0%)  200.00 ms (100.0%)
Parallelism (busy/wall): msm 1.5x, fft 4.0x, poly_eval 1.0x.
";
        let rendered = render_breakdowns(&fixture(true));
        let expected = format!(
            "poseidon, kzg, k=14, 1 thread\n{expected_table}\nsha_preimage, fflonk, k=14, 1 \
             thread\n{expected_table}\n{OVERLAP_NOTE}\n"
        );
        assert_eq!(rendered, expected);
    }

    #[test]
    fn empty_breakdown() {
        let empty = Breakdown {
            total_ns: 0,
            phases: vec![],
        };
        let rendered = breakdown_table(&empty).render_text();
        assert_eq!(rendered.lines().count(), 3);
        assert!(rendered.ends_with("total  0.00 ms (0.0%)  0.00 ms (0.0%)\n"));
        assert_eq!(parallelism_hint(&empty), None);
    }

    #[test]
    fn markdown() {
        let expected = "\
# Prover benchmarks

- Commit: `0123456789ab-dirty`
- CPU: Some CPU 9000
- Logical cores: 32
- OS: linux x86_64
- Date: 2026-01-02

## 1 thread

| workload     | pcs    |   k |   median |      min | ±MAD% | proof bytes |
| ------------ | ------ | --: | -------: | -------: | ----: | ----------: |
| poseidon     | kzg    |  14 |  1.500 s |  1.400 s |   6.7 |        4512 |
| sha_preimage | fflonk |  14 | 900.0 µs | 900.0 µs |   0.0 |        4512 |

## 32 threads

| workload | pcs |   k |    median |       min | ±MAD% | proof bytes |
| -------- | --- | --: | --------: | --------: | ----: | ----------: |
| poseidon | kzg |  14 | 210.00 ms | 200.00 ms |   4.8 |        4512 |
";
        assert_eq!(render_markdown(&fixture(false), "2026-01-02"), expected);
    }

    #[test]
    fn markdown_with_breakdown() {
        let rendered = render_markdown(&fixture(true), "2026-01-02");
        assert!(rendered.contains("\n**Warning**: built with the `profiling` feature"));
        assert!(rendered.contains("\n## Breakdown\n"));
        assert!(rendered.contains("\n### poseidon, kzg, k=14, 1 thread\n"));
        assert!(rendered.contains("\n### sha_preimage, fflonk, k=14, 1 thread\n"));
        assert!(!rendered.contains("### poseidon, kzg, k=14, 32 threads"));
        let rows = [
            "| phase     |              msm |              fft |        poly_eval |            \
             other |        phase total |",
            "| --------- | ---------------: | ---------------: | ---------------: | \
             ---------------: | -----------------: |",
            "| quotient  | 40.00 ms (20.0%) | 60.00 ms (30.0%) | 30.00 ms (15.0%) | 20.00 ms \
             (10.0%) |  140.00 ms (70.0%) |",
            "| total     | 40.00 ms (20.0%) | 60.00 ms (30.0%) | 30.00 ms (15.0%) | 80.00 ms \
             (40.0%) | 200.00 ms (100.0%) |",
        ];
        for row in rows {
            assert!(rendered.contains(row), "missing row: {row}");
        }
        assert!(
            rendered.contains("\nParallelism (busy/wall): msm 1.5x, fft 4.0x, poly_eval 1.0x.")
        );
    }

    #[test]
    fn unknown_environment() {
        let mut result = fixture(false);
        result.environment.commit = None;
        result.environment.cpu = None;
        let rendered = render_markdown(&result, "2026-01-02");
        assert!(rendered.contains("- Commit: unknown\n- CPU: unknown\n"));
    }
}
