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
    results::{CaseResult, RunResult},
    stats::Stats,
};

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
        ("verify", true),
        ("proof bytes", true),
    ]);
    let mut table = Table::new(&columns);
    for case in cases {
        let mut row = vec![
            case.workload.clone(),
            case.pcs.to_string(),
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
        row.push(match Stats::of(&case.verify_ns) {
            Some(stats) => format_duration(stats.median),
            None => "-".to_owned(),
        });
        row.push(case.proof_bytes.to_string());
        table.rows.push(row);
    }
    table
}

/// The summary of `result` for a terminal: a row per case with the median
/// and spread of its samples.
pub fn render_summary(result: &RunResult) -> String {
    summary_table(result.cases.iter(), true).render_text()
}

/// The reference tables of `result` in markdown: the environment, a summary
/// table per thread count. `date` is the day of the run.
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
        results::{Environment, SCHEMA_VERSION},
        workload::Pcs,
    };

    fn case(workload: &str, pcs: Pcs, threads: usize, samples_ns: &[u64]) -> CaseResult {
        CaseResult {
            workload: workload.to_owned(),
            pcs,
            threads,
            k: 14,
            vk_hash: "00".repeat(32),
            proof_bytes: 4_512,
            samples_ns: samples_ns.to_vec(),
            verify_ns: vec![2_000_000, 4_000_000, 3_000_000],
        }
    }

    fn fixture() -> RunResult {
        RunResult {
            schema_version: SCHEMA_VERSION,
            environment: Environment {
                commit: Some("0123456789ab-dirty".into()),
                cpu: Some("Some CPU 9000".into()),
                logical_cores: 32,
                os: "linux x86_64".into(),
            },
            cases: vec![
                case(
                    "poseidon",
                    Pcs::Kzg,
                    1,
                    &[1_500_000_000, 1_600_000_000, 1_400_000_000],
                ),
                case("poseidon", Pcs::Kzg, 32, &[200_000_000, 220_000_000]),
                case("sha_preimage", Pcs::FflonkT4, 1, &[900_000]),
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
workload      pcs         k  threads     median        min  ±MAD%   verify  proof bytes
------------  ---------  --  -------  ---------  ---------  -----  -------  -----------
poseidon      kzg        14        1    1.500 s    1.400 s    6.7  3.00 ms         4512
poseidon      kzg        14       32  210.00 ms  200.00 ms    4.8  3.00 ms         4512
sha_preimage  fflonk-t4  14        1   900.0 µs   900.0 µs    0.0  3.00 ms         4512
";
        assert_eq!(render_summary(&fixture()), expected);
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

| workload     | pcs       |   k |   median |      min | ±MAD% |  verify | proof bytes |
| ------------ | --------- | --: | -------: | -------: | ----: | ------: | ----------: |
| poseidon     | kzg       |  14 |  1.500 s |  1.400 s |   6.7 | 3.00 ms |        4512 |
| sha_preimage | fflonk-t4 |  14 | 900.0 µs | 900.0 µs |   0.0 | 3.00 ms |        4512 |

## 32 threads

| workload | pcs |   k |    median |       min | ±MAD% |  verify | proof bytes |
| -------- | --- | --: | --------: | --------: | ----: | ------: | ----------: |
| poseidon | kzg |  14 | 210.00 ms | 200.00 ms |   4.8 | 3.00 ms |        4512 |
";
        assert_eq!(render_markdown(&fixture(), "2026-01-02"), expected);
    }

    #[test]
    fn unknown_environment() {
        let mut result = fixture();
        result.environment.commit = None;
        result.environment.cpu = None;
        let rendered = render_markdown(&result, "2026-01-02");
        assert!(rendered.contains("- Commit: unknown\n- CPU: unknown\n"));
    }
}
