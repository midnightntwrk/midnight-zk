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

//! Command-line entry point of the benchmark runner.

use std::{
    fs,
    path::PathBuf,
    process::ExitCode,
    time::{SystemTime, UNIX_EPOCH},
};

use clap::{Args, Parser, Subcommand};
use midnight_benchmarks::{
    compare, report,
    runner::{self, Config},
    workload::Pcs,
    workloads,
};

/// Standard prover benchmarks for midnight-zk.
#[derive(Parser)]
#[command(name = "midnight-benchmarks", args_conflicts_with_subcommands = true)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
    #[command(flatten)]
    run: RunArgs,
}

#[derive(Subcommand)]
enum Command {
    /// Lists the workloads and the schemes each supports.
    List,
    /// Times the prover of the selected workloads. This is the default
    /// command.
    Run(RunArgs),
    /// Compares two result files written with `run --json`.
    Compare {
        /// The baseline and the candidate result files.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
}

#[derive(Args)]
struct RunArgs {
    /// Only run workloads whose name contains one of these substrings.
    #[arg(long, value_delimiter = ',', value_name = "SUBSTR")]
    filter: Vec<String>,
    /// The schemes to prove under: `kzg`, `fflonk`. Defaults to all those
    /// each workload supports.
    #[arg(long, value_delimiter = ',', value_parser = parse_pcs)]
    pcs: Option<Vec<Pcs>>,
    /// The sizes of the thread pools to prove in: positive integers or `max`
    /// for the number of logical cores.
    #[arg(long, value_delimiter = ',', value_parser = parse_threads, default_value = "1,max")]
    threads: Vec<usize>,
    /// The number of timed proofs per case.
    #[arg(long, value_name = "N", default_value_t = 5, value_parser = clap::value_parser!(u32).range(1..))]
    samples: u32,
    /// The number of untimed proofs before the timed ones.
    #[arg(long, value_name = "N", default_value_t = 1)]
    warmup: u32,
    /// Writes the results to this file as JSON.
    #[arg(long, value_name = "PATH")]
    json: Option<PathBuf>,
    /// Writes the reference tables to this file as markdown.
    #[arg(long, value_name = "PATH")]
    markdown: Option<PathBuf>,
    /// Skips verifying the last proof of each case.
    #[arg(long)]
    no_verify: bool,
}

fn parse_pcs(s: &str) -> Result<Pcs, String> {
    let known = || Pcs::ALL.map(Pcs::name).join(", ");
    (Pcs::ALL.into_iter().find(|pcs| pcs.name() == s))
        .ok_or_else(|| format!("unknown scheme, expected one of: {}", known()))
}

fn parse_threads(s: &str) -> Result<usize, String> {
    if s == "max" {
        return Ok(runner::max_threads());
    }
    match s.parse() {
        Ok(threads) if threads > 0 => Ok(threads),
        _ => Err("expected a positive integer or `max`".into()),
    }
}

fn list() -> ExitCode {
    let registry = workloads::registry();
    if registry.is_empty() {
        println!("no workloads are registered");
    }
    let width = registry.iter().map(|w| w.name().len()).max().unwrap_or(0);
    for workload in registry {
        let pcs: Vec<&str> = workload.supported_pcs().into_iter().map(Pcs::name).collect();
        println!("{:width$}  {}", workload.name(), pcs.join(","));
    }
    ExitCode::SUCCESS
}

fn run(args: RunArgs) -> ExitCode {
    let config = Config {
        filter: args.filter,
        pcs: args.pcs,
        threads: args.threads,
        samples: args.samples as usize,
        warmup: args.warmup as usize,
        verify: !args.no_verify,
    };
    let result = match runner::run(&config, workloads::registry()) {
        Ok(result) => result,
        Err(runner::Error::NothingToRun) => {
            eprintln!("error: no workloads matched; `list` shows the registered ones");
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    println!("{}", report::render_summary(&result));
    print!("{}", report::render_breakdowns(&result));

    let mut outputs = Vec::new();
    if let Some(path) = args.json {
        let json = serde_json::to_string_pretty(&result).expect("results serialize to JSON");
        outputs.push((path, json + "\n"));
    }
    if let Some(path) = args.markdown {
        let now = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs());
        let markdown = report::render_markdown(&result, &report::utc_date(now));
        outputs.push((path, markdown));
    }
    let mut code = ExitCode::SUCCESS;
    for (path, contents) in outputs {
        match fs::write(&path, contents) {
            Ok(()) => eprintln!("wrote {}", path.display()),
            Err(e) => {
                eprintln!("error: cannot write {}: {e}", path.display());
                code = ExitCode::FAILURE;
            }
        }
    }
    code
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        None => run(cli.run),
        Some(Command::Run(args)) => run(args),
        Some(Command::List) => list(),
        Some(Command::Compare { args }) => compare::run(&args),
    }
}

#[cfg(test)]
mod tests {
    use clap::CommandFactory;

    use super::*;

    fn parse(args: &[&str]) -> Result<Cli, clap::Error> {
        Cli::try_parse_from([&["midnight-benchmarks"], args].concat())
    }

    #[test]
    fn cli_is_well_formed() {
        Cli::command().debug_assert();
    }

    #[test]
    fn run_is_the_default_command() {
        let cli = parse(&[]).unwrap();
        assert!(cli.command.is_none());
        assert_eq!(cli.run.threads, [1, runner::max_threads()]);
        assert_eq!((cli.run.samples, cli.run.warmup), (5, 1));
        assert!(cli.run.pcs.is_none() && cli.run.filter.is_empty() && !cli.run.no_verify);

        let cli = parse(&["--samples", "3", "--no-verify"]).unwrap();
        assert!(cli.command.is_none());
        assert_eq!(cli.run.samples, 3);
        assert!(cli.run.no_verify);
    }

    #[test]
    fn run_flags() {
        let args = [
            "run",
            "--filter",
            "poseidon,sha",
            "--pcs",
            "fflonk,kzg",
            "--threads",
            "4,max,1",
            "--warmup",
            "0",
            "--json",
            "out.json",
            "--markdown",
            "out.md",
        ];
        let Some(Command::Run(run)) = parse(&args).unwrap().command else {
            panic!("expected the run command");
        };
        assert_eq!(run.filter, ["poseidon", "sha"]);
        assert_eq!(run.pcs, Some(vec![Pcs::Fflonk, Pcs::Kzg]));
        assert_eq!(run.threads, [4, runner::max_threads(), 1]);
        assert_eq!(run.warmup, 0);
        assert_eq!(run.json, Some("out.json".into()));
        assert_eq!(run.markdown, Some("out.md".into()));
    }

    #[test]
    fn invalid_flags_are_rejected() {
        for args in [
            &["--threads", "0"][..],
            &["--threads", "many"],
            &["--pcs", "ipa"],
            &["--samples", "0"],
            &["list", "--samples", "2"],
        ] {
            assert!(parse(args).is_err(), "{args:?}");
        }
    }

    #[test]
    fn compare_forwards_its_arguments() {
        let Some(Command::Compare { args }) =
            parse(&["compare", "a.json", "b.json", "--threshold", "5"]).unwrap().command
        else {
            panic!("expected the compare command");
        };
        assert_eq!(args, ["a.json", "b.json", "--threshold", "5"]);
    }
}
