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

//! Turns the raw rows into one row per proof and prints the totals.
//!
//! Repetition 0 up to `--warmup` (default 1) is the first run of the proof; it
//! is reported apart (`first_s`) and is not part of median, min and max.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
};

use crate::{Args, BASE_COLUMNS, RAW_HEADER};

const OUT_HEADER: &[&str] = &[
    "program",
    "circuit",
    "key_program",
    "job",
    "k",
    "n",
    "median_s",
    "min_s",
    "max_s",
    "first_s",
    "verify_median_s",
    "key_load_s",
    "proof_bytes",
    "proof_sha256",
    "verified",
    "hooks_device",
    "hits_msm",
    "hits_ntt",
    "hits_coset",
    "hits_quotient",
    "fallbacks",
    "device_peak_bytes",
    "host_hwm_bytes",
    "quiet_gate",
    "load1_before_max",
    "load1_after_max",
    "gpu_driver",
    "ready_s",
];

const HITS: [&str; 5] = [
    "hits_msm",
    "hits_ntt",
    "hits_coset",
    "hits_quotient",
    "fallbacks",
];

fn median(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    let n = v.len();
    if n == 0 {
        f64::NAN
    } else if n % 2 == 1 {
        v[n / 2]
    } else {
        (v[n / 2 - 1] + v[n / 2]) / 2.0
    }
}

/// Nearest-rank percentile.
fn percentile(v: &mut [f64], p: f64) -> f64 {
    v.sort_by(f64::total_cmp);
    if v.is_empty() {
        return f64::NAN;
    }
    let rank = ((p / 100.0) * v.len() as f64).ceil().max(1.0) as usize;
    v[rank - 1]
}

struct Proof {
    meta: [String; 5],
    first: Option<f64>,
    timed: Vec<f64>,
    verify: Vec<f64>,
    key_load: f64,
    bytes: BTreeSet<String>,
    sha: BTreeSet<String>,
    verified: bool,
    device: BTreeSet<String>,
    hits: [u64; 5],
    peaks: [u64; 2],
    gate: BTreeSet<String>,
    load_max: [f64; 2],
    driver: BTreeSet<String>,
    ready: f64,
}

/// Entry point of `compact-bench summarize`.
pub fn run(a: &Args) -> i32 {
    let raw = std::fs::read_to_string(a.req("raw")).expect("read raw TSV");
    let warmup: u32 = a.num("warmup", 1);
    let exclude: BTreeSet<&str> = a.get("exclude").unwrap_or("").split(',').collect();
    // Columns by name from the file's own header, so that files written with
    // another column set still read.
    let header: Vec<&str> = raw.lines().next().unwrap_or("").split('\t').collect();
    if let Some(m) = RAW_HEADER[..BASE_COLUMNS].iter().find(|h| !header.contains(h)) {
        eprintln!("raw file has no column {m}");
        return 2;
    }
    let col = |n: &str| header.iter().position(|h| *h == n).unwrap();
    let rows: Vec<Vec<&str>> = raw
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .filter(|f| f.len() == header.len())
        .filter(|f| !exclude.contains(f[col("program")]))
        .collect();

    let binaries: BTreeSet<&str> = rows.iter().map(|f| f[col("binary_sha256")]).collect();
    let binary = match a.get("binary") {
        Some(b) => b,
        None if binaries.len() == 1 => binaries.first().unwrap(),
        None => {
            eprintln!(
                "raw file holds rows of {} binaries; pick one with --binary",
                binaries.len()
            );
            return 2;
        }
    };
    let rows: Vec<&Vec<&str>> = rows.iter().filter(|f| f[col("binary_sha256")] == binary).collect();
    let Some(first) = rows.first() else {
        eprintln!("no rows");
        return 2;
    };

    let mut order = Vec::new();
    let mut proofs: BTreeMap<String, Proof> = BTreeMap::new();
    for f in &rows {
        let job = f[col("job")].to_string();
        let p = proofs.entry(job.clone()).or_insert_with(|| {
            order.push(job.clone());
            Proof {
                meta: ["program", "circuit", "key_program", "job", "k"]
                    .map(|c| f[col(c)].to_string()),
                first: None,
                timed: vec![],
                verify: vec![],
                key_load: f[col("key_load_s")].parse().unwrap_or(f64::NAN),
                bytes: BTreeSet::new(),
                sha: BTreeSet::new(),
                device: BTreeSet::new(),
                hits: [0; 5],
                peaks: [0; 2],
                gate: BTreeSet::new(),
                load_max: [f64::NAN; 2],
                driver: BTreeSet::new(),
                ready: f64::NAN,
                verified: true,
            }
        });
        let rep: u32 = f[col("rep")].parse().unwrap_or(0);
        let s: f64 = f[col("prove_s")].parse().unwrap_or(f64::NAN);
        if rep < warmup {
            p.first = Some(p.first.map_or(s, |x: f64| x.min(s)));
        } else {
            p.timed.push(s);
            p.verify.push(f[col("verify_s")].parse().unwrap_or(f64::NAN));
        }
        p.bytes.insert(f[col("proof_bytes")].to_string());
        p.sha.insert(f[col("proof_sha256")].to_string());
        p.verified &= f[col("verified")] == "true";
        // Hook columns: absent in files written before they existed. The
        // summary keeps the largest count of any repetition.
        let opt = |n: &str| header.iter().position(|h| *h == n).map(|i| f[i]);
        p.device.insert(opt("hooks_device").unwrap_or("-").to_string());
        for (i, h) in HITS.iter().enumerate() {
            let v = opt(h).and_then(|x| x.parse().ok()).unwrap_or(0);
            p.hits[i] = p.hits[i].max(v);
        }
        for (i, h) in ["device_peak_bytes", "host_hwm_bytes"].iter().enumerate() {
            let v = opt(h).and_then(|x| x.parse().ok()).unwrap_or(0);
            p.peaks[i] = p.peaks[i].max(v);
        }
        for (i, h) in ["load1_before", "load1_after"].iter().enumerate() {
            if let Some(v) = opt(h).and_then(|x| x.parse::<f64>().ok()) {
                p.load_max[i] = if p.load_max[i].is_nan() {
                    v
                } else {
                    p.load_max[i].max(v)
                };
            }
        }
        p.gate.insert(opt("quiet_gate").unwrap_or("-").to_string());
        p.driver.insert(opt("gpu_driver").unwrap_or("-").to_string());
        if let Some(v) = opt("ready_s").and_then(|x| x.parse::<f64>().ok()) {
            p.ready = v;
        }
    }

    let mut out = String::new();
    for c in [
        "backend",
        "proofs_source",
        "binary_sha256",
        "rustc",
        "cpu_model",
        "gpu_model",
        "threads",
    ] {
        writeln!(out, "# {c}: {}", first[col(c)]).unwrap();
    }
    writeln!(
        out,
        "# warmup reps per proof: {warmup} (first_s); n = timed reps"
    )
    .unwrap();
    writeln!(out, "{}", OUT_HEADER.join("\t")).unwrap();

    let mut medians = Vec::new();
    let mut by_k: BTreeMap<u32, Vec<f64>> = BTreeMap::new();
    let (mut verified, mut identical) = (0, 0);
    let mut min_n = usize::MAX;
    for job in &order {
        let p = &proofs[job];
        let mut t = p.timed.clone();
        let med = median(&mut t);
        let (mn, mx) = t.iter().fold((f64::INFINITY, f64::NEG_INFINITY), |(a, b), &x| {
            (a.min(x), b.max(x))
        });
        let mut v = p.verify.clone();
        let one = |s: &BTreeSet<String>| {
            if s.len() == 1 {
                s.first().unwrap().clone()
            } else {
                format!("varies({})", s.len())
            }
        };
        let fields = [
            p.meta[0].clone(),
            p.meta[1].clone(),
            p.meta[2].clone(),
            p.meta[3].clone(),
            p.meta[4].clone(),
            t.len().to_string(),
            format!("{med:.4}"),
            format!("{mn:.4}"),
            format!("{mx:.4}"),
            p.first.map_or("-".into(), |x| format!("{x:.4}")),
            format!("{:.4}", median(&mut v)),
            format!("{:.4}", p.key_load),
            one(&p.bytes),
            one(&p.sha),
            p.verified.to_string(),
            p.device.iter().cloned().collect::<Vec<_>>().join(","),
            p.hits[0].to_string(),
            p.hits[1].to_string(),
            p.hits[2].to_string(),
            p.hits[3].to_string(),
            p.hits[4].to_string(),
            p.peaks[0].to_string(),
            p.peaks[1].to_string(),
            p.gate.iter().cloned().collect::<Vec<_>>().join(","),
            format!("{:.2}", p.load_max[0]),
            format!("{:.2}", p.load_max[1]),
            p.driver.iter().cloned().collect::<Vec<_>>().join(","),
            format!("{:.3}", p.ready),
        ];
        writeln!(out, "{}", fields.join("\t")).unwrap();
        medians.push(med);
        by_k.entry(p.meta[4].parse().unwrap_or(0)).or_default().push(med);
        verified += usize::from(p.verified);
        identical += usize::from(p.sha.len() == 1);
        min_n = min_n.min(t.len());
    }
    std::fs::write(a.req("out"), out).expect("write summary");

    let total: f64 = medians.iter().sum();
    println!(
        "proofs {} verified {} byte-identical-across-reps {}",
        order.len(),
        verified,
        identical
    );
    let need_n: usize = a.num("min-n", 5);
    println!("timed reps per proof: at least {min_n} (required {need_n})");
    println!("k\tproofs\tmedian_of_medians_s\tsum_s");
    for (k, v) in &mut by_k {
        let s: f64 = v.iter().sum();
        println!("{k}\t{}\t{:.4}\t{:.3}", v.len(), median(v), s);
    }
    println!("total (sum of per-proof medians) {total:.3} s");
    println!(
        "median {:.4} s, p95 {:.4} s",
        median(&mut medians.clone()),
        percentile(&mut medians, 95.0)
    );
    if min_n < need_n {
        eprintln!("a proof has {min_n} timed repetitions, fewer than {need_n}");
        return 4;
    }
    0
}
