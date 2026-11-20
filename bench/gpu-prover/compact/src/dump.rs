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

//! Proof and statement files, and `compact-bench verify`.
//!
//! For job `J` and repetition `R`, `DIR/<J with / as __>.R.proof` holds the
//! proof bytes and `.R.pis` the line `k=<k>` followed by one public input per
//! line (hex of the serialized field element).

use std::{
    io::Write,
    path::{Path, PathBuf},
};

use midnight_serialize::{Serializable, tagged_deserialize};
use midnight_transient_crypto::{
    curve::Fr,
    proofs::{PARAMS_VERIFIER, Proof, VerifierKey},
};
use sha2::{Digest, Sha256};

use crate::{Args, jobs, params::ParamsCache};

fn base(dir: &Path, job: &str, rep: u32) -> PathBuf {
    dir.join(format!("{}.{rep}", job.replace('/', "__")))
}

/// Writes one proof and its statement.
pub fn write(dir: &Path, job: &str, rep: u32, k: u8, proof: &Proof, pis: &[Fr]) {
    let b = base(dir, job, rep);
    std::fs::write(b.with_extension(format!("{rep}.proof")), &proof.0).expect("write proof");
    let mut f = std::fs::File::create(b.with_extension(format!("{rep}.pis"))).expect("write pis");
    writeln!(f, "k={k}").unwrap();
    for x in pis {
        let mut v = Vec::new();
        Serializable::serialize(x, &mut v).unwrap();
        writeln!(f, "{}", hex::encode(v)).unwrap();
    }
}

/// Reads a statement: `k` and the raw lines of the public inputs.
fn read_pis(path: &Path) -> Option<(u8, Vec<String>)> {
    let s = std::fs::read_to_string(path).ok()?;
    let mut lines = s.lines();
    let k = lines.next()?.strip_prefix("k=")?.parse().ok()?;
    Some((k, lines.map(str::to_string).collect()))
}

/// Entry point of `compact-bench verify`.
pub fn verify(a: &Args) -> i32 {
    let jobs = jobs::read_jobs(a.req("jobs"));
    let params = ParamsCache::new(PathBuf::from(a.req("params")));
    let dump = PathBuf::from(a.req("dump"));
    let stock = PathBuf::from(a.req("statements"));
    let mut out = std::fs::File::create(a.req("out")).expect("create output");
    writeln!(
        out,
        "job\tk\trep\tproof_sha256\tverified_server\tverified_ledger\tstatement_equal\tproof_equal_stock"
    )
    .unwrap();
    let (mut n, mut bad) = (0, 0);
    for job in &jobs {
        let Some((sk, spis)) = read_pis(&base(&stock, &job.job, 0).with_extension("0.pis")) else {
            eprintln!("{}: no stock statement", job.job);
            bad += 1;
            continue;
        };
        let stock_proof = std::fs::read(base(&stock, &job.job, 0).with_extension("0.proof")).ok();
        let vk: VerifierKey = tagged_deserialize(
            &mut &std::fs::read(&job.verifier_key).expect("read verifier key")[..],
        )
        .expect("decode verifier key");
        let pv = params.verifier(sk).expect("read verifier params");
        let statement: Vec<Fr> = spis.iter().map(|h| jobs::fr_from_hex(h)).collect();
        let mut rep = 0;
        loop {
            let b = base(&dump, &job.job, rep);
            let Ok(bytes) = std::fs::read(b.with_extension(format!("{rep}.proof"))) else {
                break;
            };
            let equal = read_pis(&b.with_extension(format!("{rep}.pis")))
                .is_some_and(|(k, p)| k == sk && p == spis);
            let proof = Proof(bytes);
            let vs = vk.verify(&pv, &proof, statement.iter().copied()).is_ok();
            let vl = vk.verify(&PARAMS_VERIFIER, &proof, statement.iter().copied()).is_ok();
            let same = stock_proof.as_ref().is_some_and(|p| *p == proof.0);
            writeln!(
                out,
                "{}\t{sk}\t{rep}\t{}\t{vs}\t{vl}\t{equal}\t{same}",
                job.job,
                hex::encode(Sha256::digest(&proof.0))
            )
            .unwrap();
            n += 1;
            if !(vs && vl && equal) {
                bad += 1;
            }
            rep += 1;
        }
        if rep == 0 {
            eprintln!("{}: no dumped proof", job.job);
            bad += 1;
        }
    }
    println!("{n} proofs checked, {bad} failed (verification, statement or missing)");
    i32::from(bad > 0)
}
