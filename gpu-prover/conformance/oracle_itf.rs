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

use super::*;

fn decode(value: Value) -> Value {
    match value {
        Value::Object(mut record) if record.contains_key("#bigint") => {
            json!(record.remove("#bigint").unwrap().as_str().unwrap().parse::<u64>().unwrap())
        }
        Value::Object(record) => record.into_iter().map(|(k, v)| (k, decode(v))).collect(),
        Value::Array(list) => Value::Array(list.into_iter().map(decode).collect()),
        other => other,
    }
}

fn trace(path: &Path, root: &Path) -> Trace {
    let raw: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    let mut states = Vec::new();
    let mut ops = Vec::new();
    for (i, state) in raw["states"].as_array().unwrap().iter().enumerate() {
        let field = |short| {
            let key = raw["vars"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v.as_str().unwrap())
                .find(|k| k.rsplit("::").next() == Some(short))
                .unwrap();
            decode(state[key].clone())
        };
        states.push(field("s"));
        if i != 0 {
            ops.push(field("lastOp").as_u64().unwrap());
        }
    }
    Trace {
        format: "midnight-gpu-vectors/2".to_owned(),
        name: path.strip_prefix(root).unwrap().to_str().unwrap().to_owned(),
        config: states[0].clone(),
        refused: vec![vec![]; ops.len()],
        states,
        ops,
    }
}

#[test]
#[ignore = "requires the frozen Quint ITF files and an output path"]
fn quint_daemon_gate() {
    let root =
        std::path::PathBuf::from(std::env::var_os("ORACLE_ITF_DIR").expect("ORACLE_ITF_DIR"));
    let output =
        File::create(std::env::var_os("ORACLE_ITF_EVIDENCE").expect("ORACLE_ITF_EVIDENCE"))
            .unwrap();
    let mut paths = Vec::new();
    for dir in fs::read_dir(&root).unwrap() {
        for file in fs::read_dir(dir.unwrap().path()).unwrap() {
            let p = file.unwrap().path();
            if p.to_string_lossy().ends_with(".itf.json") {
                paths.push(p);
            }
        }
    }
    paths.sort();
    assert!(!paths.is_empty());
    let params = ParamsKZG::unsafe_setup(
        midnight_zk_stdlib::optimal_k(&PoseidonPreimage),
        rand_chacha::ChaCha8Rng::seed_from_u64(9),
    );
    let writer = Mutex::new(std::io::BufWriter::new(output));
    let totals = Mutex::new((0, 0, 0, 0));
    let next = AtomicUsize::default();
    thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, SeqCst);
                let Some(path) = paths.get(i) else { break };
                let t = trace(path, &root);
                let checks = replay(&t, &params, None, true);
                let mismatches = checks.rows.iter().map(|r| number(r, "step")).collect::<BTreeSet<_>>();
                let mut totals = totals.lock().unwrap();
                totals.0 += 1;
                totals.1 += t.ops.len();
                totals.2 += mismatches.len();
                totals.3 += checks.rows.len();
                let row = json!({"trace": t.name, "transitions": t.ops.len(), "comparisons": checks.comparisons,
                    "mismatching_steps": mismatches.len(), "disagreements": checks.rows});
                let mut writer = writer.lock().unwrap();
                writeln!(writer, "{row}").unwrap();
                writer.flush().unwrap();
                if totals.0 % 100 == 0 { eprintln!("{} ITF traces replayed", totals.0); }
            });
        }
    });
    let (files, transitions, mismatches, fields) = totals.into_inner().unwrap();
    eprintln!(
        "daemon ITF: {files} files, {transitions} transitions, {mismatches} mismatching steps, {fields} differing field observations"
    );
    assert_eq!((files, transitions), (1077, 40471));
    assert_eq!(
        (mismatches, fields),
        (0, 0),
        "daemon disagrees with the frozen Quint gate"
    );
}
