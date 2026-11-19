// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
};

use serde_json::Value;

/// Read the oracle's payload policy. V1 exported arithmetic and service files
/// only. A v2 arithmetic corpus must supply the data-movement plans as well.
pub(super) fn permitted() -> Option<BTreeMap<String, u64>> {
    let root = std::env::var_os("ORACLE_VECTOR_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../gpu-spec/vectors"));
    let mut policy = None;
    let mut v2 = false;
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "json") {
            continue;
        }
        let file: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        v2 |= file["format"] == "midnight-gpu-vectors/2";
        if file["kind"] != "datamove" {
            continue;
        }
        assert_eq!(file["format"], "midnight-gpu-vectors/2");
        let names = |list: &Value| -> BTreeSet<String> {
            list.as_array()
                .unwrap()
                .iter()
                .map(|entry| entry["kind"].as_str().unwrap().to_owned())
                .collect()
        };
        let allowed = names(&file["permitted"]);
        let forbidden = names(&file["forbidden"]);
        assert!(allowed.is_disjoint(&forbidden));
        for required in ["extended", "zeroed-region"] {
            assert!(forbidden.contains(required));
        }
        let mut plans = BTreeSet::new();
        for plan in file["plans"].as_array().unwrap() {
            let name = plan["name"].as_str().unwrap();
            assert!(plans.insert(name));
            let executable = plan["executable"].as_bool().unwrap();
            if matches!(name, "spec" | "old-port" | "msm-buckets") {
                assert!(executable, "reference plan {name} must execute");
            }
            let mut offending = Vec::new();
            for kind in plan["trace"].as_array().unwrap() {
                let name = kind.as_str().unwrap();
                assert!(allowed.contains(name) || forbidden.contains(name), "{name}");
                if forbidden.contains(name) {
                    offending.push(kind);
                }
            }
            assert_eq!(plan["gpu038"], offending.is_empty());
            assert!(offending.into_iter().eq(plan["offending"].as_array().unwrap()));
            eprintln!("vector table pass datamove.json / {name}");
        }
        assert!(["spec", "old-port", "msm-buckets"].iter().all(|p| plans.contains(*p)));
        let mut wire = BTreeMap::new();
        for row in file["permitted"].as_array().unwrap() {
            let name = row["kind"].as_str().unwrap();
            let field = row.get("code").expect("missing read-back code");
            let code = field.as_u64().expect("permitted read-back code");
            assert!(wire.insert(name.to_owned(), code).is_none());
        }
        for (name, code) in [
            ("quotient-coeffs", 0),
            ("msm-point", 1),
            ("msm-buckets", 1),
            ("counter", 2),
            ("base-transform", 3),
        ] {
            assert_eq!(wire.get(name), Some(&code), "service read-back kind {name}");
        }
        assert!(policy.replace(wire).is_none(), "duplicate datamove file");
    }
    assert!(
        !v2 || policy.is_some(),
        "v2 corpus missing datamove fixture"
    );
    policy
}
