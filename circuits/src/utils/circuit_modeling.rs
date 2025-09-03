// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
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

use std::{
    collections::BTreeMap,
    fs, io,
    io::Write,
    sync::{Arc, Mutex, OnceLock},
};

use ff::{FromUniformBytes, PrimeField};
use goldenfile::Mint;
use midnight_curves::Fq;
use midnight_proofs::{
    dev::cost_model::{from_circuit_to_circuit_model, CircuitModel},
    plonk::Circuit,
};
use serde_json::{json, Map, Value};

/// Obtains the cost-model provided by `[ModelCircuit] of `circuit` .
/// Serializes the cost-model into a `csv`.
///
/// If the reference `csv` differs in a future benchmark, performance of the
/// module has changed. An alert is triggered by `goldenfile` which requires
/// manual inspection. If the change is approved, a new reference `goldenfile`
/// can be writen over the old one.`
///
/// Does nothing on Windows since goldenfiles do not work due to different line
/// endings.
#[cfg(not(target_os = "windows"))]
pub fn circuit_to_json<F>(
    k: u32,
    chip_name: &str,
    op_name: &str,
    nb_public_inputs: usize,
    circuit: impl Circuit<F>,
) where
    F: FromUniformBytes<64> + Ord,
{
    // Store model only when tests are run in BLS12-381 (i.e. when the
    // native scalar is BLS's scalar
    if F::MODULUS == Fq::MODULUS {
        let model =
            from_circuit_to_circuit_model::<F, _, 48, 32>(Some(k), &circuit, nb_public_inputs);
        update_json(chip_name, op_name, model).expect("csv generation failed");
    }
}

#[cfg(target_os = "windows")]
/// Does nothing on Windows since goldenfiles do not work due to different line
/// endings.
pub fn circuit_to_json<F>(k: u32, name: &str, public: &[&[F]], circuit: impl Circuit<F> + Clone)
where
    F: FromUniformBytes<64> + Ord,
{
}

// Use OnceLock to initialize the Arc<Mutex<()>>
static FILE_MUTEX: OnceLock<Arc<Mutex<()>>> = OnceLock::new();

fn get_file_mutex() -> &'static Arc<Mutex<()>> {
    FILE_MUTEX.get_or_init(|| Arc::new(Mutex::new(())))
}

fn update_json(chip_name: &str, op_name: &str, model: CircuitModel) -> io::Result<()> {
    // Acquire the lock on the mutex
    let _lock = get_file_mutex()
        .lock()
        .expect("Failed to acquire mutex lock");

    let file_path = "goldenfiles/cost-model.json";
    let mut mint = Mint::new("goldenfiles");

    // Read and parse the file content
    let content = fs::read_to_string(file_path).unwrap_or("{}".to_string());
    let mut json_value: Value = serde_json::from_str(&content).expect("Failed to parse JSON.");

    // Modify the JSON content
    if json_value.get(chip_name).is_none() {
        json_value[chip_name] = json!({});
    }

    if json_value[chip_name].get(op_name).is_none() {
        json_value[chip_name][op_name] = json!({});
    }

    report_model_json(&model, &mut json_value[chip_name][op_name])
        .expect("Failed to construct JSON.");

    // We need to sort the JSON, to make sure it is always the same
    json_value = sort_json(json_value);

    let mut goldenfile = mint
        .new_goldenfile("cost-model.json")
        .expect("Failed to mint Goldenfile.");
    writeln!(goldenfile, "{}", serde_json::to_string_pretty(&json_value)?).expect("7");

    Ok(())
}

fn sort_json(value: Value) -> Value {
    match value {
        Value::Object(map) => {
            let mut sorted_map = Map::new();
            let mut keys: Vec<_> = map.keys().collect();
            keys.sort();
            for key in keys {
                if let Some(val) = map.get(key) {
                    sorted_map.insert(key.clone(), sort_json(val.clone()));
                }
            }
            Value::Object(sorted_map)
        }
        Value::Array(arr) => Value::Array(arr.into_iter().map(sort_json).collect()),
        _ => value,
    }
}

fn report_model_json(model: &CircuitModel, json_value: &mut Value) -> io::Result<()> {
    let headers = [
        "max_deg",
        "rows",
        "table_rows",
        "advice_columns",
        "fixed_columns",
        "lookups",
        "permutations",
        "column_queries",
        "point_sets",
    ];
    let row = vec![
        model.max_deg.to_string(),
        model.rows.to_string(),
        model.table_rows.to_string(),
        model.advice_columns.to_string(),
        model.fixed_columns.to_string(),
        model.lookups.to_string(),
        model.permutations.to_string(),
        model.column_queries.to_string(),
        model.point_sets.to_string(),
    ];

    let mut map = BTreeMap::new();
    for (key, value) in headers.iter().zip(row.into_iter()) {
        map.insert(*key, value);
    }

    // Serialize the HashMap to JSON
    *json_value = serde_json::to_value(&map)?;

    Ok(())
}
