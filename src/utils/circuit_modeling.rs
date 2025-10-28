use std::{
    collections::BTreeMap,
    fs, io,
    io::Write,
    iter,
    sync::{Arc, Mutex, OnceLock},
};

use blstrs::Scalar;
use ff::{FromUniformBytes, PrimeField};
use goldenfile::Mint;
use halo2_proofs::{
    dev::cost_model::{from_circuit_to_cost_model_options, CostOptions},
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
    public: &[&[F]],
    circuit: impl Circuit<F>,
) where
    F: FromUniformBytes<64> + Ord,
{
    // Store model only when tests are run in BLS12-381 (i.e. when the
    // native scalar is BLS's scalar
    if F::MODULUS == Scalar::MODULUS {
        let instances = public.iter().map(|x| x.to_vec()).collect();
        let options = from_circuit_to_cost_model_options(k, &circuit, instances);
        update_json(chip_name, op_name, options).expect("csv generation failed");
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

fn update_json(chip_name: &str, op_name: &str, model: CostOptions) -> io::Result<()> {
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

fn report_model_json(model: &CostOptions, json_value: &mut Value) -> io::Result<()> {
    let (column_queries, point_sets): (usize, usize) = compute_queries(model);

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
        model.max_degree.to_string(),
        model.rows_count.to_string(),
        model.table_rows_count.to_string(),
        model.advice.len().to_string(),
        model.fixed.len().to_string(),
        model.lookup.len().to_string(),
        model.permutation.nr_columns().to_string(),
        column_queries.to_string(),
        point_sets.to_string(),
    ];

    let mut map = BTreeMap::new();
    for (key, value) in headers.iter().zip(row.into_iter()) {
        map.insert(*key, value);
    }

    // Serialize the HashMap to JSON
    *json_value = serde_json::to_value(&map)?;

    Ok(())
}

fn compute_queries(model: &CostOptions) -> (usize, usize) {
    let mut queries: Vec<_> = iter::empty()
        .chain(model.advice.iter())
        .chain(model.instance.iter())
        .chain(model.fixed.iter())
        .cloned()
        .chain(model.lookup.iter().flat_map(|l| l.queries()))
        .chain(model.permutation.queries())
        .chain(iter::repeat("0".parse().unwrap()).take(model.max_degree - 1))
        .collect();

    let column_queries = queries.len();
    queries.sort_unstable();
    queries.dedup();
    let point_sets = queries.len();

    (column_queries, point_sets)
}
