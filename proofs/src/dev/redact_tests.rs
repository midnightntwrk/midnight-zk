//! Tests that developer-tool output withholds assigned cell values when the
//! `gpu` feature is enabled, and shows them when it is not.
#![allow(dead_code)]

use std::{
    fmt::Debug,
    num::NonZeroU64,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
    },
};

use midnight_curves::Fq as Scalar;
use tracing::{
    Event, Id, Metadata, Subscriber,
    field::{Field as TracingField, Visit},
    span::{Attributes, Record},
    subscriber::with_default,
};

use super::{MockProver, TracingFloorPlanner, VerifyFailure};
use crate::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Selector,
        TableColumn,
    },
    poly::Rotation,
};

const DISTINCT: u64 = 0xdead_beef_cafe;
const PLACEHOLDER: &str = "<withheld>";

fn distinct_forms() -> Vec<String> {
    vec![
        "deadbeefcafe".to_string(),
        "0xdeadbeefcafe".to_string(),
        DISTINCT.to_string(),
    ]
}

fn assert_clean(what: &str, text: &str) {
    for needle in distinct_forms() {
        assert!(
            !text.contains(&needle),
            "{what} contains witness value form {needle:?}:\n{text}"
        );
    }
}

#[allow(dead_code)]
fn assert_shows(what: &str, text: &str) {
    assert!(
        distinct_forms().iter().any(|needle| text.contains(needle)),
        "{what} does not show the witness value:\n{text}"
    );
}

// Circuit with an unsatisfied equality gate over a distinctive value.
#[derive(Clone)]
struct UnsatConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    q: Selector,
}

struct UnsatCircuit;

fn configure_unsat(meta: &mut ConstraintSystem<Scalar>) -> UnsatConfig {
    let a = meta.advice_column();
    let b = meta.advice_column();
    let q = meta.selector();
    meta.create_gate("redact equality check", |cells| {
        let a = cells.query_advice(a, Rotation::cur());
        let b = cells.query_advice(b, Rotation::cur());
        Constraints::with_selector(q, vec![("redact eq", a - b)])
    });
    UnsatConfig { a, b, q }
}

fn synthesize_unsat(config: UnsatConfig, mut layouter: impl Layouter<Scalar>) -> Result<(), Error> {
    layouter.assign_region(
        || "redact region",
        |mut region| {
            config.q.enable(&mut region, 0)?;
            region.assign_advice(|| "a", config.a, 0, || Value::known(Scalar::from(DISTINCT)))?;
            region.assign_advice(|| "b", config.b, 0, || Value::known(Scalar::from(7u64)))?;
            region.name_column(|| "witness a", config.a);
            Ok(())
        },
    )
}

impl Circuit<Scalar> for UnsatCircuit {
    type Config = UnsatConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self::Config {
        configure_unsat(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        synthesize_unsat(config, layouter)
    }
}

// Same assignments routed through the tracing floor planner.
struct TracingCircuit;

impl Circuit<Scalar> for TracingCircuit {
    type Config = UnsatConfig;
    type FloorPlanner = TracingFloorPlanner<SimpleFloorPlanner>;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self::Config {
        let config = configure_unsat(meta);
        meta.enable_equality(config.a);
        meta.enable_equality(config.b);
        let fixed = meta.fixed_column();
        meta.enable_constant(fixed);
        config
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "redact region",
            |mut region| {
                config.q.enable(&mut region, 0)?;
                let a = region.assign_advice(
                    || "a",
                    config.a,
                    0,
                    || Value::known(Scalar::from(DISTINCT)),
                )?;
                region.assign_advice_from_constant(|| "b", config.b, 0, Scalar::from(DISTINCT))?;
                region.constrain_constant(a.cell(), Scalar::from(DISTINCT))?;
                Ok(())
            },
        )
    }
}

// Circuit with a lookup whose input is the distinctive value.
struct BadLookupCircuit;

#[derive(Clone)]
struct BadLookupConfig {
    a: Column<Advice>,
    q: Selector,
    table: TableColumn,
}

impl Circuit<Scalar> for BadLookupCircuit {
    type Config = BadLookupConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self::Config {
        let a = meta.advice_column();
        let q = meta.complex_selector();
        let table = meta.lookup_table_column();
        meta.lookup("redact lookup", None, |cells| {
            let a = cells.query_advice(a, Rotation::cur());
            let q = cells.query_selector(q);
            let not_q = Expression::from(1) - q.clone();
            let default = Expression::from(2);
            vec![(q * a + not_q * default, table)]
        });
        BadLookupConfig { a, q, table }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "small table",
            |mut table| {
                for (i, v) in [2u64, 4, 6, 8].into_iter().enumerate() {
                    table.assign_cell(
                        || "table cell",
                        config.table,
                        i,
                        || Value::known(Scalar::from(v)),
                    )?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "redact lookup region",
            |mut region| {
                config.q.enable(&mut region, 0)?;
                region.assign_advice(
                    || "a",
                    config.a,
                    0,
                    || Value::known(Scalar::from(DISTINCT)),
                )?;
                Ok(())
            },
        )
    }
}

// Circuit with an equality (permutation) constraint between unequal cells.
struct BadPermutationCircuit;

#[derive(Clone)]
struct BadPermutationConfig {
    a: Column<Advice>,
    b: Column<Advice>,
}

impl Circuit<Scalar> for BadPermutationCircuit {
    type Config = BadPermutationConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        meta.enable_equality(a);
        meta.enable_equality(b);
        BadPermutationConfig { a, b }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "redact perm region",
            |mut region| {
                let a = region.assign_advice(
                    || "a",
                    config.a,
                    0,
                    || Value::known(Scalar::from(DISTINCT)),
                )?;
                let b = region.assign_advice(
                    || "b",
                    config.b,
                    0,
                    || Value::known(Scalar::from(7u64)),
                )?;
                region.constrain_equal(a.cell(), b.cell())?;
                Ok(())
            },
        )
    }
}

// A `tracing` subscriber that records span and event fields as text.
struct Capture {
    log: Arc<Mutex<Vec<String>>>,
    next_id: AtomicU64,
}

struct FieldVisitor<'a>(&'a mut String);

impl Visit for FieldVisitor<'_> {
    fn record_debug(&mut self, field: &TracingField, value: &dyn Debug) {
        self.0.push_str(&format!("{}={value:?} ", field.name()));
    }

    fn record_str(&mut self, field: &TracingField, value: &str) {
        self.0.push_str(&format!("{}={value:?} ", field.name()));
    }

    fn record_i64(&mut self, field: &TracingField, value: i64) {
        self.0.push_str(&format!("{}={value} ", field.name()));
    }

    fn record_u64(&mut self, field: &TracingField, value: u64) {
        self.0.push_str(&format!("{}={value} ", field.name()));
    }

    fn record_bool(&mut self, field: &TracingField, value: bool) {
        self.0.push_str(&format!("{}={value} ", field.name()));
    }
}

impl Subscriber for Capture {
    fn enabled(&self, _: &Metadata<'_>) -> bool {
        true
    }

    fn new_span(&self, attrs: &Attributes<'_>) -> Id {
        let mut fields = String::new();
        attrs.record(&mut FieldVisitor(&mut fields));
        self.log
            .lock()
            .unwrap()
            .push(format!("span {} {}", attrs.metadata().name(), fields));
        let n = self.next_id.fetch_add(1, Ordering::SeqCst);
        Id::from_non_zero_u64(NonZeroU64::new(n).unwrap())
    }

    fn record(&self, _: &Id, _: &Record<'_>) {}

    fn record_follows_from(&self, _: &Id, _: &Id) {}

    fn event(&self, event: &Event<'_>) {
        let mut fields = String::new();
        event.record(&mut FieldVisitor(&mut fields));
        self.log
            .lock()
            .unwrap()
            .push(format!("event {} {}", event.metadata().target(), fields));
    }

    fn enter(&self, _: &Id) {}

    fn exit(&self, _: &Id) {}
}

fn capture_tracing_output() -> String {
    let log = Arc::new(Mutex::new(Vec::new()));
    let capture = Capture {
        log: log.clone(),
        next_id: AtomicU64::new(1),
    };
    let result = with_default(capture, || {
        MockProver::<Scalar>::run(&TracingCircuit, vec![])
    });
    assert!(result.is_ok(), "tracing synthesis failed: {result:?}");
    log.lock().unwrap().join("\n")
}

fn unsat_failures() -> (MockProver<Scalar>, Vec<VerifyFailure>) {
    let prover = MockProver::<Scalar>::run(&UnsatCircuit, vec![]).unwrap();
    let failures = prover.verify().expect_err("circuit must be unsatisfied");
    assert!(
        failures
            .iter()
            .any(|f| matches!(f, VerifyFailure::ConstraintNotSatisfied { .. })),
        "expected a ConstraintNotSatisfied failure, got {failures:?}"
    );
    (prover, failures)
}

#[cfg(feature = "gpu")]
#[test]
fn gate_failure_output_withholds_value() {
    let (prover, failures) = unsat_failures();
    let display = failures.iter().map(|f| f.to_string()).collect::<Vec<_>>().join("\n");
    let debug = format!("{failures:#?}");
    assert_clean("VerifyFailure Display", &display);
    assert_clean("VerifyFailure Debug", &debug);
    assert!(display.contains(PLACEHOLDER), "Display:\n{display}");
    assert!(debug.contains(PLACEHOLDER), "Debug:\n{debug}");
    assert!(display.contains("redact equality check"), "{display}");
    assert!(display.contains("redact region"), "{display}");
    assert!(display.contains("Advice"), "{display}");
    assert!(display.contains("offset 0"), "{display}");

    // The stored strings carry no value either.
    for failure in &failures {
        if let VerifyFailure::ConstraintNotSatisfied { cell_values, .. } = failure {
            assert!(!cell_values.is_empty());
            for (_, value) in cell_values {
                assert_clean("stored cell value", value);
                assert_eq!(value, PLACEHOLDER);
            }
        }
    }

    let prover_debug = format!("{prover:?}");
    assert_clean("MockProver Debug", &prover_debug);
    assert!(prover_debug.contains(PLACEHOLDER), "{prover_debug:.200}");
}

#[cfg(feature = "gpu")]
#[test]
fn lookup_failure_output_withholds_value() {
    let prover = MockProver::<Scalar>::run(&BadLookupCircuit, vec![]).unwrap();
    let failures = prover.verify().expect_err("lookup must fail");
    assert!(
        failures.iter().any(|f| matches!(f, VerifyFailure::Lookup { .. })),
        "expected a Lookup failure, got {failures:?}"
    );
    let display = failures.iter().map(|f| f.to_string()).collect::<Vec<_>>().join("\n");
    let debug = format!("{failures:#?}");
    assert_clean("Lookup Display", &display);
    assert_clean("Lookup Debug", &debug);
    assert!(display.contains("redact lookup"), "{display}");
    let prover_debug = format!("{prover:?}");
    assert_clean("MockProver Debug (lookup)", &prover_debug);
}

#[cfg(feature = "gpu")]
#[test]
fn permutation_failure_output_withholds_value() {
    let prover = MockProver::<Scalar>::run(&BadPermutationCircuit, vec![]).unwrap();
    let failures = prover.verify().expect_err("permutation must fail");
    assert!(
        failures.iter().any(|f| matches!(f, VerifyFailure::Permutation { .. })),
        "expected a Permutation failure, got {failures:?}"
    );
    let display = failures.iter().map(|f| f.to_string()).collect::<Vec<_>>().join("\n");
    let debug = format!("{failures:#?}");
    assert_clean("Permutation Display", &display);
    assert_clean("Permutation Debug", &debug);
    assert!(display.contains("Equality constraint"), "{display}");
    let prover_debug = format!("{prover:?}");
    assert_clean("MockProver Debug (permutation)", &prover_debug);
}

#[cfg(feature = "gpu")]
#[test]
fn assert_satisfied_panic_withholds_value() {
    let (prover, _) = unsat_failures();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prover.assert_satisfied();
    }));
    let payload = result.expect_err("assert_satisfied must panic");
    let message = if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        String::new()
    };
    assert_clean("assert_satisfied panic message", &message);
    assert_eq!(message, "circuit was not satisfied");
}

#[cfg(feature = "gpu")]
#[test]
fn tracing_floor_planner_withholds_value() {
    let output = capture_tracing_output();
    assert_clean("tracing output", &output);
    assert!(output.contains(PLACEHOLDER), "tracing output:\n{output}");
    assert!(output.contains("assigned"), "tracing output:\n{output}");
}

#[cfg(not(feature = "gpu"))]
#[test]
fn gate_failure_output_shows_value_feature_off() {
    let (prover, failures) = unsat_failures();
    let display = failures.iter().map(|f| f.to_string()).collect::<Vec<_>>().join("\n");
    let debug = format!("{failures:#?}");
    assert_shows("VerifyFailure Display (feature off)", &display);
    assert_shows("VerifyFailure Debug (feature off)", &debug);
    assert!(display.contains("redact equality check"), "{display}");
    let prover_debug = format!("{prover:?}");
    assert_shows("MockProver Debug (feature off)", &prover_debug);
}

#[cfg(not(feature = "gpu"))]
#[test]
fn tracing_floor_planner_shows_value_feature_off() {
    let output = capture_tracing_output();
    assert_shows("tracing output (feature off)", &output);
}
