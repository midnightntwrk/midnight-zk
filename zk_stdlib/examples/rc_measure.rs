//! Measurement harness (not for commit): breaks down how many rows / cells go
//! to range checks in a few foreign-field-heavy relations.
//!
//! Run: cargo run --release -j 2 -p midnight-zk-stdlib --example rc_measure

#[allow(dead_code)]
#[path = "bitcoin_signature.rs"]
mod btc;
#[allow(dead_code)]
#[path = "ethereum_signature.rs"]
mod eth;

use std::{
    backtrace::Backtrace,
    collections::{BTreeMap, HashSet},
    io,
};

use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed, FloorPlanner,
        Instance, Selector,
    },
    utils::rational::Rational,
};
use midnight_zk_stdlib::{MidnightCircuit, Relation, ZkStdLib, ZkStdLibArch};

type F = midnight_curves::Fq;

/// Wraps a relation, overriding `nr_pow2range_cols`.
#[derive(Clone)]
struct WithCols<R>(R, u8);

impl<R: Relation> Relation for WithCols<R> {
    type Instance = R::Instance;
    type Witness = R::Witness;
    type Error = R::Error;

    fn format_instance(i: &Self::Instance) -> Result<Vec<F>, Self::Error> {
        R::format_instance(i)
    }
    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Self::Error> {
        self.0.circuit(std_lib, layouter, instance, witness)
    }
    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            nr_pow2range_cols: self.1,
            ..self.0.used_chips()
        }
    }
    fn write_relation<W: io::Write>(&self, _: &mut W) -> io::Result<()> {
        Ok(())
    }
    fn read_relation<Rd: io::Read>(_: &mut Rd) -> io::Result<Self> {
        unimplemented!()
    }
}

#[derive(Default)]
struct RegionStat {
    name: String,
    /// `Some(caller)` if the region is range-check overhead.
    rc_caller: Option<String>,
    rows: HashSet<usize>,
    cells: usize,
    tags: Vec<u64>,
}

#[derive(Default)]
struct Rec {
    regions: Vec<RegionStat>,
    cur: Option<RegionStat>,
    max_row: usize,
    copies: usize,
}

const RC_MARKERS: [&str; 4] = ["lower_than_fixed", "decompos", "pow2", "assign_many_small"];
const RC_REGIONS: [&str; 5] = [
    "decompose core",
    "assign limbs decompose fixed",
    "assign_many_small",
    "Assign values",
    "copy",
];
const RC_INTERNAL: [&str; 5] = [
    "field::native::",
    "field::decomposition::",
    "instructions::",
    "midnight_proofs::",
    "core::",
];

/// Returns the caller of the outermost range-check function on the stack, if
/// any.
fn classify(bt: &str) -> Option<String> {
    let frames: Vec<&str> = bt
        .lines()
        .map(str::trim)
        .filter(|l| l.contains(": ") && !l.starts_with("at "))
        .map(|l| l.split_once(": ").unwrap().1)
        .collect();
    // Frames go innermost -> outermost. Find outermost rc frame.
    let outer_rc = frames
        .iter()
        .rposition(|f| f.contains("midnight_circuits") && RC_MARKERS.iter().any(|m| f.contains(m)))
        .unwrap_or(0);
    let caller = frames[outer_rc..].iter().find(|f| f.contains("::foreign::")).or_else(|| {
        frames[outer_rc + 1..]
            .iter()
            .find(|f| f.contains("midnight_circuits") && !RC_INTERNAL.iter().any(|m| f.contains(m)))
    })?;
    let clean: String = {
        let mut depth = 0;
        caller
            .chars()
            .filter(|c| {
                match c {
                    '<' => depth += 1,
                    '>' => depth -= 1,
                    _ => return depth == 0,
                }
                false
            })
            .collect()
    };
    let clean = clean.rsplit_once("::h").map(|(a, _)| a.to_string()).unwrap_or(clean);
    Some(clean.replace("midnight_circuits::", "").replace("{{closure}}", "{}"))
}

impl Rec {
    fn touch(&mut self, row: usize) {
        if let Some(r) = self.cur.as_mut() {
            if r.name != "pow2range table" {
                self.max_row = self.max_row.max(row);
            }
            r.rows.insert(row);
            r.cells += 1;
        }
    }
}

impl Assignment<F> for Rec {
    fn enter_region<NR: Into<String>, N: FnOnce() -> NR>(&mut self, name: N) {
        let name: String = name().into();
        let rc = RC_REGIONS.contains(&name.as_str());
        self.cur = Some(RegionStat {
            rc_caller: if rc {
                Some(classify(&Backtrace::force_capture().to_string()).unwrap_or("?".into()))
            } else {
                None
            },
            name,
            ..Default::default()
        });
    }
    fn annotate_column<A: FnOnce() -> AR, AR: Into<String>>(&mut self, _: A, _: Column<Any>) {}
    fn exit_region(&mut self) {
        self.regions.push(self.cur.take().unwrap());
    }
    fn enable_selector<A: FnOnce() -> AR, AR: Into<String>>(
        &mut self,
        _: A,
        _: &Selector,
        _row: usize,
    ) -> Result<(), Error> {
        Ok(())
    }
    fn query_instance(&self, _: Column<Instance>, _: usize) -> Result<Value<F>, Error> {
        Ok(Value::unknown())
    }
    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Advice>,
        row: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.touch(row);
        Ok(())
    }
    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        ann: A,
        _: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if self.cur.is_none() {
            return Ok(());
        }
        if ann().into() == "pow2range_tag" {
            to().map(|v| {
                let f: F = v.into().evaluate();
                let b = f.to_bytes_le();
                let t = u64::from_le_bytes(b[..8].try_into().unwrap());
                self.cur.as_mut().unwrap().tags.push(t);
            });
        }
        self.touch(row);
        Ok(())
    }
    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        self.copies += 1;
        Ok(())
    }
    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Rational<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }
    fn push_namespace<NR: Into<String>, N: FnOnce() -> NR>(&mut self, _: N) {}
    fn pop_namespace(&mut self, _: Option<String>) {}
}

fn measure<R: Relation + Clone>(label: &str, relation: R) {
    let circuit = MidnightCircuit::from_relation(&relation, None);
    let params = circuit.params();
    let mut cs = ConstraintSystem::<F>::default();
    let config = MidnightCircuit::<R>::configure_with_params(&mut cs, params);
    let mut rec = Rec::default();
    <MidnightCircuit<R> as Circuit<F>>::FloorPlanner::synthesize(
        &mut rec,
        &circuit,
        config,
        cs.constants().clone(),
    )
    .unwrap();

    let nb_rc_cols = params.0.nr_pow2range_cols;
    let total_rows = rec.max_row + 1;
    let all_rows: usize = rec.regions.iter().map(|r| r.rows.len()).sum();
    let all_cells: usize = rec.regions.iter().map(|r| r.cells).sum();
    let rc: Vec<&RegionStat> = rec.regions.iter().filter(|r| r.rc_caller.is_some()).collect();
    let all_rows: usize = all_rows
        - rec
            .regions
            .iter()
            .filter(|r| r.name == "pow2range table")
            .map(|r| r.rows.len())
            .sum::<usize>();
    let rc_rows: usize = rc.iter().map(|r| r.rows.len()).sum();
    let rc_cells: usize = rc.iter().map(|r| r.cells).sum();

    println!(
        "\n================ {label} (nr_pow2range_cols = {nb_rc_cols}, max_bit_len = {}) ================",
        params.1
    );
    let table_rows: usize = rec
        .regions
        .iter()
        .filter(|r| r.name == "pow2range table")
        .map(|r| r.rows.len())
        .sum();
    println!("circuit rows (excl. table): {total_rows}   pow2range table rows: {table_rows}");
    println!(
        "used rows: {total_rows}   sum of region rows: {all_rows}   cells: {all_cells}   copies: {}",
        rec.copies
    );
    println!(
        "range-check regions: {}   rows: {rc_rows} ({:.1}% of region rows)   cells: {rc_cells} ({:.1}%)",
        rc.len(),
        100.0 * rc_rows as f64 / all_rows as f64,
        100.0 * rc_cells as f64 / all_cells as f64
    );

    // By caller.
    let mut by_caller: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for r in &rc {
        let e = by_caller.entry(r.rc_caller.clone().unwrap()).or_default();
        e.0 += 1;
        e.1 += r.rows.len();
    }
    let mut v: Vec<_> = by_caller.into_iter().collect();
    v.sort_by_key(|(_, (_, rows))| std::cmp::Reverse(*rows));
    println!("\n  rc rows by caller (regions, rows):");
    for (c, (n, rows)) in v.iter().take(15) {
        println!("    {rows:>8} {n:>7}  {c}");
    }

    // By region name (range-check regions).
    let mut by_name: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for r in &rc {
        let e = by_name.entry(r.name.clone()).or_default();
        e.0 += 1;
        e.1 += r.rows.len();
    }
    println!("\n  rc rows by region name (regions, rows):");
    for (c, (n, rows)) in &by_name {
        println!("    {rows:>8} {n:>7}  {c}");
    }

    // Tag histogram: one tag per lookup row.
    let mut tag_hist: BTreeMap<u64, usize> = BTreeMap::new();
    for t in rec.regions.iter().flat_map(|r| r.tags.iter()) {
        *tag_hist.entry(*t).or_default() += 1;
    }
    println!("\n  lookup rows by tag (tag: rows):  {tag_hist:?}");

    // Requested-check shape: the multiset of tags in each decompose-core region.
    let mut shapes: BTreeMap<Vec<u64>, usize> = BTreeMap::new();
    for r in rec.regions.iter().filter(|r| r.name == "decompose core") {
        let mut t = r.tags.clone();
        t.sort_unstable_by(|a, b| b.cmp(a));
        *shapes.entry(t).or_default() += 1;
    }
    let mut shapes: Vec<_> = shapes.into_iter().collect();
    shapes.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("\n  decompose-core row-tag shapes (count: tags per row):");
    for (s, n) in shapes.iter().take(12) {
        println!("    {n:>7}: {s:?}");
    }
}

fn main() {
    for cols in [4u8, 1] {
        measure(
            "bitcoin schnorr (secp256k1)",
            WithCols(btc::BitcoinSigExample, cols),
        );
        measure(
            "ethereum ecdsa (secp256k1)",
            WithCols(eth::EthereumSigExample, cols),
        );
    }
}
