//! The cost estimator takes high-level parameters for a circuit design, and
//! estimates the verification cost, as well as resulting proof size.

use std::{
    cell::RefCell,
    cmp::max,
    collections::{HashMap, HashSet},
    iter,
    num::ParseIntError,
    str::FromStr,
};

use ff::{Field, FromUniformBytes};
use serde::Deserialize;
use serde_derive::Serialize;

use super::Region;
use crate::{
    circuit::{self, Value},
    plonk::{
        Advice,
        Any::{self, Fixed},
        Assignment, Circuit, Column, ConstraintSystem, Error, FloorPlanner, Instance, Selector,
    },
    poly::{commitment::PolynomialCommitmentScheme, Coeff, Polynomial, PolynomialLabel},
    utils::{
        helpers::{ProcessedSerdeObject, SerdeFormat},
        rational::Rational,
    },
};

/// Options to build a circuit specification to measure the cost model of.
#[derive(Debug)]
pub(crate) struct CostOptions {
    /// An advice column with the given rotations. May be repeated.
    advice: Vec<Poly>,

    /// An instance column with the given rotations. May be repeated.
    instance: Vec<Poly>,

    /// How many of the instance columns are given in committed form.
    nb_committed_instances: usize,

    /// A fixed column with the given rotations. May be repeated.
    fixed: Vec<Poly>,

    /// Maximum degree of the constraint system.
    max_degree: usize,

    /// A lookup over N columns with max input degree I and max table degree T.
    /// May be repeated.
    lookup: Vec<Lookup>,

    /// A permutation over N columns. May be repeated.
    permutation: Permutation,

    /// Trash arguments (one per additive-selector gate).
    trash: Vec<Trash>,

    /// 2^K bound on the number of rows, accounting for ZK, PIs and Lookup
    /// tables.
    pub(crate) min_k: u32,

    /// Rows count, not including table rows and not accounting for compression
    /// (where multiple regions can use the same rows).
    rows_count: usize,

    /// Table rows count, not accounting for compression (where multiple regions
    /// can use the same rows), but not much if any compression can happen with
    /// table rows anyway.
    table_rows_count: usize,

    /// Number of rows that are devoted to blinding factors and cannot be used
    /// for "computing".
    nb_unusable_rows: usize,
}

/// Structure holding polynomial related data for benchmarks
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Poly {
    /// Rotations for the given polynomial
    rotations: Vec<isize>,
}

impl FromStr for Poly {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut rotations: Vec<isize> =
            s.split(',').map(|r| r.parse()).collect::<Result<_, _>>()?;
        rotations.sort_unstable();
        Ok(Poly { rotations })
    }
}

/// Structure holding the Lookup related data for circuit benchmarks.
///
/// Each lookup argument has shared multiplicity `m(X)` and accumulator `Z(X)`
/// polynomials, plus one helper polynomial `h_i(X)` per degree-bounded chunk.
#[derive(Debug, Clone)]
struct Lookup {
    num_chunks: usize,
}

impl Lookup {
    /// Returns the queries of the LogUp lookup argument.
    ///
    /// Per argument:
    ///  - 1 multiplicities polynomial at x,
    ///  - `num_chunks` helper polynomials at x,
    ///  - 1 accumulator polynomial at x and ωx.
    fn queries(&self) -> impl Iterator<Item = Poly> {
        let multiplicities: Poly = "0".parse().unwrap();
        let helper: Poly = "0".parse().unwrap();
        let aggregator: Poly = "0,1".parse().unwrap();

        iter::once(multiplicities)
            .chain(iter::repeat(helper).take(self.num_chunks))
            .chain(iter::once(aggregator))
    }

    /// Number of evaluations:
    /// 1 (multiplicities) + num_chunks (helpers) + 1 (Z at x) + 1 (Z at ωx).
    fn num_evaluations(&self) -> usize {
        self.num_chunks + 3
    }
}

/// Structure holding the Trash argument data for circuit benchmarks.
///
/// Each trash argument contributes 1 commitment and 1 evaluation.
#[derive(Debug, Clone)]
struct Trash;

/// Number of permutation enabled columns
#[derive(Debug, Clone, Deserialize, Serialize)]
struct Permutation {
    chunk_len: usize,
    columns: usize,
    /// Number of usable rows. See [here](https://zcash.github.io/halo2/design/proving-system/permutation.html#zero-knowledge-adjustment)
    u: isize,
}

impl Permutation {
    /// Returns the queries of the Permutation argument
    fn queries(&self) -> impl Iterator<Item = Poly> {
        // - at wX, X, uwX for all (except the last)
        // - at wX, X for the last
        let mut chunks: Poly = "0,1".parse().unwrap();
        chunks.rotations.push(self.u);

        let last_chunk: Poly = "0,1".parse().unwrap();

        iter::empty()
            .chain(iter::repeat(chunks).take((self.columns - 1) / self.chunk_len))
            .chain(Some(last_chunk))
    }
}

/// High-level specifications of an abstract circuit.
#[derive(Debug, Deserialize, Serialize)]
pub struct CircuitModel {
    /// Power-of-2 bound on the number of rows in the circuit.
    pub k: u32,
    /// Number of rows in the circuit (not including table rows).
    pub rows: usize,
    /// Number of table rows in the circuit.
    pub table_rows: usize,
    /// Number of rows that are devoted to blinding factors and cannot be used
    /// for "computing".
    pub nb_unusable_rows: usize,
    /// Maximum degree of the circuit.
    pub max_deg: usize,
    /// Number of advice columns.
    pub advice_columns: usize,
    /// Number of fixed columns. This includes selectors, tables (for lookups),
    /// and permutation commitments.
    pub fixed_columns: usize,
    /// Number of lookup arguments.
    pub lookups: usize,
    /// Number of trash arguments.
    pub trashcans: usize,
    /// Equality constraint enabled columns (fixed columns are counted in
    /// `fixed_columns` value).
    pub permutations: usize,
    /// Number of distinct column queries across all gates.
    pub column_queries: usize,
    /// Number of distinct sets of points in the multiopening argument.
    pub point_sets: usize,
    /// Size of the proof for the circuit
    pub size: usize,
}

/// Given a Plonk circuit, this function returns a [CircuitModel].
///
/// `commit` is a function mapping a number of polynomials `n` to the byte
/// length of a single commitment that covers all `n` of them.  This lets
/// callers supply a commitment-scheme-specific size without requiring a generic
/// `CS` type parameter here.
///
/// See [`circuit_model`] for the variant that derives `commit` automatically
/// from a `PolynomialCommitmentScheme`.
pub fn circuit_model_with<F: Ord + Field + FromUniformBytes<64>>(
    circuit: &impl Circuit<F>,
    nb_committed_instances: usize,
    commit: impl Fn(usize) -> usize,
) -> CircuitModel {
    let o = cost_model_options(circuit, nb_committed_instances);

    let scalar = (F::NUM_BITS as usize).div_ceil(8);

    let mut queries: Vec<_> = iter::empty()
        .chain(o.advice.iter())
        .chain(o.instance.iter().take(o.nb_committed_instances))
        .chain(o.fixed.iter())
        .cloned()
        .chain(o.lookup.iter().flat_map(|l| l.queries()))
        .chain(o.permutation.queries())
        .chain(iter::repeat("0".parse().unwrap()).take(o.trash.len()))
        .chain(iter::once("0".parse().unwrap())) // Linearization polynomial query at x
        .filter(|p| !p.rotations.is_empty())
        .collect();

    let column_queries = queries.len();
    queries.iter_mut().for_each(|p| p.rotations.sort());
    queries.sort_unstable();
    queries.dedup();
    let point_sets = queries.len();

    let commit1 = commit(1);

    // PLONK:
    // - 1 commitment for the entire advice batch
    // - SCALAR bytes per advice column per query
    // - SCALAR bytes per committed instance column per query
    // - SCALAR bytes per fixed column per query
    // - SCALAR bytes per permutation column
    // - One batched commit for all permutation accumulator chunks
    //   + 3 SCALAR per chunk (last chunk has 2 SCALAR)
    // - For logup: one batched commit for all multiplicities (cross-arg),
    //   one batched commit for all helpers (cross-arg + within-arg — each
    //   helper carries a unique `LogupHelper(name, chunk)` label),
    //   one batched commit for all aggregators (cross-arg);
    //   + (num_chunks + 3) SCALAR per arg.
    // - Per trash argument: commit1 + 1 SCALAR
    let nb_perm_chunks =
        (o.permutation.columns.saturating_sub(1) / o.max_degree.saturating_sub(2)) + 1;
    let nb_lookups = o.lookup.len();
    let total_helper_chunks: usize = o.lookup.iter().map(|l| l.num_chunks).sum();
    let plonk = commit(o.advice.len())
        + o.advice.iter().map(|p| p.rotations.len() * scalar).sum::<usize>()
        + o.instance
            .iter()
            .take(o.nb_committed_instances)
            .map(|p| p.rotations.len() * scalar)
            .sum::<usize>()
        + o.fixed.iter().map(|p| p.rotations.len() * scalar).sum::<usize>()
        + scalar * o.permutation.columns
        + commit(nb_perm_chunks)
        + (scalar * 3 * nb_perm_chunks).saturating_sub(scalar) // last chunk has 2 evals
        + commit(nb_lookups)                  // batched multiplicities
        + commit(total_helper_chunks)         // batched helpers (cross-arg + within-arg)
        + commit(nb_lookups)                  // batched aggregators
        + o.lookup.iter().map(|l| scalar * l.num_evaluations()).sum::<usize>()
        + (commit1 + scalar) * o.trash.len();

    // Commitments to quotient limbs: one commitment per limb.
    let limbs = commit1 * (o.max_degree - 1);

    // Multiopening argument:
    // - commit1 bytes for f_commitment
    // - scalar bytes per set of points
    // - commit1 bytes for proof
    let multiopen = commit1 * 2 + scalar * point_sets;

    CircuitModel {
        k: o.min_k,
        rows: o.rows_count,
        table_rows: o.table_rows_count,
        nb_unusable_rows: o.nb_unusable_rows,
        max_deg: o.max_degree,
        advice_columns: o.advice.len(),
        // Note that we have one fixed commitment per column in the permutation argument
        fixed_columns: o.fixed.len() + o.permutation.columns,
        lookups: o.lookup.len(),
        trashcans: o.trash.len(),
        permutations: o.permutation.columns,
        column_queries,
        point_sets,
        size: plonk + multiopen + limbs,
    }
}

/// Given a Plonk circuit, this function returns a [CircuitModel].
///
/// `CS` is the commitment scheme; commitment byte sizes and scalar field
/// element sizes are both derived from it — no size constants need to be
/// supplied.
pub fn circuit_model<F: Ord + Field + FromUniformBytes<64>, CS: PolynomialCommitmentScheme<F>>(
    circuit: &impl Circuit<F>,
    nb_committed_instances: usize,
) -> CircuitModel {
    let params = CS::gen_params(1);
    let zero_poly = Polynomial::<F, Coeff>::init(1);
    let commit = |n: usize| {
        if n == 0 {
            return 0;
        }
        let polys: Vec<&Polynomial<F, Coeff>> = vec![&zero_poly; n];
        let labels = vec![PolynomialLabel::NoLabel; n];
        CS::commit(&params, &polys, &labels).byte_length(SerdeFormat::Processed)
    };
    circuit_model_with(circuit, nb_committed_instances, commit)
}

/// Namespace marker that signals the start of the region to measure.
///
/// Place this marker in `synthesize` (via `layouter.namespace(||
/// COST_MEASURE_START)`) immediately before the operation whose cost you want
/// to isolate.  Pair it with [`COST_MEASURE_END`].  When both markers are
/// present, `cost_model_options` reports `rows` as the span of the rows
/// assigned between the two markers rather than the full circuit row count.
pub const COST_MEASURE_START: &str = "__cost_model_measure_start__";

/// Namespace marker that signals the end of the region to measure.
///
/// See [`COST_MEASURE_START`].
pub const COST_MEASURE_END: &str = "__cost_model_measure_end__";

/// Given a circuit, this function returns [CostOptions]. If no upper bound for
/// `k` is provided, we iterate until a valid `k` is found (this might delay the
/// computation).
pub(crate) fn cost_model_options<F: Ord + Field + FromUniformBytes<64>, C: Circuit<F>>(
    circuit: &C,
    nb_committed_instances: usize,
) -> CostOptions {
    let prover = DevAssembly::run(circuit).unwrap();

    let cs = prover.cs;

    let fixed = {
        // init the fixed polynomials with no rotations
        let mut fixed = vec![Poly { rotations: vec![] }; cs.num_fixed_columns()];
        for (col, rot) in cs.fixed_queries() {
            if !cs.has_simple_selector_col(col.index()) {
                fixed[col.index()].rotations.push(rot.0 as isize);
            }
        }
        fixed
    };

    let advice = {
        // init the advice polynomials with at least X as a rotation (always opens at
        // least once)
        let mut advice = vec![Poly { rotations: vec![] }; cs.num_advice_columns()];
        for (col, rot) in cs.advice_queries() {
            advice[col.index()].rotations.push(rot.0 as isize);
            advice[col.index()].rotations.sort()
        }
        advice
    };

    let instance = {
        // init the instance polynomials with no rotations
        let mut instance = vec![Poly { rotations: vec![] }; cs.num_instance_columns()];
        for (col, rot) in cs.instance_queries() {
            instance[col.index()].rotations.push(rot.0 as isize);
            instance[col.index()].rotations.sort()
        }
        instance
    };

    let lookup = {
        cs.lookups()
            .iter()
            .map(|l| Lookup {
                num_chunks: l.num_chunks(cs.degree()),
            })
            .collect::<Vec<_>>()
    };

    let trash: Vec<Trash> = cs.trashcans().iter().map(|_| Trash).collect();

    let permutation = Permutation {
        chunk_len: cs.degree() - 2,
        columns: cs.permutation().get_columns().len(),
        u: -((cs.blinding_factors() + 1) as isize),
    };

    // Note that this computation does't assume that `regions` is already in
    // order of increasing row indices.
    let (table_rows_count, rows_count) = {
        let mut rows_count = 0usize;
        let mut table_rows_count = 0usize;

        // When the circuit uses COST_MEASURE_START / COST_MEASURE_END markers,
        // report only the row span covered by the marked regions. Table rows
        // are always counted in full (they are a global cost).
        let mut min_measured_row = usize::MAX;
        let mut max_measured_row = 0usize;
        let mut has_any_measured = false;

        for region in &prover.regions {
            if let Some((start, end)) = region.rows {
                // A region is a _table region_ if all of its columns are `Fixed`
                // columns (see that [`plonk::circuit::TableColumn` is a wrapper
                // around `Column<Fixed>`]). All of a table region's rows are
                // counted towards `table_rows_count.`
                if region.columns.iter().all(|c| *c.column_type() == Fixed) {
                    table_rows_count = std::cmp::max(table_rows_count, end + 1);
                } else if prover.has_measured_regions {
                    if region.is_measured {
                        min_measured_row = std::cmp::min(min_measured_row, start);
                        max_measured_row = std::cmp::max(max_measured_row, end);
                        has_any_measured = true;
                    }
                } else {
                    // Note that `end` is the index of the last row, so when
                    // counting rows this last row needs to be counted via `end + 1`.
                    rows_count = std::cmp::max(rows_count, end + 1);
                }
            }
        }

        if has_any_measured {
            rows_count = max_measured_row - min_measured_row + 1;
        }

        (table_rows_count, rows_count)
    };

    let nb_unusable_rows = cs.blinding_factors() + 1;

    let nb_instances = prover.instance_rows.take();
    let min_circuit_size = [
        rows_count + nb_unusable_rows,
        table_rows_count + nb_unusable_rows,
        nb_instances + nb_unusable_rows,
        cs.minimum_rows() + 1,
    ]
    .into_iter()
    .max()
    .unwrap();

    if min_circuit_size == nb_instances {
        println!("WARNING: The dominant factor in your circuit's size is the number of public inputs, which causes the verifier to perform linear work.");
    }

    CostOptions {
        advice,
        instance,
        nb_committed_instances,
        fixed,
        max_degree: cs.degree(),
        lookup,
        permutation,
        trash,
        min_k: min_circuit_size.next_power_of_two().ilog2(),
        rows_count,
        table_rows_count,
        nb_unusable_rows,
    }
}

// DevAssembly is only used to compute the cost model, meaning that we only care
// about the number of assignments and not the assignments themselves.
// Therefore, we only keep track of the number of rows, the regions and ignore
// we values of the trace.
struct DevAssembly<F: Field> {
    cs: ConstraintSystem<F>,
    instance_rows: RefCell<usize>,
    /// The regions in the circuit.
    regions: Vec<Region>,
    current_region: Option<Region>,
    /// Set to `true` while the synthesizer is between a
    /// [`COST_MEASURE_START`] and a [`COST_MEASURE_END`] namespace marker.
    in_measured_region: bool,
    /// Set to `true` once a [`COST_MEASURE_START`] marker has been seen.
    /// Used to switch [`cost_model_options`] into "measured-only" mode.
    has_measured_regions: bool,
}

impl<F: FromUniformBytes<64> + Ord> DevAssembly<F> {
    /// Runs a synthetic keygen-and-prove operation on the given circuit,
    /// collecting data about the constraints and their assignments.
    pub fn run<ConcreteCircuit: Circuit<F>>(circuit: &ConcreteCircuit) -> Result<Self, Error> {
        let mut cs = ConstraintSystem::default();
        #[cfg(feature = "circuit-params")]
        let config = ConcreteCircuit::configure_with_params(&mut cs, circuit.params());
        #[cfg(not(feature = "circuit-params"))]
        let config = ConcreteCircuit::configure(&mut cs);
        let cs = cs;
        let constants = cs.constants.clone();

        let mut prover = DevAssembly {
            cs,
            instance_rows: RefCell::new(0),
            regions: vec![],
            current_region: None,
            in_measured_region: false,
            has_measured_regions: false,
        };

        ConcreteCircuit::FloorPlanner::synthesize(
            &mut prover,
            circuit,
            config.clone(),
            constants.clone(),
        )?;

        let selectors = vec![vec![]; prover.cs.num_selectors];
        let (cs, _selector_polys) = prover.cs.directly_convert_selectors_to_fixed(selectors);
        prover.cs = cs;

        Ok(prover)
    }
}

impl<F: Field> Assignment<F> for DevAssembly<F> {
    fn enter_region<NR, N>(&mut self, name: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        assert!(self.current_region.is_none());
        self.current_region = Some(Region {
            name: name().into(),
            columns: HashSet::default(),
            rows: None,
            annotations: HashMap::default(),
            enabled_selectors: HashMap::default(),
            cells: HashMap::default(),
            is_measured: self.in_measured_region,
        });
    }

    fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing
    }

    fn exit_region(&mut self) {
        self.regions.push(self.current_region.take().unwrap());
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Track that this selector was enabled. We require that all selectors are
        // enabled inside some region (i.e. no floating selectors).
        self.current_region
            .as_mut()
            .unwrap()
            .enabled_selectors
            .entry(*selector)
            .or_default()
            .push(row);

        Ok(())
    }

    fn query_instance(&self, _column: Column<Instance>, _row: usize) -> Result<Value<F>, Error> {
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        _to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> circuit::Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if let Some(region) = self.current_region.as_mut() {
            region.update_extent(column.into(), row);
            region
                .cells
                .entry((column.into(), row))
                .and_modify(|count| *count += 1)
                .or_default();
        }

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<crate::plonk::Fixed>,
        row: usize,
        _to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> circuit::Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if let Some(region) = self.current_region.as_mut() {
            region.update_extent(column.into(), row);
            region
                .cells
                .entry((column.into(), row))
                .and_modify(|count| *count += 1)
                .or_default();
        }

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), crate::plonk::Error> {
        if let Any::Instance = left_column.column_type() {
            *self.instance_rows.borrow_mut() = max(left_row + 1, self.instance_rows.take());
        }

        if let Any::Instance = right_column.column_type() {
            *self.instance_rows.borrow_mut() = max(right_row + 1, self.instance_rows.take());
        }

        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _col: Column<crate::plonk::Fixed>,
        _from_row: usize,
        _to: circuit::Value<Rational<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let name: String = name_fn().into();
        if name == COST_MEASURE_START {
            self.in_measured_region = true;
            self.has_measured_regions = true;
        } else if name == COST_MEASURE_END {
            self.in_measured_region = false;
        }
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

/// This function makes a dummy pass on the synthesize function associated to
/// the given circuit. This could be useful for checking that the circuit is
/// well-formed.
pub fn dummy_synthesize_run<F, C>(circuit: &C) -> Result<(), Error>
where
    F: Ord + Field + FromUniformBytes<64>,
    C: Circuit<F>,
{
    DevAssembly::run(circuit).map(|_| ())
}

#[cfg(test)]
mod tests {
    use blake2b_simd::State;
    use midnight_curves::{Bls12, Fq};
    use rand_core::{OsRng, RngCore};

    use super::*;
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{
            create_proof, keygen_pk, keygen_vk_with_k, Constraints, Expression, Fixed, TableColumn,
        },
        poly::{kzg::params::ParamsKZG, Rotation},
        transcript::{CircuitTranscript, Transcript},
        MidnightPCS,
    };

    #[derive(Clone, Copy)]
    struct StandardPlonkConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        q_a: Column<Fixed>,
        q_b: Column<Fixed>,
        q_c: Column<Fixed>,
        q_ab: Column<Fixed>,
        constant: Column<Fixed>,
        #[allow(dead_code)]
        instance: Column<Instance>,
        table_selector: Selector,
        table: TableColumn,
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<Fq>) -> Self {
            let [a, b, c] = std::array::from_fn(|_| meta.advice_column());
            let [q_a, q_b, q_c, q_ab, constant] = std::array::from_fn(|_| meta.fixed_column());
            let instance = meta.instance_column();
            meta.enable_equality(instance);

            [a, b, c].iter().for_each(|column| meta.enable_equality(*column));

            let table_selector = meta.complex_selector();
            let sl = meta.lookup_table_column();

            meta.lookup("lookup", None, |meta| {
                let selector = meta.query_selector(table_selector);
                let not_selector = Expression::from(1) - selector.clone();
                let advice = meta.query_advice(a, Rotation::cur());
                vec![(selector * advice + not_selector, sl)]
            });

            meta.create_gate(
                "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
                |meta| {
                    let [a, b, c] =
                        [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let instance = meta.query_instance(instance, Rotation::cur());
                    Constraints::without_selector(vec![
                        q_a * &a + q_b * &b + q_c * c + q_ab * a * b + constant + instance,
                    ])
                },
            );

            StandardPlonkConfig {
                a,
                b,
                c,
                q_a,
                q_b,
                q_c,
                q_ab,
                constant,
                instance,
                table_selector,
                table: sl,
            }
        }
    }

    #[derive(Clone, Default)]
    struct StandardPlonk<const NB_PUBLIC_INPUTS: usize>(Fq);

    impl<const NB_PUBLIC_INPUTS: usize> Circuit<Fq> for StandardPlonk<NB_PUBLIC_INPUTS> {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fq>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "8-bit table",
                |mut table| {
                    for row in 0u64..(1 << 8) {
                        table.assign_cell(
                            || format!("row {row}"),
                            config.table,
                            row as usize,
                            || Value::known(Fq::from(row + 1)),
                        )?;
                    }

                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "",
                |mut region| {
                    config.table_selector.enable(&mut region, 0)?;
                    region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                    region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fq::ONE))?;

                    region.assign_advice(|| "", config.a, 1, || Value::known(-Fq::from(5u64)))?;
                    for (idx, column) in (1..).zip([
                        config.q_a,
                        config.q_b,
                        config.q_c,
                        config.q_ab,
                        config.constant,
                    ]) {
                        region.assign_fixed(
                            || "",
                            column,
                            1,
                            || Value::known(Fq::from(idx as u64)),
                        )?;
                    }

                    let a = region.assign_advice(|| "", config.a, 2, || Value::known(Fq::ONE))?;
                    a.copy_advice(|| "", &mut region, config.b, 3)?;
                    a.copy_advice(|| "", &mut region, config.c, 4)?;
                    region.assign_advice(|| "", config.a, 5, || Value::known(Fq::ZERO))?;

                    // Assign instances. We are just forcing the number of instances to be
                    // determined by the variable `NB_PUBLIC_INPUTS`.
                    for i in 0..NB_PUBLIC_INPUTS {
                        let _ = region.assign_advice_from_instance(
                            || "",
                            config.instance,
                            i,
                            config.a,
                            0,
                        )?;
                    }
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn cost_model() {
        let k = 9;
        let mut random_byte = [0u8; 1];
        OsRng::fill_bytes(&mut OsRng, &mut random_byte);
        let circuit = StandardPlonk::<1>(Fq::from(random_byte[0] as u64));

        let params = ParamsKZG::<Bls12>::unsafe_setup(k, OsRng);
        let vk = keygen_vk_with_k::<_, MidnightPCS, _>(&params, &circuit, k)
            .expect("vk should not fail");
        let pk = keygen_pk(vk, &circuit).expect("pk should not fail");

        let instances: &[&[Fq]] = &[&[circuit.0]];
        let mut transcript = CircuitTranscript::<State>::init();

        create_proof::<Fq, MidnightPCS, _, _>(
            &params,
            &pk,
            &circuit,
            #[cfg(feature = "committed-instances")]
            0,
            instances,
            &mut transcript,
            OsRng,
        )
        .expect("proof generation should not fail");

        let proof = transcript.finalize();

        assert_eq!(
            circuit_model::<_, MidnightPCS>(&circuit, 0).size,
            proof.len()
        );
    }

    #[cfg(feature = "committed-instances")]
    #[test]
    fn cost_model_with_committed_instances() {
        let k = 9;
        let mut random_byte = [0u8; 1];
        OsRng::fill_bytes(&mut OsRng, &mut random_byte);
        let circuit = StandardPlonk::<1>(Fq::from(random_byte[0] as u64));

        let params = ParamsKZG::<Bls12>::unsafe_setup(k, OsRng);
        let vk = keygen_vk_with_k::<_, MidnightPCS, _>(&params, &circuit, k)
            .expect("vk should not fail");
        let pk = keygen_pk(vk, &circuit).expect("pk should not fail");

        let instances: &[&[Fq]] = &[&[circuit.0]];
        let mut transcript = CircuitTranscript::<State>::init();

        create_proof::<Fq, MidnightPCS, _, _>(
            &params,
            &pk,
            &circuit,
            1,
            instances,
            &mut transcript,
            OsRng,
        )
        .expect("proof generation should not fail");

        let proof = transcript.finalize();

        assert_eq!(
            circuit_model::<_, MidnightPCS>(&circuit, 1).size,
            proof.len()
        );
    }

    #[test]
    fn check_correct_computation_k() {
        let mut random_byte = [0u8; 1];
        OsRng::fill_bytes(&mut OsRng, &mut random_byte);

        macro_rules! test_nb_pi {
            ($($nb_pi:expr),*) => {
                $(
                    {
                        const NB_PI: usize = $nb_pi;
                        let circuit = StandardPlonk::<NB_PI>(Fq::from(random_byte[0] as u64));
                        let cost_model = cost_model_options(&circuit, 0);

                        // nb of unusable rows for this circuit is 8.
                        let pi_k = (NB_PI + 8).next_power_of_two().ilog2();
                        assert_eq!(cost_model.min_k, max(9, pi_k));
                    }
                )*
            };
        }

        test_nb_pi!(1, 10, 100, 1017, 1018, 1019, 1020);
    }
}
