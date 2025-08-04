//! The cost estimator takes high-level parameters for a circuit design, and
//! estimates the verification cost, as well as resulting proof size.

use std::{
    collections::{HashMap, HashSet},
    iter,
    num::ParseIntError,
    ops::Range,
    str::FromStr,
};

use blake2b_simd::blake2b;
use ff::{Field, FromUniformBytes};
use serde::Deserialize;
use serde_derive::Serialize;

use super::{CellValue, Region};
use crate::{
    circuit,
    circuit::Value,
    plonk::{
        k_from_circuit, permutation, sealed, sealed::SealedPhase, Advice, Any, Any::Fixed,
        Assignment, Challenge, Circuit, Column, ConstraintSystem, Error, FirstPhase, FloorPlanner,
        Instance, Phase, Selector,
    },
    utils::rational::Rational,
};

/// Options to build a circuit specification to measure the cost model of.
#[derive(Debug)]
struct CostOptions {
    /// An advice column with the given rotations. May be repeated.
    advice: Vec<Poly>,

    /// An instance column with the given rotations. May be repeated.
    instance: Vec<Poly>,

    /// A fixed column with the given rotations. May be repeated.
    fixed: Vec<Poly>,

    /// Maximum degree of the constraint system.
    max_degree: usize,

    /// A lookup over N columns with max input degree I and max table degree T.
    /// May be repeated.
    lookup: Vec<Lookup>,

    /// A permutation over N columns. May be repeated.
    permutation: Permutation,

    /// 2^K bound on the number of rows, accounting for ZK, PIs and Lookup
    /// tables.
    min_k: usize,

    /// Rows count, not including table rows and not accounting for compression
    /// (where multiple regions can use the same rows).
    rows_count: usize,

    /// Table rows count, not accounting for compression (where multiple regions
    /// can use the same rows), but not much if any compression can happen with
    /// table rows anyway.
    table_rows_count: usize,

    /// Compressed rows count, accounting for compression (where multiple
    /// regions can use the same rows).
    compressed_rows_count: usize,
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
#[derive(Debug, Clone)]
struct Lookup;

impl Lookup {
    /// Returns the queries of the lookup argument
    fn queries(&self) -> impl Iterator<Item = Poly> {
        // - product commitments at x and \omega x
        // - input commitments at x and x_inv
        // - table commitments at x
        let product = "0,1".parse().unwrap();
        let input = "-1,0".parse().unwrap();
        let table = "0".parse().unwrap();

        iter::empty()
            .chain(Some(product))
            .chain(Some(input))
            .chain(Some(table))
    }
}

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
    pub k: usize,
    /// Number of rows in the circuit (not including table rows).
    pub rows: usize,
    /// Number of table rows in the circuit.
    pub table_rows: usize,
    /// Maximum degree of the circuit.
    pub max_deg: usize,
    /// Number of advice columns.
    pub advice_columns: usize,
    /// Number of fixed columns. This includes selectors, tables (for lookups),
    /// and permutation commitments.
    pub fixed_columns: usize,
    /// Number of advice columns used in the lookup argument.
    pub lookups: usize,
    /// Equality constraint enabled columns (fixed columns are counted in
    /// `fixed_columns` value).
    pub permutations: usize,
    /// Number of distinct column queries across all gates.
    pub column_queries: usize,
    /// Number of distinct sets of points in the multiopening argument.
    pub point_sets: usize,
    /// Size of the proof for the circuit
    pub size: usize,
    /// Compressed rows count, accounting for compression (where multiple
    /// regions can use the same rows).
    pub compressed_rows_count: usize,
}

impl CostOptions {
    /// Convert [CostOptions] to [CircuitModel]. The proof sizè is computed
    /// depending on the base and scalar field size of the curve used.
    fn into_circuit_model<const COMM: usize, const SCALAR: usize>(self) -> CircuitModel {
        let mut queries: Vec<_> = iter::empty()
            .chain(self.advice.iter())
            .chain(self.instance.iter())
            .chain(self.fixed.iter())
            .cloned()
            .chain(self.lookup.iter().flat_map(|l| l.queries()))
            .chain(self.permutation.queries())
            .chain(iter::repeat("0".parse().unwrap()).take(self.max_degree - 1))
            .collect();

        let column_queries = queries.len();
        queries.sort_unstable();
        queries.dedup();
        let point_sets = queries.len();

        let comp_bytes = |points: usize, scalars: usize| points * COMM + scalars * SCALAR;

        // PLONK:
        // - COMM bytes (commitment) per advice column
        // - 3 * COMM bytes per lookup
        // - COMM bytes per ((self.permutation.columns - 1) / (self.max_degree - 2)) + 1
        // - 3 * SCALAR bytes per ((self.permutation.columns - 1) / (self.max_degree -
        //   2)) + 1
        // - SCALAR bytes per advice per query
        // - SCALAR bytes per fixed per query <- missing
        // - SCALAR bytes per permutation column
        // - 5 * SCALAR bytes per lookup argument
        let nb_perm_chunks =
            (self.permutation.columns.saturating_sub(1) / self.max_degree.saturating_sub(2)) + 1;
        let plonk = comp_bytes(1, 0) * self.advice.len()
            + self
                .advice
                .iter()
                .map(|polys| comp_bytes(0, polys.rotations.len()))
                .sum::<usize>()
            + self
                .fixed
                .iter()
                .map(|polys| comp_bytes(0, polys.rotations.len()))
                .sum::<usize>()
            + comp_bytes(3, 5) * self.lookup.len()
            + (comp_bytes(1, 3) * nb_perm_chunks).saturating_sub(comp_bytes(0, 1)) // we don't need the permutation_product_last_eval of the last chunk
            + comp_bytes(0, 1) * self.permutation.columns;

        // Vanishing argument:
        // - COMM bytes for random poly
        // - (max_deg - 1) COMM bytes for the pieces
        // - SCALAR bytes for random piece eval
        let vanishing = comp_bytes(self.max_degree, 1);

        // Multiopening argument:
        // - COMM bytes for f_commitment
        // - SCALAR bytes per set of points in multiopen argument
        // - COMM bytes for proof
        let multiopen = comp_bytes(2, point_sets);

        let mut nr_rotations = HashSet::new();
        for poly in self.advice.iter() {
            nr_rotations.extend(poly.rotations.clone());
        }
        for poly in self.fixed.iter() {
            nr_rotations.extend(poly.rotations.clone());
        }
        for poly in self.instance.iter() {
            nr_rotations.extend(poly.rotations.clone());
        }

        let size = plonk + vanishing + multiopen;

        CircuitModel {
            k: self.min_k,
            rows: self.rows_count,
            table_rows: self.table_rows_count,
            max_deg: self.max_degree,
            advice_columns: self.advice.len(),
            // Note that we have one fixed commitment per column in the permutation argument
            fixed_columns: self.fixed.len() + self.permutation.columns,
            lookups: self.lookup.len(),
            permutations: self.permutation.columns,
            column_queries,
            point_sets,
            size,
            compressed_rows_count: self.compressed_rows_count,
        }
    }
}

/// Given a Plonk circuit, this function returns a [CircuitModel]
pub fn from_circuit_to_circuit_model<
    F: Ord + Field + FromUniformBytes<64>,
    C: Circuit<F>,
    const COMM: usize,
    const SCALAR: usize,
>(
    k: Option<u32>,
    circuit: &C,
    nb_instances: usize,
) -> CircuitModel {
    let options = from_circuit_to_cost_model_options(k, circuit, nb_instances);
    options.into_circuit_model::<COMM, SCALAR>()
}

/// Given a circuit, this function returns [CostOptions]. If no upper bound for
/// `k` is provided, we iterate until a valid `k` is found (this might delay the
/// computation).
fn from_circuit_to_cost_model_options<F: Ord + Field + FromUniformBytes<64>, C: Circuit<F>>(
    k_upper_bound: Option<u32>,
    circuit: &C,
    nb_instances: usize,
) -> CostOptions {
    let prover = if let Some(k) = k_upper_bound {
        DevAssembly::run(k, circuit).unwrap()
    } else {
        let k = k_from_circuit(circuit);
        DevAssembly::run(k, circuit).unwrap()
    };

    let cs = prover.cs;

    let fixed = {
        // init the fixed polynomials with no rotations
        let mut fixed = vec![Poly { rotations: vec![] }; cs.num_fixed_columns()];
        for (col, rot) in cs.fixed_queries() {
            fixed[col.index()].rotations.push(rot.0 as isize);
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

    let lookup = { cs.lookups().iter().map(|_| Lookup).collect::<Vec<_>>() };

    let permutation = Permutation {
        chunk_len: cs.degree() - 2,
        columns: cs.permutation().get_columns().len(),
        u: -((cs.blinding_factors() + 1) as isize),
    };

    // Note that this computation does't assume that `regions` is already in
    // order of increasing row indices.
    let (rows_count, table_rows_count, compressed_rows_count) = {
        let mut rows_count = 0;
        let mut table_rows_count = 0;
        let mut compressed_rows_count = 0;
        for region in prover.regions {
            // If `region.rows == None`, then that region has no rows.
            if let Some((start, end)) = region.rows {
                // Note that `end` is the index of the last column, so when
                // counting rows this last column needs to be counted via `end +
                // 1`.

                // A region is a _table region_ if all of its columns are `Fixed`
                // columns (see that [`plonk::circuit::TableColumn` is a wrapper
                // around `Column<Fixed>`]). All of a table region's rows are
                // counted towards `table_rows_count.`
                if region.columns.iter().all(|c| *c.column_type() == Fixed) {
                    table_rows_count += (end + 1) - start;
                } else {
                    rows_count += (end + 1) - start;
                }
                compressed_rows_count = std::cmp::max(compressed_rows_count, end + 1);
            }
        }
        (rows_count, table_rows_count, compressed_rows_count)
    };

    let min_k = [
        rows_count + cs.blinding_factors(),
        table_rows_count + cs.blinding_factors(),
        nb_instances,
    ]
    .into_iter()
    .max()
    .unwrap();
    if min_k == nb_instances {
        println!("WARNING: The dominant factor in your circuit's size is the number of public inputs, which causes the verifier to perform linear work.");
    }

    CostOptions {
        advice,
        instance,
        fixed,
        max_degree: cs.degree(),
        lookup,
        permutation,
        min_k: (min_k - 1).next_power_of_two().ilog2() as usize,
        rows_count,
        table_rows_count,
        compressed_rows_count,
    }
}

struct DevAssembly<F: Field> {
    k: u32,
    cs: ConstraintSystem<F>,

    /// The regions in the circuit.
    regions: Vec<Region>,
    /// The current region being assigned to. Will be `None` after the circuit
    /// has been synthesized.
    current_region: Option<Region>,

    // The fixed cells in the circuit, arranged as [column][row].
    fixed: Vec<Vec<CellValue<F>>>,
    // The advice cells in the circuit, arranged as [column][row].
    _advice: Vec<Vec<CellValue<F>>>,

    selectors: Vec<Vec<bool>>,

    _challenges: Vec<F>,

    permutation: permutation::keygen::Assembly,

    // A range of available rows for assignment and copies.
    usable_rows: Range<usize>,

    current_phase: sealed::Phase,
}

impl<F: FromUniformBytes<64> + Ord> DevAssembly<F> {
    /// Runs a synthetic keygen-and-prove operation on the given circuit,
    /// collecting data about the constraints and their assignments.
    pub fn run<ConcreteCircuit: Circuit<F>>(
        k: u32,
        circuit: &ConcreteCircuit,
    ) -> Result<Self, Error> {
        let n = 1 << k;

        let mut cs = ConstraintSystem::default();
        #[cfg(feature = "circuit-params")]
        let config = ConcreteCircuit::configure_with_params(&mut cs, circuit.params());
        #[cfg(not(feature = "circuit-params"))]
        let config = ConcreteCircuit::configure(&mut cs);
        let cs = cs;

        assert!(
            n >= cs.minimum_rows(),
            "n={}, minimum_rows={}, k={}",
            n,
            cs.minimum_rows(),
            k,
        );

        // Fixed columns contain no blinding factors.
        let fixed = vec![vec![CellValue::Unassigned; n]; cs.num_fixed_columns];
        let selectors = vec![vec![false; n]; cs.num_selectors];
        // Advice columns contain blinding factors.
        let blinding_factors = cs.blinding_factors();
        let usable_rows = n - (blinding_factors + 1);
        let _advice = vec![
            {
                let mut column = vec![CellValue::Unassigned; n];
                // Poison unusable rows.
                for (i, cell) in column.iter_mut().enumerate().skip(usable_rows) {
                    *cell = CellValue::Poison(i);
                }
                column
            };
            cs.num_advice_columns
        ];
        let permutation = permutation::keygen::Assembly::new(n, &cs.permutation);
        let constants = cs.constants.clone();

        // Use hash chain to derive deterministic challenges for testing
        let _challenges = {
            let mut hash: [u8; 64] = blake2b(b"CostModel").as_bytes().try_into().unwrap();
            iter::repeat_with(|| {
                hash = blake2b(&hash).as_bytes().try_into().unwrap();
                F::from_uniform_bytes(&hash)
            })
            .take(cs.num_challenges)
            .collect()
        };

        let mut prover = DevAssembly {
            k,
            cs,
            regions: vec![],
            current_region: None,
            fixed,
            _advice,
            selectors,
            _challenges,
            permutation,
            usable_rows: 0..usable_rows,
            current_phase: FirstPhase.to_sealed(),
        };

        for current_phase in prover.cs.phases() {
            prover.current_phase = current_phase;
            ConcreteCircuit::FloorPlanner::synthesize(
                &mut prover,
                circuit,
                config.clone(),
                constants.clone(),
            )?;
        }

        let (cs, selector_polys) = prover
            .cs
            .directly_convert_selectors_to_fixed(prover.selectors.clone());
        prover.cs = cs;
        prover.fixed.extend(selector_polys.into_iter().map(|poly| {
            let mut v = vec![CellValue::Unassigned; n];
            for (v, p) in v.iter_mut().zip(&poly[..]) {
                *v = CellValue::Assigned(*p);
            }
            v
        }));

        Ok(prover)
    }
}

impl<F: Field> DevAssembly<F> {
    fn in_phase<P: Phase>(&self, phase: P) -> bool {
        self.current_phase == phase.to_sealed()
    }
}

impl<F: Field> Assignment<F> for DevAssembly<F> {
    fn enter_region<NR, N>(&mut self, name: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        if !self.in_phase(FirstPhase) {
            return;
        }

        assert!(self.current_region.is_none());
        self.current_region = Some(Region {
            name: name().into(),
            columns: HashSet::default(),
            rows: None,
            annotations: HashMap::default(),
            enabled_selectors: HashMap::default(),
            cells: HashMap::default(),
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
        if !self.in_phase(FirstPhase) {
            return;
        }

        self.regions.push(self.current_region.take().unwrap());
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // Track that this selector was enabled. We require that all selectors are
        // enabled inside some region (i.e. no floating selectors).
        self.current_region
            .as_mut()
            .unwrap()
            .enabled_selectors
            .entry(*selector)
            .or_default()
            .push(row);

        self.selectors[selector.0][row] = true;

        Ok(())
    }

    fn query_instance(&self, _column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // There is no instance in this context.
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
        if self.in_phase(FirstPhase) {
            assert!(
                self.usable_rows.contains(&row),
                "row={}, usable_rows={:?}, k={}",
                row,
                self.usable_rows,
                self.k,
            );

            if let Some(region) = self.current_region.as_mut() {
                region.update_extent(column.into(), row);
                region
                    .cells
                    .entry((column.into(), row))
                    .and_modify(|count| *count += 1)
                    .or_default();
            }
        }

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<crate::plonk::Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> circuit::Value<VR>,
        VR: Into<Rational<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.in_phase(FirstPhase) {
            return Ok(());
        }

        assert!(
            self.usable_rows.contains(&row),
            "row={}, usable_rows={:?}, k={}",
            row,
            self.usable_rows,
            self.k,
        );

        if let Some(region) = self.current_region.as_mut() {
            region.update_extent(column.into(), row);
            region
                .cells
                .entry((column.into(), row))
                .and_modify(|count| *count += 1)
                .or_default();
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .expect("bounds failure") = CellValue::Assigned(to().into_field().evaluate().assign()?);

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), crate::plonk::Error> {
        if !self.in_phase(FirstPhase) {
            return Ok(());
        }

        assert!(
            self.usable_rows.contains(&left_row) && self.usable_rows.contains(&right_row),
            "left_row={}, right_row={}, usable_rows={:?}, k={}",
            left_row,
            right_row,
            self.usable_rows,
            self.k,
        );

        self.permutation
            .copy(left_column, left_row, right_column, right_row)
    }

    fn fill_from_row(
        &mut self,
        col: Column<crate::plonk::Fixed>,
        from_row: usize,
        to: circuit::Value<Rational<F>>,
    ) -> Result<(), Error> {
        if !self.in_phase(FirstPhase) {
            return Ok(());
        }

        assert!(
            self.usable_rows.contains(&from_row),
            "row={}, usable_rows={:?}, k={}",
            from_row,
            self.usable_rows,
            self.k,
        );

        for row in self.usable_rows.clone().skip(from_row) {
            self.assign_fixed(|| "", col, row, || to)?;
        }

        Ok(())
    }

    fn get_challenge(&self, _challenge: Challenge) -> circuit::Value<F> {
        Value::unknown()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
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
        poly::{
            kzg::{params::ParamsKZG, KZGCommitmentScheme},
            Rotation,
        },
        transcript::{CircuitTranscript, Transcript},
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

            [a, b, c].map(|column| meta.enable_equality(column));

            let table_selector = meta.complex_selector();
            let sl = meta.lookup_table_column();

            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(table_selector);
                let not_selector = Expression::Constant(Fq::ONE) - selector.clone();
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
                        q_a * a.clone()
                            + q_b * b.clone()
                            + q_c * c
                            + q_ab * a * b
                            + constant
                            + instance,
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
    struct StandardPlonk(Fq);

    impl Circuit<Fq> for StandardPlonk {
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
        let circuit = StandardPlonk(Fq::from(random_byte[0] as u64));

        let params = ParamsKZG::<Bls12>::unsafe_setup(k, OsRng);
        let vk = keygen_vk_with_k::<_, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, k)
            .expect("vk should not fail");
        let pk = keygen_pk(vk, &circuit).expect("pk should not fail");

        let instances: &[&[Fq]] = &[&[circuit.0]];
        let mut transcript = CircuitTranscript::<State>::init();

        create_proof::<Fq, KZGCommitmentScheme<Bls12>, _, _>(
            &params,
            &pk,
            &[circuit.clone()],
            #[cfg(feature = "committed-instances")]
            0,
            &[instances],
            OsRng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        let circuit_model =
            from_circuit_to_circuit_model::<_, _, 48, 32>(Some(k), &circuit, instances[0].len());

        let proof = transcript.finalize();

        assert_eq!(circuit_model.size, proof.len());
    }
}
