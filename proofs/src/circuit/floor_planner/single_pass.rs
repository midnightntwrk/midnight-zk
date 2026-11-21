use std::{cmp, collections::HashMap, fmt, marker::PhantomData};

use ff::Field;

#[cfg(feature = "prover-par")]
use crate::circuit::layouter::{MeasuredLayout, MeasuredRegion};
use crate::{
    circuit::{
        Cell, Layouter, Region, RegionIndex, RegionStart, Table, Value,
        layouter::{RegionColumn, RegionLayouter, RegionShape, SyncDeps, TableLayouter},
        table_layouter::{SimpleTableLayouter, compute_table_lengths},
    },
    plonk::{
        Advice, Any, Assignment, Circuit, Column, Error, Fixed, FloorPlanner, Instance, Selector,
        TableColumn,
    },
    utils::rational::Rational,
};

/// A simple [`FloorPlanner`] that performs minimal optimizations.
///
/// This floor planner is suitable for debugging circuits. It aims to reflect
/// the circuit "business logic" in the circuit layout as closely as possible.
/// It uses a single-pass layouter that does not reorder regions for optimal
/// packing.
#[derive(Debug)]
pub struct SimpleFloorPlanner;

impl FloorPlanner for SimpleFloorPlanner {
    fn synthesize<F: Field, CS: Assignment<F> + SyncDeps, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
    ) -> Result<(), Error> {
        let layouter = SingleChipLayouter::new(cs, constants)?;
        circuit.synthesize(config, layouter)
    }

    fn synthesize_capturing_regions<F: Field, CS: Assignment<F> + SyncDeps, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
    ) -> Result<Option<Vec<RegionStart>>, Error> {
        let mut sink = Vec::new();
        let layouter = SingleChipLayouter::new_capturing(cs, constants, &mut sink)?;
        circuit.synthesize(config, layouter)?;
        Ok(Some(sink))
    }

    fn synthesize_with_cached_regions<F: Field, CS: Assignment<F> + SyncDeps, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
        cached_regions: Option<&[RegionStart]>,
    ) -> Result<(), Error> {
        match cached_regions {
            Some(cached) => {
                let layouter =
                    SingleChipLayouter::new_with_cached_regions(cs, constants, cached.to_vec())?;
                circuit.synthesize(config, layouter)
            }
            None => {
                let layouter = SingleChipLayouter::new(cs, constants)?;
                circuit.synthesize(config, layouter)
            }
        }
    }

    #[cfg(feature = "prover-par")]
    fn synthesize_measuring_layout<F: Field, CS: Assignment<F> + SyncDeps, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
    ) -> Result<Option<MeasuredLayout>, Error> {
        let mut probe = ProbeState::default();
        let layouter = SingleChipLayouter::new_probing(cs, constants, None, &mut probe)?;
        circuit.synthesize(config, layouter)?;
        // A later check could not detect regions whose cells differ between
        // the shape pass and the assignment.
        Ok((!probe.mismatch).then_some(probe.layout))
    }

    #[cfg(feature = "prover-par")]
    fn synthesize_checking_layout<F: Field, CS: Assignment<F> + SyncDeps, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
        layout: &MeasuredLayout,
    ) -> bool {
        let mut probe = ProbeState::default();
        let Ok(layouter) = SingleChipLayouter::new_probing(cs, constants, Some(layout), &mut probe)
        else {
            return false;
        };
        let result = circuit.synthesize(config, layouter);
        result.is_ok() && !probe.mismatch && probe.regions == layout.regions.len()
    }
}

/// A [`Layouter`] for a single-chip circuit.
pub struct SingleChipLayouter<'a, F: Field, CS: Assignment<F> + 'a> {
    cs: &'a mut CS,
    constants: Vec<Column<Fixed>>,
    /// Stores the starting row for each region.
    regions: Vec<RegionStart>,
    /// Stores the first empty row for each column.
    columns: HashMap<RegionColumn, usize>,
    /// Stores the table fixed columns.
    table_columns: Vec<TableColumn>,
    /// When `Some`, the shape pass is skipped and these pre-computed region
    /// starts are consulted instead. Indexed by the region's synthesis order.
    cached_region_starts: Option<Vec<RegionStart>>,
    /// When `Some`, each newly determined `RegionStart` is also written here
    /// so the caller can read the layout back after `circuit.synthesize`
    /// has consumed the layouter. Used by `synthesize_capturing_regions`.
    region_sink: Option<&'a mut Vec<RegionStart>>,
    /// When `Some`, the regions are measured.
    #[cfg(feature = "prover-par")]
    probe: Option<Probe<'a>>,
    _marker: PhantomData<F>,
}

/// How a [`SingleChipLayouter`] measures regions: without `expected` it runs
/// the stock shape pass and records the layout; with `expected` it places
/// the regions at its starts and checks them.
#[cfg(feature = "prover-par")]
struct Probe<'a> {
    expected: Option<&'a MeasuredLayout>,
    state: &'a mut ProbeState,
}

#[cfg(feature = "prover-par")]
#[derive(Default)]
struct ProbeState {
    layout: MeasuredLayout,
    /// Index of each column set in `layout.column_sets`.
    column_sets: HashMap<Vec<RegionColumn>, usize>,
    regions: usize,
    /// Checking: a region differed from `expected` or failed. Measuring: a
    /// region's assignment touched other cells than its shape pass.
    mismatch: bool,
}

impl<'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug for SingleChipLayouter<'a, F, CS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SingleChipLayouter")
            .field("regions", &self.regions)
            .field("columns", &self.columns)
            .finish()
    }
}

impl<'a, F: Field, CS: Assignment<F>> SingleChipLayouter<'a, F, CS> {
    /// Creates a new single-chip layouter.
    pub fn new(cs: &'a mut CS, constants: Vec<Column<Fixed>>) -> Result<Self, Error> {
        Ok(SingleChipLayouter {
            cs,
            constants,
            regions: vec![],
            columns: HashMap::default(),
            table_columns: vec![],
            cached_region_starts: None,
            region_sink: None,
            #[cfg(feature = "prover-par")]
            probe: None,
            _marker: PhantomData,
        })
    }

    /// Creates a layouter that skips the shape pass and reuses pre-computed
    /// region starts (typically captured during keygen).
    pub fn new_with_cached_regions(
        cs: &'a mut CS,
        constants: Vec<Column<Fixed>>,
        cached_regions: Vec<RegionStart>,
    ) -> Result<Self, Error> {
        Ok(SingleChipLayouter {
            cs,
            constants,
            regions: vec![],
            columns: HashMap::default(),
            table_columns: vec![],
            cached_region_starts: Some(cached_regions),
            region_sink: None,
            #[cfg(feature = "prover-par")]
            probe: None,
            _marker: PhantomData,
        })
    }

    /// Creates a layouter that runs the shape pass normally but mirrors each
    /// determined `RegionStart` into `sink`. After `circuit.synthesize`
    /// consumes the layouter, the caller can read the captured layout from
    /// `sink`.
    pub fn new_capturing(
        cs: &'a mut CS,
        constants: Vec<Column<Fixed>>,
        sink: &'a mut Vec<RegionStart>,
    ) -> Result<Self, Error> {
        Ok(SingleChipLayouter {
            cs,
            constants,
            regions: vec![],
            columns: HashMap::default(),
            table_columns: vec![],
            cached_region_starts: None,
            region_sink: Some(sink),
            #[cfg(feature = "prover-par")]
            probe: None,
            _marker: PhantomData,
        })
    }
}

impl<'a, F: Field, CS: Assignment<F> + 'a + SyncDeps> SingleChipLayouter<'a, F, CS> {
    fn assign_region_impl<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        #[cfg(feature = "prover-par")]
        if let Some(mut probe) = self.probe.take() {
            let result = self.assign_region_probed(&mut probe, name, assignment);
            self.probe = Some(probe);
            return result;
        }

        let region_index = self.regions.len();

        if let Some(ref cached) = self.cached_region_starts {
            // Reuse the layout computed by an earlier synthesis. The caller is
            // responsible for ensuring the circuit produces the same sequence
            // of `assign_region` calls as when the cache was captured; see
            // `FloorPlanner::synthesize_with_cached_regions`.
            self.regions.push(*cached.get(region_index).expect(
                "cached region count mismatch: more `assign_region` calls during \
                     proving than were captured during keygen; the circuit must produce \
                     the same sequence of `assign_region` calls in both contexts",
            ));
        } else {
            // Shape pass: position this region at the earliest row for which
            // none of its columns are in use.
            let mut shape = RegionShape::new(region_index.into());
            {
                let region: &mut dyn RegionLayouter<F> = &mut shape;
                assignment(region.into())?;
            }

            let mut region_start = 0;
            for column in &shape.columns {
                region_start =
                    cmp::max(region_start, self.columns.get(column).cloned().unwrap_or(0));
            }
            self.regions.push(region_start.into());

            for column in shape.columns {
                self.columns.insert(column, region_start + shape.row_count);
            }
        }

        if let Some(ref mut sink) = self.region_sink {
            sink.push(*self.regions.last().unwrap());
        }

        // Assign region cells.
        self.cs.enter_region(name);
        let mut region = SingleChipLayouterRegion::new(self, region_index.into());
        let result = {
            let region: &mut dyn RegionLayouter<F> = &mut region;
            assignment(region.into())
        }?;
        let constants_to_assign = region.constants;
        self.cs.exit_region();

        // Assign constants. For the simple floor planner, we assign constants in order
        // in the first `constants` column.
        if self.constants.is_empty() {
            if !constants_to_assign.is_empty() {
                return Err(Error::NotEnoughColumnsForConstants);
            }
        } else {
            let constants_column = self.constants[0];
            let next_constant_row =
                self.columns.entry(Column::<Any>::from(constants_column).into()).or_default();
            for (constant, advice) in constants_to_assign {
                self.cs.assign_fixed(
                    || format!("Constant({:?})", constant.evaluate()),
                    constants_column,
                    *next_constant_row,
                    || Value::known(constant),
                )?;
                self.cs.copy(
                    constants_column.into(),
                    *next_constant_row,
                    advice.column,
                    *self.regions[*advice.region_index] + advice.row_offset,
                )?;
                *next_constant_row += 1;
            }
        }

        Ok(result)
    }
}

#[cfg(feature = "prover-par")]
impl<'a, F: Field, CS: Assignment<F> + 'a + SyncDeps> SingleChipLayouter<'a, F, CS> {
    /// See [`Probe`].
    fn new_probing(
        cs: &'a mut CS,
        constants: Vec<Column<Fixed>>,
        expected: Option<&'a MeasuredLayout>,
        state: &'a mut ProbeState,
    ) -> Result<Self, Error> {
        Ok(SingleChipLayouter {
            cs,
            constants,
            regions: vec![],
            columns: HashMap::default(),
            table_columns: vec![],
            cached_region_starts: None,
            region_sink: None,
            probe: Some(Probe { expected, state }),
            _marker: PhantomData,
        })
    }

    /// Never surfaced: the prover discards the assignment and reruns the
    /// shape pass.
    fn layout_mismatch() -> Error {
        Error::Synthesis("the region differs from the cached layout".into())
    }

    /// `assign_region` of a probing layouter.
    ///
    /// Checking: the region is assigned once at its expected start. Its
    /// columns, row count and constants must match the expected entry, and
    /// the expected start must be the one the stock shape pass computes from
    /// `self.columns`. After a mismatch every later region fails at once.
    fn assign_region_probed<A, AR, N, NR>(
        &mut self,
        probe: &mut Probe<'a>,
        name: N,
        mut assignment: A,
    ) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        let region_index = self.regions.len();
        let state = &mut *probe.state;

        let (result, constants_to_assign) = match probe.expected {
            Some(expected) => {
                if state.mismatch {
                    return Err(Self::layout_mismatch());
                }
                state.regions += 1;
                let Some(entry) = expected.regions.get(region_index) else {
                    state.mismatch = true;
                    return Err(Self::layout_mismatch());
                };
                let start = entry.start;
                self.regions.push(start);

                let assigned = self.assign_measured(region_index, name, &mut assignment);
                let (result, measured, constants_to_assign) = match assigned {
                    Ok(assigned) => assigned,
                    Err(e) => {
                        state.mismatch = true;
                        return Err(e);
                    }
                };
                let stock_start = (measured.columns.iter())
                    .map(|column| self.columns.get(column).copied().unwrap_or(0))
                    .max()
                    .unwrap_or(0);
                if stock_start != *start
                    || !region_matches(expected, entry, &measured, constants_to_assign.len())
                {
                    state.mismatch = true;
                    return Err(Self::layout_mismatch());
                }
                for column in measured.columns {
                    self.columns.insert(column, *start + measured.row_count);
                }
                (result, constants_to_assign)
            }
            None => {
                let mut shape = RegionShape::new(region_index.into());
                {
                    let region: &mut dyn RegionLayouter<F> = &mut shape;
                    assignment(region.into())?;
                }

                let mut region_start = 0;
                for column in &shape.columns {
                    region_start =
                        cmp::max(region_start, self.columns.get(column).cloned().unwrap_or(0));
                }
                self.regions.push(region_start.into());

                for column in shape.columns.iter() {
                    self.columns.insert(*column, region_start + shape.row_count);
                }

                let (result, measured, constants_to_assign) =
                    self.assign_measured(region_index, name, &mut assignment)?;

                state.regions += 1;
                if measured.row_count != shape.row_count || !measured.has_columns(&shape.columns) {
                    state.mismatch = true;
                }
                let mut columns: Vec<RegionColumn> = shape.columns.iter().copied().collect();
                columns.sort();
                let next = state.layout.column_sets.len();
                let index = *state.column_sets.entry(columns).or_insert_with_key(|columns| {
                    state.layout.column_sets.push(columns.clone());
                    next
                });
                state.layout.regions.push(MeasuredRegion {
                    start: region_start.into(),
                    columns: index,
                    row_count: shape.row_count,
                    constants: constants_to_assign.len(),
                });
                (result, constants_to_assign)
            }
        };

        // Assign constants, as the stock `assign_region_impl` does.
        if self.constants.is_empty() {
            if !constants_to_assign.is_empty() {
                return Err(Error::NotEnoughColumnsForConstants);
            }
        } else {
            let constants_column = self.constants[0];
            let next_constant_row =
                self.columns.entry(Column::<Any>::from(constants_column).into()).or_default();
            for (constant, advice) in constants_to_assign {
                self.cs.assign_fixed(
                    || format!("Constant({:?})", constant.evaluate()),
                    constants_column,
                    *next_constant_row,
                    || Value::known(constant),
                )?;
                self.cs.copy(
                    constants_column.into(),
                    *next_constant_row,
                    advice.column,
                    *self.regions[*advice.region_index] + advice.row_offset,
                )?;
                *next_constant_row += 1;
            }
        }

        Ok(result)
    }

    /// The assignment of the stock `assign_region_impl`, measured.
    fn assign_measured<A, AR, N, NR>(
        &mut self,
        region_index: usize,
        name: N,
        assignment: &mut A,
    ) -> Result<MeasuredAssignment<F, AR>, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        self.cs.enter_region(name);
        let mut region = SingleChipLayouterRegion::new(self, region_index.into());
        let mut measuring = Measuring {
            inner: &mut region,
            measure: RegionMeasure::default(),
        };
        let result = {
            let region: &mut dyn RegionLayouter<F> = &mut measuring;
            assignment(region.into())
        };
        let measured = measuring.measure;
        let result = result?;
        let constants_to_assign = region.constants;
        self.cs.exit_region();
        Ok((result, measured, constants_to_assign))
    }
}

/// The closure's result, the measure, and the constants to assign.
#[cfg(feature = "prover-par")]
type MeasuredAssignment<F, AR> = (AR, RegionMeasure, Vec<(Rational<F>, Cell)>);

#[cfg(feature = "prover-par")]
fn region_matches(
    layout: &MeasuredLayout,
    region: &MeasuredRegion,
    measured: &RegionMeasure,
    constants: usize,
) -> bool {
    let Some(columns) = layout.column_sets.get(region.columns) else {
        return false;
    };
    region.row_count == measured.row_count
        && region.constants == constants
        && measured.has_columns(columns)
}

/// The columns and row count of a region, as `RegionShape` records them,
/// with a bitset lookup per call instead of hashing (large regions make
/// millions of calls).
#[cfg(feature = "prover-par")]
#[derive(Debug, Default)]
struct RegionMeasure {
    /// Per kind ([`RegionMeasure::key`]), one bit per column index below
    /// [`RegionMeasure::BITSET_COLUMNS`].
    seen: [Vec<u64>; 5],
    columns: Vec<RegionColumn>,
    row_count: usize,
}

#[cfg(feature = "prover-par")]
impl RegionMeasure {
    /// Indices from this one on are searched in `columns`, so a sparse large
    /// index allocates no large bitset.
    const BITSET_COLUMNS: usize = 1 << 16;

    /// Two columns are equal exactly when their keys are.
    fn key(column: &RegionColumn) -> (usize, usize) {
        match column {
            RegionColumn::Column(c) => {
                let kind = match c.column_type() {
                    Any::Advice => 0,
                    Any::Fixed => 1,
                    Any::Instance => 2,
                };
                (kind, c.index())
            }
            RegionColumn::Selector(s) => (if s.is_simple() { 3 } else { 4 }, s.index()),
        }
    }

    #[inline]
    fn touch(&mut self, column: RegionColumn, offset: usize) {
        self.row_count = cmp::max(self.row_count, offset + 1);
        let (kind, index) = Self::key(&column);
        if index >= Self::BITSET_COLUMNS {
            if !self.columns.contains(&column) {
                self.columns.push(column);
            }
            return;
        }
        let (word, bit) = (index / 64, 1u64 << (index % 64));
        let seen = &mut self.seen[kind];
        if seen.len() <= word {
            seen.resize(word + 1, 0);
        }
        if seen[word] & bit == 0 {
            seen[word] |= bit;
            self.columns.push(column);
        }
    }

    fn contains(&self, column: &RegionColumn) -> bool {
        let (kind, index) = Self::key(column);
        if index >= Self::BITSET_COLUMNS {
            return self.columns.contains(column);
        }
        self.seen[kind].get(index / 64).is_some_and(|w| w & (1u64 << (index % 64)) != 0)
    }

    /// Whether the region touched exactly the distinct columns `columns`.
    fn has_columns<'c>(&self, columns: impl IntoIterator<Item = &'c RegionColumn>) -> bool {
        let mut count = 0;
        for column in columns {
            if !self.contains(column) {
                return false;
            }
            count += 1;
        }
        count == self.columns.len()
    }
}

/// Forwards every call to `inner` and records it in `measure`.
#[cfg(feature = "prover-par")]
struct Measuring<'r, R> {
    inner: &'r mut R,
    measure: RegionMeasure,
}

#[cfg(feature = "prover-par")]
impl<R: fmt::Debug> fmt::Debug for Measuring<'_, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Measuring")
            .field("inner", &self.inner)
            .field("measure", &self.measure)
            .finish()
    }
}

/// Records the same calls as `RegionShape`.
#[cfg(feature = "prover-par")]
impl<F: Field, R: RegionLayouter<F>> RegionLayouter<F> for Measuring<'_, R> {
    fn enable_selector<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        selector: &Selector,
        offset: usize,
    ) -> Result<(), Error> {
        self.measure.touch((*selector).into(), offset);
        self.inner.enable_selector(annotation, selector, offset)
    }

    fn name_column<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Any>,
    ) {
        self.inner.name_column(annotation, column)
    }

    fn assign_advice<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Value<Rational<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.measure.touch(Column::<Any>::from(column).into(), offset);
        self.inner.assign_advice(annotation, column, offset, to)
    }

    fn assign_advice_from_constant<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        constant: Rational<F>,
    ) -> Result<Cell, Error> {
        self.measure.touch(Column::<Any>::from(column).into(), offset);
        self.inner.assign_advice_from_constant(annotation, column, offset, constant)
    }

    fn assign_advice_from_instance<'v>(
        &mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        instance: Column<Instance>,
        row: usize,
        advice: Column<Advice>,
        offset: usize,
    ) -> Result<(Cell, Value<F>), Error> {
        self.measure.touch(Column::<Any>::from(advice).into(), offset);
        self.inner
            .assign_advice_from_instance(annotation, instance, row, advice, offset)
    }

    fn instance_value(
        &mut self,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<Value<F>, Error> {
        self.inner.instance_value(instance, row)
    }

    fn assign_fixed<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Value<Rational<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.measure.touch(Column::<Any>::from(column).into(), offset);
        self.inner.assign_fixed(annotation, column, offset, to)
    }

    fn constrain_constant(&mut self, cell: Cell, constant: Rational<F>) -> Result<(), Error> {
        self.inner.constrain_constant(cell, constant)
    }

    fn constrain_equal(&mut self, left: Cell, right: Cell) -> Result<(), Error> {
        self.inner.constrain_equal(left, right)
    }
}

impl<'a, F: Field, CS: Assignment<F> + 'a + SyncDeps> Layouter<F>
    for SingleChipLayouter<'a, F, CS>
{
    type Root = Self;

    fn assign_region<A, AR, N, NR>(&mut self, name: N, assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        self.assign_region_impl(name, assignment)
    }

    fn assign_table<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), Error>
    where
        A: FnMut(Table<'_, F>) -> Result<(), Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        // Maintenance hazard: there is near-duplicate code in
        // `v1::AssignmentPass::assign_table`. Assign table cells.
        self.cs.enter_region(name);
        let mut table = SimpleTableLayouter::new(self.cs, &self.table_columns);
        {
            let table: &mut dyn TableLayouter<F> = &mut table;
            assignment(table.into())
        }?;
        let default_and_assigned = table.default_and_assigned;
        self.cs.exit_region();

        // Check that all table columns have the same length `first_unused`,
        // and all cells up to that length are assigned.
        let first_unused = compute_table_lengths(&default_and_assigned)?;

        // Record these columns so that we can prevent them from being used again.
        for column in default_and_assigned.keys() {
            self.table_columns.push(*column);
        }

        for (col, (default_val, _)) in default_and_assigned {
            // default_val must be Some because we must have assigned
            // at least one cell in each column, and in that case we checked
            // that all cells up to first_unused were assigned.
            self.cs.fill_from_row(col.inner(), first_unused, default_val.unwrap())?;
        }

        Ok(())
    }

    fn constrain_instance(
        &mut self,
        cell: Cell,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<(), Error> {
        self.cs.copy(
            cell.column,
            *self.regions[*cell.region_index] + cell.row_offset,
            instance.into(),
            row,
        )
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.cs.push_namespace(name_fn)
    }

    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        self.cs.pop_namespace(gadget_name)
    }
}

struct SingleChipLayouterRegion<'r, 'a, F: Field, CS: Assignment<F> + 'a> {
    layouter: &'r mut SingleChipLayouter<'a, F, CS>,
    region_index: RegionIndex,
    /// Stores the constants to be assigned, and the cells to which they are
    /// copied.
    constants: Vec<(Rational<F>, Cell)>,
}

impl<'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug for SingleChipLayouterRegion<'_, 'a, F, CS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SingleChipLayouterRegion")
            .field("layouter", &self.layouter)
            .field("region_index", &self.region_index)
            .finish()
    }
}

impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> SingleChipLayouterRegion<'r, 'a, F, CS> {
    fn new(layouter: &'r mut SingleChipLayouter<'a, F, CS>, region_index: RegionIndex) -> Self {
        SingleChipLayouterRegion {
            layouter,
            region_index,
            constants: vec![],
        }
    }
}

impl<'a, F: Field, CS: Assignment<F> + 'a + SyncDeps> RegionLayouter<F>
    for SingleChipLayouterRegion<'_, 'a, F, CS>
{
    fn enable_selector<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        selector: &Selector,
        offset: usize,
    ) -> Result<(), Error> {
        self.layouter.cs.enable_selector(
            annotation,
            selector,
            *self.layouter.regions[*self.region_index] + offset,
        )
    }

    fn name_column<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Any>,
    ) {
        self.layouter.cs.annotate_column(annotation, column);
    }

    fn assign_advice<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Value<Rational<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.layouter.cs.assign_advice(
            annotation,
            column,
            *self.layouter.regions[*self.region_index] + offset,
            to,
        )?;

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn assign_advice_from_constant<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        constant: Rational<F>,
    ) -> Result<Cell, Error> {
        let advice =
            self.assign_advice(annotation, column, offset, &mut || Value::known(constant))?;
        self.constrain_constant(advice, constant)?;

        Ok(advice)
    }

    fn assign_advice_from_instance<'v>(
        &mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        instance: Column<Instance>,
        row: usize,
        advice: Column<Advice>,
        offset: usize,
    ) -> Result<(Cell, Value<F>), Error> {
        let value = self.layouter.cs.query_instance(instance, row)?;

        let cell = self.assign_advice(annotation, advice, offset, &mut || value.to_field())?;

        self.layouter.cs.copy(
            cell.column,
            *self.layouter.regions[*cell.region_index] + cell.row_offset,
            instance.into(),
            row,
        )?;

        Ok((cell, value))
    }

    fn instance_value(
        &mut self,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<Value<F>, Error> {
        self.layouter.cs.query_instance(instance, row)
    }

    fn assign_fixed<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Value<Rational<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.layouter.cs.assign_fixed(
            annotation,
            column,
            *self.layouter.regions[*self.region_index] + offset,
            to,
        )?;

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn constrain_constant(&mut self, cell: Cell, constant: Rational<F>) -> Result<(), Error> {
        self.constants.push((constant, cell));
        Ok(())
    }

    fn constrain_equal(&mut self, left: Cell, right: Cell) -> Result<(), Error> {
        self.layouter.cs.copy(
            left.column,
            *self.layouter.regions[*left.region_index] + left.row_offset,
            right.column,
            *self.layouter.regions[*right.region_index] + right.row_offset,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use midnight_curves::Fq;

    use super::SimpleFloorPlanner;
    use crate::{
        circuit::{Layouter, Value},
        dev::MockProver,
        plonk::{
            Advice, Any, Assignment, Circuit, Column, Error, Fixed, FloorPlanner, Instance,
            Selector,
        },
        utils::rational::Rational,
    };

    #[test]
    fn not_enough_columns_for_constants() {
        struct MyCircuit {}

        impl Circuit<Fq> for MyCircuit {
            type Config = Column<Advice>;
            type FloorPlanner = SimpleFloorPlanner;
            #[cfg(feature = "circuit-params")]
            type Params = ();

            fn without_witnesses(&self) -> Self {
                MyCircuit {}
            }

            fn configure(meta: &mut crate::plonk::ConstraintSystem<Fq>) -> Self::Config {
                meta.advice_column()
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl crate::circuit::Layouter<Fq>,
            ) -> Result<(), crate::plonk::Error> {
                layouter.assign_region(
                    || "assign constant",
                    |mut region| region.assign_advice_from_constant(|| "one", config, 0, Fq::ONE),
                )?;

                Ok(())
            }
        }

        let circuit = MyCircuit {};
        assert!(matches!(
            MockProver::run(&circuit, vec![]).unwrap_err(),
            Error::NotEnoughColumnsForConstants,
        ));
    }

    // -----------------------------------------------------------------------
    // Helpers shared by the caching tests below.
    // -----------------------------------------------------------------------

    /// A two-region circuit: region 0 uses col_a (2 rows), region 1 uses col_b
    /// (1 row). Because the two regions share no columns they both start at
    /// row 0.
    struct TwoRegionCircuit;

    impl Circuit<Fq> for TwoRegionCircuit {
        type Config = (Column<Advice>, Column<Advice>);
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            TwoRegionCircuit
        }

        fn configure(meta: &mut crate::plonk::ConstraintSystem<Fq>) -> Self::Config {
            (meta.advice_column(), meta.advice_column())
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fq>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "r0",
                |mut region| {
                    region.assign_advice(|| "a0", config.0, 0, &mut || Value::known(Fq::ONE))?;
                    region.assign_advice(|| "a1", config.0, 1, &mut || Value::known(Fq::ONE))
                },
            )?;
            layouter.assign_region(
                || "r1",
                |mut region| {
                    region.assign_advice(|| "b0", config.1, 0, &mut || Value::known(Fq::ONE))
                },
            )?;
            Ok(())
        }
    }

    /// A no-op CS used to drive `synthesize_capturing_regions` /
    /// `synthesize_with_cached_regions` in unit tests without a full prover.
    struct NullCs;
    impl Assignment<Fq> for NullCs {
        fn enter_region<NR, N>(&mut self, _: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
        }
        fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
        }
        fn exit_region(&mut self) {}
        fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(())
        }
        fn query_instance(&self, _: Column<Instance>, _: usize) -> Result<Value<Fq>, Error> {
            Ok(Value::unknown())
        }
        fn assign_advice<V, VR, A, AR>(
            &mut self,
            _: A,
            _: Column<Advice>,
            _: usize,
            _: V,
        ) -> Result<(), Error>
        where
            V: FnOnce() -> Value<VR>,
            VR: Into<Rational<Fq>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(())
        }
        fn assign_fixed<V, VR, A, AR>(
            &mut self,
            _: A,
            _: Column<Fixed>,
            _: usize,
            _: V,
        ) -> Result<(), Error>
        where
            V: FnOnce() -> Value<VR>,
            VR: Into<Rational<Fq>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(())
        }
        fn copy(
            &mut self,
            _: Column<Any>,
            _: usize,
            _: Column<Any>,
            _: usize,
        ) -> Result<(), Error> {
            Ok(())
        }
        fn fill_from_row(
            &mut self,
            _: Column<Fixed>,
            _: usize,
            _: Value<Rational<Fq>>,
        ) -> Result<(), Error> {
            Ok(())
        }
        fn push_namespace<NR, N>(&mut self, _: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
        }
        fn pop_namespace(&mut self, _: Option<String>) {}
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    #[test]
    fn capturing_regions_returns_some_and_correct_starts() {
        // SimpleFloorPlanner must support capture (return Some) and the
        // returned starts must match what the shape pass computes.
        let circuit = TwoRegionCircuit;
        let mut cs = crate::plonk::ConstraintSystem::<Fq>::default();
        let config = TwoRegionCircuit::configure(&mut cs);

        let starts = SimpleFloorPlanner::synthesize_capturing_regions(
            &mut NullCs,
            &circuit,
            config,
            cs.constants.clone(),
        )
        .expect("synthesis must not fail")
        .expect("SimpleFloorPlanner must return Some from synthesize_capturing_regions");

        assert_eq!(starts.len(), 2);
        // Both regions use independent columns, so both start at row 0.
        assert_eq!(*starts[0], 0);
        assert_eq!(*starts[1], 0);
    }

    #[test]
    #[should_panic(expected = "cached region count mismatch")]
    fn cached_region_count_mismatch_panics() {
        // A cache that is too short (1 entry for a 2-region circuit) must
        // produce a descriptive panic rather than a bare index-out-of-bounds.
        let circuit = TwoRegionCircuit;
        let mut cs = crate::plonk::ConstraintSystem::<Fq>::default();
        let config = TwoRegionCircuit::configure(&mut cs);

        // Capture the real starts so we have a properly-typed Vec, then
        // truncate it to 1 element.
        let mut starts = SimpleFloorPlanner::synthesize_capturing_regions(
            &mut NullCs,
            &circuit,
            config,
            cs.constants.clone(),
        )
        .unwrap()
        .unwrap();
        starts.truncate(1);

        SimpleFloorPlanner::synthesize_with_cached_regions(
            &mut NullCs,
            &circuit,
            config,
            cs.constants.clone(),
            Some(&starts),
        )
        .unwrap();
    }

    /// The measured layout has the stock starts; a check passes for it and
    /// fails, without a panic, against any altered layout.
    #[cfg(feature = "prover-par")]
    #[test]
    fn checking_layout_mismatch_is_not_a_panic() {
        use crate::circuit::layouter::MeasuredLayout;

        let circuit = TwoRegionCircuit;
        let mut cs = crate::plonk::ConstraintSystem::<Fq>::default();
        let config = TwoRegionCircuit::configure(&mut cs);
        let constants = cs.constants.clone();

        let starts = SimpleFloorPlanner::synthesize_capturing_regions(
            &mut NullCs,
            &circuit,
            config,
            constants.clone(),
        );
        let layout = SimpleFloorPlanner::synthesize_measuring_layout(
            &mut NullCs,
            &circuit,
            config,
            constants.clone(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(Some(layout.starts()), starts.unwrap());
        assert_eq!(
            layout.regions.iter().map(|r| r.row_count).collect::<Vec<_>>(),
            [2, 1]
        );

        let check = |alter: fn(&mut MeasuredLayout)| {
            let mut altered = layout.clone();
            alter(&mut altered);
            SimpleFloorPlanner::synthesize_checking_layout(
                &mut NullCs,
                &circuit,
                config,
                constants.clone(),
                &altered,
            )
        };
        assert!(check(|_| {}));
        let alterations: [fn(&mut MeasuredLayout); 7] = [
            |l| l.regions.truncate(1),
            |l| l.regions.push(l.regions[1].clone()),
            |l| l.regions[0].row_count = 3,
            |l| l.regions[1].columns = l.regions[0].columns,
            |l| l.regions[1].start = 5.into(),
            |l| *l = MeasuredLayout::default(),
            |l| l.regions[0].constants = 1,
        ];
        for alter in alterations {
            assert!(!check(alter));
        }
    }

    /// A region whose cells differ between the shape pass and the
    /// assignment yields no layout.
    #[cfg(feature = "prover-par")]
    #[test]
    fn measuring_skips_regions_unlike_their_shape_pass() {
        struct Fickle;
        impl Circuit<Fq> for Fickle {
            type Config = Column<Advice>;
            type FloorPlanner = SimpleFloorPlanner;
            #[cfg(feature = "circuit-params")]
            type Params = ();
            fn without_witnesses(&self) -> Self {
                Fickle
            }
            fn configure(meta: &mut crate::plonk::ConstraintSystem<Fq>) -> Self::Config {
                meta.advice_column()
            }
            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fq>,
            ) -> Result<(), Error> {
                let mut calls = 0;
                layouter.assign_region(
                    || "fickle",
                    |mut region| {
                        calls += 1;
                        for row in 0..calls {
                            region.assign_advice(|| "a", config, row, || Value::known(Fq::ONE))?;
                        }
                        Ok(())
                    },
                )
            }
        }
        let mut cs = crate::plonk::ConstraintSystem::<Fq>::default();
        let config = Fickle::configure(&mut cs);
        let measured = SimpleFloorPlanner::synthesize_measuring_layout(
            &mut NullCs,
            &Fickle,
            config,
            cs.constants.clone(),
        )
        .unwrap();
        assert!(measured.is_none());
    }

    /// `RegionMeasure` records what `RegionShape` records from the same
    /// calls.
    #[cfg(feature = "prover-par")]
    #[test]
    fn region_measure_matches_region_shape() {
        use crate::circuit::layouter::{RegionColumn, RegionLayouter, RegionShape};

        let mut cs = crate::plonk::ConstraintSystem::<Fq>::default();
        let advice: Vec<Column<Advice>> = (0..70).map(|_| cs.advice_column()).collect();
        let fixed: Vec<Column<Fixed>> = (0..66).map(|_| cs.fixed_column()).collect();
        let instance = cs.instance_column();
        let simple = cs.selector();
        let complex = cs.complex_selector();
        let far = Column::new(1 << 17, Fixed);

        let calls = |region: &mut dyn RegionLayouter<Fq>| -> Result<(), Error> {
            let name = &|| String::new();
            region.enable_selector(name, &simple, 3)?;
            region.enable_selector(name, &complex, 1)?;
            for (row, column) in [(0, 0), (5, 69), (2, 64), (9, 0), (4, 63)] {
                region.assign_advice(name, advice[column], row, &mut || {
                    Value::known(Fq::ONE.into())
                })?;
            }
            region.assign_advice_from_constant(name, advice[7], 11, Fq::ONE.into())?;
            region.assign_advice_from_instance(name, instance, 0, advice[8], 6)?;
            region.assign_fixed(name, fixed[65], 2, &mut || Value::known(Fq::ONE.into()))?;
            region.assign_fixed(name, far, 12, &mut || Value::known(Fq::ONE.into()))?;
            region.assign_fixed(name, far, 1, &mut || Value::known(Fq::ONE.into()))?;
            region.name_column(name, advice[30].into());
            let cell =
                region.assign_advice(name, advice[0], 1, &mut || Value::known(Fq::ONE.into()))?;
            region.constrain_equal(cell, cell)?;
            Ok(())
        };

        let mut shape = RegionShape::new(0.into());
        calls(&mut shape).unwrap();
        let mut inner = RegionShape::new(0.into());
        let mut measuring = super::Measuring {
            inner: &mut inner,
            measure: super::RegionMeasure::default(),
        };
        calls(&mut measuring).unwrap();
        let measure = measuring.measure;

        assert_eq!(shape.row_count(), 13);
        assert_eq!(measure.row_count, shape.row_count());
        assert_eq!(measure.columns.len(), shape.columns().len());
        assert!(measure.has_columns(shape.columns()));
        let mut fewer: Vec<RegionColumn> = shape.columns().iter().copied().collect();
        let dropped = fewer.pop().unwrap();
        assert!(!measure.has_columns(&fewer));
        fewer.push(Column::<Any>::from(advice[30]).into());
        assert!(!measure.has_columns(&fewer));
        fewer.pop();
        fewer.push(dropped);
        assert!(measure.has_columns(&fewer));
    }
}
