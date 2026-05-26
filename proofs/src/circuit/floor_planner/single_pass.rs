use std::{cmp, collections::HashMap, fmt, marker::PhantomData};

use ff::Field;

use crate::{
    circuit::{
        layouter::{RegionColumn, RegionLayouter, RegionShape, SyncDeps, TableLayouter},
        table_layouter::{compute_table_lengths, SimpleTableLayouter},
        Cell, Layouter, Region, RegionIndex, RegionStart, Table, Value,
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
    _marker: PhantomData<F>,
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
}
