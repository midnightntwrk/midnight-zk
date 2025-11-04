//! Traits and structs related to groups of regions.

use std::{
    cell::RefCell,
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher as _},
    marker::PhantomData,
    ops::Deref,
    rc::Rc,
};

use ff::Field;

use crate::{
    circuit::{Cell, Layouter},
    plonk::Error,
};

/// Marker trait that defines a key that uniquelly identifying a group.
///
/// The uniqueness comes from [`std::hash::Hash`].
///
/// For most cases the [`DefaultKey`] is enough, but you can define your own if
/// necessary.
pub trait GroupKey: Copy + Hash + std::fmt::Debug + Sized {}

/// Type erased group key.
///
/// Allows using different implementations of [`GroupKey`] together.
/// Can be constructed from any implementation of [`GroupKey`]
/// and stores only the resulting hash, erasing the original type.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GroupKeyInstance(u64);

impl<K> From<K> for GroupKeyInstance
where
    K: GroupKey,
{
    fn from(value: K) -> Self {
        let mut h = DefaultHasher::new();
        // Salt the hash with the type's name
        std::any::type_name_of_val(&value).hash(&mut h);
        value.hash(&mut h);
        Self(h.finish())
    }
}

impl Deref for GroupKeyInstance {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<GroupKeyInstance> for u64 {
    fn from(value: GroupKeyInstance) -> Self {
        value.0
    }
}

impl From<GroupKeyInstance> for usize {
    fn from(value: GroupKeyInstance) -> Self {
        value.0 as usize
    }
}

/// Alias to the default key type used by [`crate::default_group_key!`].
pub type DefaultKey = SourceLocKey;

/// This macro returns an instance of the default key.
#[macro_export]
macro_rules! default_group_key {
    () => {
        $crate::circuit::groups::DefaultKey {
            file: std::file!(),
            line: std::line!(),
            column: std::column!(),
        }
    };
}

/// [`GroupKey`] based on a source code location (file, line, col).
#[derive(Copy, Clone, Debug, Hash)]
pub struct SourceLocKey {
    /// Filename
    pub file: &'static str,
    /// Line number
    pub line: u32,
    /// Column number
    pub column: u32,
}

impl GroupKey for SourceLocKey {}

/// Annotations associated with a group.
///
/// Currently the only possible annotation is declaring what [`CellRole`]
/// a [`Cell`] has in the group.
#[derive(Debug, Clone)]
pub struct RegionsGroup {
    cells: Vec<Cell>,
    annotations: HashMap<Cell, RoleAnnotation>,
    /// Shared with the Layouter for tracking if annotating is enabled or not.
    enabled: Rc<RefCell<bool>>,
}

impl RegionsGroup {
    fn new(enabled: Rc<RefCell<bool>>) -> Self {
        Self {
            cells: Default::default(),
            annotations: Default::default(),
            enabled,
        }
    }

    /// Returns a list of cells of the given role in the order of their
    /// annotation.
    fn cells_of_role(&self, role: CellRole) -> impl Iterator<Item = Cell> + '_ {
        self.cells.iter().filter_map(move |cell| {
            if self.annotations[cell] == role {
                Some(*cell)
            } else {
                None
            }
        })
    }

    /// Returns a list of [`Cell`] annotated as [`CellRole::Input`] in the order
    /// of annotation.
    pub fn inputs(&self) -> impl Iterator<Item = Cell> + '_ {
        self.cells_of_role(CellRole::Input)
    }

    /// Returns a list of [`Cell`] annotated as [`CellRole::Output`] in the
    /// order of annotation.
    pub fn outputs(&self) -> impl Iterator<Item = Cell> + '_ {
        self.cells_of_role(CellRole::Output)
    }

    /// Annotates a [`Cell`] with a [`CellRole`].
    ///
    /// Any cell can be annotated, even cells from regions outside the group.
    /// Upstream consumers of these annotations may require that cells from
    /// outside that are annotated with a role must have transitive copy
    /// constrains to at least one cell from the regions of the group. This
    /// requirement is not enforced by this type.
    #[inline]
    pub fn annotate_cell(&mut self, cell: Cell, role: CellRole) -> Result<(), Error> {
        if !*self.enabled.borrow() {
            return Ok(());
        }
        let entry = self.annotations.entry(cell);
        if matches!(entry, std::collections::hash_map::Entry::Vacant(_)) {
            self.cells.push(cell);
        }
        entry.or_default().annotate(role);
        //if self.annotations.contains_key(&cell) {
        //    return Err(Error::Transcript(std::io::Error::other(format!(
        //        "Failed to annotate cell {cell:?} with role {role:?}. Has role {:?}",
        //        self.annotations.get(&cell)
        //    ))));
        //}
        //self.cells.push(cell);
        //self.annotations.insert(cell, role);
        Ok(())
    }

    /// Annotates a [`Cell`] with a [`CellRole::Input`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    #[inline]
    pub fn annotate_input(&mut self, cell: Cell) -> Result<(), Error> {
        self.annotate_cell(cell, CellRole::Input)
    }

    /// Annotates a [`Cell`] with a [`CellRole::Output`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    /// cell from the regions of the group.
    #[inline]
    pub fn annotate_output(&mut self, cell: Cell) -> Result<(), Error> {
        self.annotate_cell(cell, CellRole::Output)
    }

    /// Annotates a list of [`Cell`] with a [`CellRole::Input`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    #[inline]
    pub fn annotate_inputs(&mut self, cells: impl IntoIterator<Item = Cell>) -> Result<(), Error> {
        for cell in cells {
            self.annotate_cell(cell, CellRole::Input)?;
        }
        Ok(())
    }

    /// Annotates a list of [`Cell`] with a [`CellRole::Output`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    /// cell from the regions of the group.
    #[inline]
    pub fn annotate_outputs(&mut self, cells: impl IntoIterator<Item = Cell>) -> Result<(), Error> {
        for cell in cells {
            self.annotate_cell(cell, CellRole::Output)?;
        }
        Ok(())
    }
}

/// Tracks regions and cell roles in a group.
///
/// Implements [`Layouter`] and can be used as a drop-in replacement.
#[derive(Debug)]
pub struct GroupLayouter<'l, F: Field, L: Layouter<F>> {
    parent: &'l mut L,
    /// Shared with RegionGroup for tracking if annotating is enabled or not.
    enabled: Rc<RefCell<bool>>,
    _marker: PhantomData<F>,
}

impl<'l, F: Field, L: Layouter<F>> GroupLayouter<'l, F, L> {
    pub(super) fn new(parent: &'l mut L, enabled: Rc<RefCell<bool>>) -> Self {
        Self {
            parent,
            enabled,
            _marker: Default::default(),
        }
    }
}

impl<F: Field, L: Layouter<F>> Layouter<F> for GroupLayouter<'_, F, L> {
    type Root = L::Root;

    fn assign_region<A, AR, N, NR>(
        &mut self,
        name: N,
        mut assignment: A,
    ) -> Result<AR, crate::plonk::Error>
    where
        A: FnMut(super::Region<'_, F>) -> Result<AR, crate::plonk::Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        let mut call_count = 0;
        self.parent.assign_region(name, |region| {
            // Enable annotating only the first time we call the closure.
            *self.enabled.borrow_mut() = call_count == 0;
            let r = assignment(region);
            *self.enabled.borrow_mut() = true;
            call_count += 1;
            r
        })
    }

    fn assign_table<A, N, NR>(
        &mut self,
        name: N,
        mut assignment: A,
    ) -> Result<(), crate::plonk::Error>
    where
        A: FnMut(super::Table<'_, F>) -> Result<(), crate::plonk::Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        let mut call_count = 0;
        self.parent.assign_table(name, |table| {
            // Enable annotating only the first time we call the closure.
            *self.enabled.borrow_mut() = call_count == 0;
            let r = assignment(table);
            *self.enabled.borrow_mut() = true;
            call_count += 1;
            r
        })
    }

    fn constrain_instance(
        &mut self,
        cell: Cell,
        column: crate::plonk::Column<crate::plonk::Instance>,
        row: usize,
    ) -> Result<(), crate::plonk::Error> {
        self.parent.constrain_instance(cell, column, row)
    }

    fn get_challenge(&self, challenge: crate::plonk::Challenge) -> super::Value<F> {
        self.parent.get_challenge(challenge)
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self.parent.get_root()
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.parent.push_namespace(name_fn)
    }

    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        self.parent.pop_namespace(gadget_name)
    }

    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: self::GroupKey,
    {
        self.parent.push_group(name, key)
    }

    fn pop_group(&mut self, meta: RegionsGroup) {
        self.parent.pop_group(meta)
    }
}

/// RAII handler used by the [`Layouter::group`] method.
pub(super) struct GroupScope<'l, F: Field, L: Layouter<F>> {
    pub layouter: GroupLayouter<'l, F, L>,
    pub meta: RegionsGroup,
}

impl<'l, F: Field, L: Layouter<F>> GroupScope<'l, F, L> {
    pub fn new(parent: &'l mut L) -> Self {
        let enabled = Rc::new(RefCell::new(true));
        Self {
            layouter: GroupLayouter::new(parent, enabled.clone()),
            meta: RegionsGroup::new(enabled),
        }
    }
}

impl<F: Field, L: Layouter<F>> Drop for GroupScope<'_, F, L> {
    fn drop(&mut self) {
        let meta = std::mem::replace(&mut self.meta, RegionsGroup::new(Default::default()));
        self.layouter.pop_group(meta)
    }
}

/// Possible roles of a cell inside a group.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CellRole {
    /// Input role
    Input,
    /// Output role
    Output,
    /// Internal role
    Internal,
}

/// Records the annotations of a cell.
#[derive(Copy, Clone, Debug, Default)]
enum RoleAnnotation {
    #[default]
    Empty,
    Input,
    Output,
    InputOutput,
    Internal,
}

impl RoleAnnotation {
    /// Annotates a role, updating internally based on the existing roles and
    /// the given one.
    ///
    /// Follows these rules for updating:
    /// - `{}, R -> {R}`: If its empty just adds the role.
    /// - `{IN}, OUT -> {IN, OUT}`: If it's an input and is annotated as an
    ///   output, combine them.
    /// - `{OUT}, IN -> {IN, OUT}`: If it's an output and is annotated as an
    ///   input, combine them.
    /// - `{R*}, INT -> {INT}`: Annotating as internal overrides preexisting
    ///   roles.
    /// - `{INT}, R -> {R}`: If it's annotated as internal overrides it with the
    ///   new role.
    fn annotate(&mut self, role: CellRole) {
        match (*self, role) {
            (RoleAnnotation::Empty | RoleAnnotation::Internal, r) => *self = r.into(),
            (RoleAnnotation::Input, CellRole::Input) => {}
            (RoleAnnotation::Input, CellRole::Output) => *self = RoleAnnotation::InputOutput,
            (RoleAnnotation::Output, CellRole::Output) => {}
            (RoleAnnotation::Output, CellRole::Input) => *self = RoleAnnotation::InputOutput,
            (RoleAnnotation::InputOutput, CellRole::Input | CellRole::Output) => {}
            (_, CellRole::Internal) => *self = RoleAnnotation::Internal,
        }
    }
}

impl From<CellRole> for RoleAnnotation {
    fn from(value: CellRole) -> Self {
        match value {
            CellRole::Input => RoleAnnotation::Input,
            CellRole::Output => RoleAnnotation::Output,
            CellRole::Internal => RoleAnnotation::Internal,
        }
    }
}

impl PartialEq<CellRole> for RoleAnnotation {
    fn eq(&self, other: &CellRole) -> bool {
        matches!(
            (self, other),
            (
                RoleAnnotation::Input | RoleAnnotation::InputOutput,
                CellRole::Input
            ) | (
                RoleAnnotation::Output | RoleAnnotation::InputOutput,
                CellRole::Output
            ) | (RoleAnnotation::Internal, CellRole::Internal)
        )
    }
}

#[cfg(test)]
mod tests {
    //! This test verify that the layouters forward properly the information
    //! about groups to an assignment.

    use super::*;
    use crate::plonk::{Advice, Any, Assignment, Column, Fixed, Instance};

    #[derive(Clone)]
    struct TestConfig {
        #[allow(dead_code)]
        instances: [Column<Instance>; 2],
        advices: [Column<Advice>; 4],
        #[allow(dead_code)]
        fixed: Column<Fixed>,
    }

    /// Helper macro for writing tests that run a sample circuit and computes a
    /// specification of the groups in created in it. Accepts a text
    /// representation of the specification that is compared against the
    /// produced result and, optionally, a closure that accepts a reference to
    /// a [`MockGroup`] to do additional assertions.
    macro_rules! circuit_test {
        ($name:ident, $planner:ident, |$config:ident, $layouter:ident| $body:expr, $expected:expr, $checks:expr) => {
            #[allow(unused_imports)]
            #[test]
            fn $name() {
                use halo2curves::bn256::Fr as F;

                use crate::{
                    circuit::{
                        groups::{
                            tests::{MockAssignment, TestConfig},
                            CellRole,
                        },
                        $planner, Layouter as _, Value,
                    },
                    plonk::{Circuit, ConstraintSystem, FloorPlanner},
                };

                #[derive(Default)]
                struct TestCircuit;

                impl Circuit<F> for TestCircuit {
                    type Config = TestConfig;

                    type FloorPlanner = $planner;

                    type Params = ();

                    fn without_witnesses(&self) -> Self {
                        Self::default()
                    }

                    fn configure(meta: &mut crate::plonk::ConstraintSystem<F>) -> Self::Config {
                        TestConfig {
                            instances: std::array::from_fn(|_| meta.instance_column()),
                            advices: std::array::from_fn(|_| meta.advice_column()),
                            fixed: meta.fixed_column(),
                        }
                    }

                    fn synthesize(
                        &self,
                        $config: Self::Config,
                        mut $layouter: impl crate::circuit::Layouter<F>,
                    ) -> Result<(), crate::plonk::Error> {
                        $body
                    }
                }

                let circuit = TestCircuit::default();
                let mut cs = ConstraintSystem::default();
                let cfg = TestCircuit::configure(&mut cs);
                let mut mock = MockAssignment::default();
                <TestCircuit as Circuit<F>>::FloorPlanner::synthesize(
                    &mut mock,
                    &circuit,
                    cfg,
                    vec![],
                )
                .unwrap();
                let top_level = mock.top_level();
                {
                    let top_level: String =
                        top_level.to_string().chars().filter(|c| !c.is_whitespace()).collect();
                    let expected: String =
                        $expected.to_string().chars().filter(|c| !c.is_whitespace()).collect();
                    assert_eq!(top_level, expected);
                }
                ($checks)(&top_level);
            }
        };
        ($name:ident, $planner:ident, |$config:ident, $layouter:ident| $body:expr, $expected:expr) => {
            circuit_test!(
                $name,
                $planner,
                |$config, $layouter| $body,
                $expected,
                |_| {}
            );
        };
    }

    circuit_test!(
        empty_circuit,
        SimpleFloorPlanner,
        |_config, _layouter| Ok(()),
        "(top-level)"
    );

    circuit_test!(
        one_level,
        SimpleFloorPlanner,
        |config, layouter| {
            layouter.group(
                || "one",
                default_group_key!(),
                |layouter, group| {
                    let o = layouter.assign_region(
                        || "r",
                        |mut region| {
                            let input = region.assign_advice(
                                || "in",
                                config.advices[1],
                                0,
                                || Value::<F>::unknown(),
                            )?;
                            group.annotate_input(input.cell())?;
                            region.assign_advice(
                                || "f",
                                config.advices[0],
                                0,
                                || input.value().copied(),
                            )
                        },
                    )?;
                    group.annotate_output(o.cell())?;
                    Ok(())
                },
            )
        },
        r"(top-level 
            (groups (one
                (inputs [R0[A1, 0]])
                (outputs [R0[A0, 0]])
        )))"
    );

    circuit_test!(
        one_level_outside_inputs,
        SimpleFloorPlanner,
        |config, layouter| {
            // This test uses cells from an outside region to test that any cell can be
            // annotated.
            let ins = layouter.assign_region(
                || "region #0",
                |mut region| {
                    let in0 = region.assign_advice(
                        || "in0",
                        config.advices[1],
                        0,
                        || Value::<F>::unknown(),
                    )?;
                    let in1 = region.assign_advice(
                        || "in1",
                        config.advices[1],
                        1,
                        || Value::<F>::unknown(),
                    )?;
                    Ok([in0, in1])
                },
            )?;
            layouter.group(
                || "one",
                default_group_key!(),
                |layouter, group| {
                    group.annotate_inputs(ins.iter().map(|ac| ac.cell()))?;
                    let o = layouter.assign_region(
                        || "region #1",
                        |mut region| {
                            let in0 = region.assign_advice(
                                || "in0",
                                config.advices[0],
                                0,
                                || ins[0].value().copied(),
                            )?;
                            let in1 = region.assign_advice(
                                || "in1",
                                config.advices[0],
                                1,
                                || ins[1].value().copied(),
                            )?;
                            region.constrain_equal(ins[0].cell(), in0.cell())?;
                            region.constrain_equal(ins[1].cell(), in1.cell())?;

                            region.assign_advice(
                                || "sum",
                                config.advices[2],
                                0,
                                || in0.value() + in1.value(),
                            )
                        },
                    )?;
                    group.annotate_output(o.cell())?;
                    Ok(())
                },
            )
        },
        r"(top-level 
            (groups (one
                (inputs [R0[A1, 0], R0[A1, 1]])
                (outputs [R1[A2, 0]])
        )))"
    );

    circuit_test!(
        one_level_outside_inputs_maintain_insertion_order,
        SimpleFloorPlanner,
        |config, layouter| {
            // This test uses cells from an outside region to test that any cell can be
            // annotated.
            let ins = layouter.assign_region(
                || "region #0",
                |mut region| {
                    let in0 = region.assign_advice(
                        || "in0",
                        config.advices[1],
                        0,
                        || Value::<F>::unknown(),
                    )?;
                    let in1 = region.assign_advice(
                        || "in1",
                        config.advices[1],
                        1,
                        || Value::<F>::unknown(),
                    )?;
                    Ok([in0, in1])
                },
            )?;
            layouter.group(
                || "one",
                default_group_key!(),
                |layouter, group| {
                    group.annotate_inputs(ins.iter().rev().map(|ac| ac.cell()))?;
                    let o = layouter.assign_region(
                        || "region #1",
                        |mut region| {
                            let in0 = region.assign_advice(
                                || "in0",
                                config.advices[0],
                                0,
                                || ins[0].value().copied(),
                            )?;
                            let in1 = region.assign_advice(
                                || "in1",
                                config.advices[0],
                                1,
                                || ins[1].value().copied(),
                            )?;
                            region.constrain_equal(ins[0].cell(), in0.cell())?;
                            region.constrain_equal(ins[1].cell(), in1.cell())?;

                            region.assign_advice(
                                || "sum",
                                config.advices[2],
                                0,
                                || in0.value() + in1.value(),
                            )
                        },
                    )?;
                    group.annotate_output(o.cell())?;
                    Ok(())
                },
            )
        },
        r"(top-level 
            (groups (one
                (inputs [R0[A1, 1], R0[A1, 0]])
                (outputs [R1[A2, 0]])
        )))"
    );

    circuit_test!(
        two_levels,
        SimpleFloorPlanner,
        |_config, layouter| {
            layouter.group(
                || "one",
                default_group_key!(),
                |layouter, _group| layouter.group(|| "two", default_group_key!(), |_, _| Ok(())),
            )
        },
        r"(top-level
            (groups (one
                (groups (two)
        ))))"
    );

    circuit_test!(
        two_consecutives,
        SimpleFloorPlanner,
        |_config, layouter| {
            layouter.group(|| "one", default_group_key!(), |_, _| Ok(()))?;
            layouter.group(|| "two", default_group_key!(), |_, _| Ok(()))
        },
        r"(top-level (groups (one) (two)))"
    );

    circuit_test!(
        two_calls_to_same_group,
        SimpleFloorPlanner,
        |_config, layouter| {
            for _ in 0..2 {
                layouter.group(|| "one", default_group_key!(), |_, _| Ok(()))?;
            }
            Ok(())
        },
        r"(top-level (groups (one) (one)))",
        |group: &MockGroup| {
            assert!(group.key == None);
            assert!(group.groups.len() == 2);
            let fst = &group.groups[0];
            let snd = &group.groups[1];

            // We need to test for the key here since the testing string does not include it
            assert_eq!(fst.key, snd.key);
        }
    );

    circuit_test!(
        two_calls_to_same_group_with_io,
        SimpleFloorPlanner,
        |config, layouter| {
            let x = config.advices[0];
            let y = config.advices[1];
            let z = config.advices[2];
            for _ in 0..2 {
                layouter.group(
                    || "one",
                    default_group_key!(),
                    |layouter, group| {
                        layouter.assign_region(
                            || "r",
                            |mut region| {
                                let x =
                                    region.assign_advice(|| "x", x, 0, || Value::<F>::unknown())?;
                                group.annotate_input(x.cell())?;
                                let y =
                                    region.assign_advice(|| "y", y, 0, || Value::<F>::unknown())?;
                                group.annotate_input(y.cell())?;
                                let z =
                                    region.assign_advice(|| "z", z, 0, || x.value() * y.value())?;
                                group.annotate_output(z.cell())?;
                                Ok(())
                            },
                        )
                    },
                )?;
            }
            Ok(())
        },
        r"(top-level (groups 
            (one
                (inputs [R0[A0, 0], R0[A1, 0]])
                (outputs [R0[A2, 0]])
            ) 
            (one
                (inputs [R1[A0, 0], R1[A1, 0]])
                (outputs [R1[A2, 0]])
            )))",
        |group: &MockGroup| {
            assert!(group.key == None);
            assert!(group.groups.len() == 2);
            let fst = &group.groups[0];
            let snd = &group.groups[1];

            // We need to test for the key here since the testing string does not include it
            assert_eq!(fst.key, snd.key);
        }
    );

    circuit_test!(
        cell_annotated_input_and_output,
        SimpleFloorPlanner,
        |config, layouter| {
            let x = config.advices[0];
            let y = config.advices[1];
            let z = config.advices[2];
            layouter.group(
                || "g",
                default_group_key!(),
                |layouter, group| {
                    layouter.assign_region(
                        || "r",
                        |mut region| {
                            let x = region.assign_advice(|| "x", x, 0, || Value::<F>::unknown())?;
                            let y = region.assign_advice(|| "y", y, 0, || Value::<F>::unknown())?;
                            let z = region.assign_advice(|| "z", z, 0, || Value::<F>::unknown())?;
                            group.annotate_inputs([x.cell(), y.cell()])?;
                            group.annotate_outputs([y.cell(), z.cell()])?;
                            Ok(())
                        },
                    )
                },
            )
        },
        r"(top-level (groups 
            (g
                (inputs [R0[A0, 0], R0[A1, 0]])
                (outputs [R0[A1, 0], R0[A2, 0]])
            )))"
    );

    // Supporting type for the tests

    #[derive(Clone, PartialEq, Eq, Debug)]
    enum GroupName {
        TopLevel,
        Group(String),
    }

    impl AsRef<str> for GroupName {
        fn as_ref(&self) -> &str {
            match self {
                GroupName::TopLevel => "top-level",
                GroupName::Group(s) => s.as_ref(),
            }
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone)]
    struct MockGroup {
        name: GroupName,
        key: Option<u64>,
        inputs: Vec<Cell>,
        outputs: Vec<Cell>,
        groups: Vec<MockGroup>,
    }

    impl MockGroup {
        fn empty(name: String, key: u64) -> Self {
            Self {
                name: GroupName::Group(name),
                key: Some(key),
                inputs: vec![],
                outputs: vec![],
                groups: vec![],
            }
        }
    }

    // Helper for displaying the cells in the mock output
    #[derive(PartialEq, Eq)]
    struct CellDisplay(Cell);

    impl std::fmt::Debug for CellDisplay {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "R{}[{}{}, {}]",
                self.0.region_index.0,
                match &self.0.column.column_type() {
                    crate::plonk::Any::Advice(_) => "A",
                    crate::plonk::Any::Fixed => "F",
                    crate::plonk::Any::Instance => "I",
                },
                self.0.column.index(),
                self.0.row_offset
            )
        }
    }

    impl PartialOrd for CellDisplay {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            // Lexicographic order (region idx, col type, col idx, row offset)
            match self.0.region_index.0.partial_cmp(&other.0.region_index.0) {
                Some(ord) if ord != std::cmp::Ordering::Equal => {
                    return Some(ord);
                }
                _ => {}
            }
            // col type order: Instance, Advice, Fixed
            match (self.0.column.column_type(), other.0.column.column_type()) {
                (Any::Advice(_), Any::Advice(_)) => None,
                (Any::Advice(_), Any::Fixed) => Some(std::cmp::Ordering::Less),
                (Any::Advice(_), Any::Instance) => Some(std::cmp::Ordering::Greater),
                (Any::Fixed, Any::Advice(_)) => Some(std::cmp::Ordering::Greater),
                (Any::Fixed, Any::Fixed) => None,
                (Any::Fixed, Any::Instance) => Some(std::cmp::Ordering::Greater),
                (Any::Instance, Any::Advice(_)) => Some(std::cmp::Ordering::Less),
                (Any::Instance, Any::Fixed) => Some(std::cmp::Ordering::Less),
                (Any::Instance, Any::Instance) => None,
            }
            .or_else(|| {
                match self.0.column.index().partial_cmp(&other.0.column.index()) {
                    Some(ord) if ord != std::cmp::Ordering::Equal => {
                        return Some(ord);
                    }
                    _ => {}
                }
                self.0.row_offset.partial_cmp(&other.0.row_offset)
            })
        }
    }

    impl Ord for CellDisplay {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.partial_cmp(other).expect("partial_cmp implementation is a total order")
        }
    }

    #[inline]
    fn format_cell_list(cells: &[Cell]) -> Vec<CellDisplay> {
        cells.iter().copied().map(CellDisplay).collect()
    }

    fn write_group(
        g: &MockGroup,
        f: &mut std::fmt::Formatter<'_>,
        ident: &mut String,
    ) -> std::fmt::Result {
        writeln!(f, "{ident}({}", g.name.as_ref())?;
        {
            ident.push(' ');
            if !g.inputs.is_empty() {
                writeln!(f, "{ident}(inputs {:?})", format_cell_list(&g.inputs))?;
            }
            if !g.outputs.is_empty() {
                writeln!(f, "{ident}(outputs {:?})", format_cell_list(&g.outputs))?;
            }
            if !g.groups.is_empty() {
                writeln!(f, "{ident}(groups")?;
                {
                    ident.push(' ');
                    for child in &g.groups {
                        write_group(child, f, ident)?;
                    }
                    ident.pop();
                }
                writeln!(f, "{ident})")?;
            }
            ident.pop();
        }
        writeln!(f, "{ident})")
    }

    impl std::fmt::Display for MockGroup {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut ident = String::new();
            write_group(self, f, &mut ident)
        }
    }

    struct MockAssignment {
        stack: Vec<MockGroup>,
    }

    impl MockAssignment {
        fn top_level(self) -> MockGroup {
            assert!(self.stack.len() == 1);
            self.stack.into_iter().next().unwrap()
        }
    }

    impl Default for MockAssignment {
        fn default() -> Self {
            Self {
                stack: vec![MockGroup {
                    name: GroupName::TopLevel,
                    key: None,
                    inputs: vec![],
                    outputs: vec![],
                    groups: vec![],
                }],
            }
        }
    }

    impl<F: Field> Assignment<F> for MockAssignment {
        fn enter_region<NR, N>(&mut self, _name_fn: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
        }

        fn annotate_column<A, AR>(&mut self, _annotation: A, _column: crate::plonk::Column<Any>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
        }

        fn exit_region(&mut self) {}

        fn enable_selector<A, AR>(
            &mut self,
            _annotation: A,
            _selector: &crate::plonk::Selector,
            _row: usize,
        ) -> Result<(), crate::plonk::Error>
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(())
        }

        fn query_instance(
            &self,
            _column: crate::plonk::Column<crate::plonk::Instance>,
            _row: usize,
        ) -> Result<crate::circuit::Value<F>, crate::plonk::Error> {
            Ok(crate::circuit::Value::unknown())
        }

        fn assign_advice<V, VR, A, AR>(
            &mut self,
            _annotation: A,
            _column: crate::plonk::Column<crate::plonk::Advice>,
            _row: usize,
            _to: V,
        ) -> Result<(), crate::plonk::Error>
        where
            V: FnOnce() -> crate::circuit::Value<VR>,
            VR: Into<crate::utils::rational::Rational<F>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(())
        }

        fn assign_fixed<V, VR, A, AR>(
            &mut self,
            _annotation: A,
            _column: crate::plonk::Column<crate::plonk::Fixed>,
            _row: usize,
            _to: V,
        ) -> Result<(), crate::plonk::Error>
        where
            V: FnOnce() -> crate::circuit::Value<VR>,
            VR: Into<crate::utils::rational::Rational<F>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            Ok(())
        }

        fn copy(
            &mut self,
            _left_column: crate::plonk::Column<Any>,
            _left_row: usize,
            _right_column: crate::plonk::Column<Any>,
            _right_row: usize,
        ) -> Result<(), crate::plonk::Error> {
            Ok(())
        }

        fn fill_from_row(
            &mut self,
            _column: crate::plonk::Column<crate::plonk::Fixed>,
            _row: usize,
            _to: crate::circuit::Value<crate::utils::rational::Rational<F>>,
        ) -> Result<(), crate::plonk::Error> {
            Ok(())
        }

        fn get_challenge(&self, _challenge: crate::plonk::Challenge) -> crate::circuit::Value<F> {
            crate::circuit::Value::unknown()
        }

        fn push_namespace<NR, N>(&mut self, _name_fn: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
        }

        fn pop_namespace(&mut self, _gadget_name: Option<String>) {}

        fn enter_group<NR, N, K>(&mut self, name_fn: N, key: K)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
            K: crate::circuit::groups::GroupKey,
        {
            let name = name_fn().into();
            let key = {
                let mut h = DefaultHasher::new();
                key.hash(&mut h);
                h.finish()
            };
            self.stack.push(MockGroup::empty(name, key));
        }

        fn exit_group(&mut self, meta: crate::circuit::groups::RegionsGroup) {
            // Fill the rest of the group data from the meta
            if let Some(top) = self.stack.last_mut() {
                top.inputs.extend(meta.inputs());
                top.outputs.extend(meta.outputs());
            }
            // Pop it from the stack and add it to the last one
            let g = self.stack.pop().unwrap();
            self.stack.last_mut().unwrap().groups.push(g);
        }
    }
}
