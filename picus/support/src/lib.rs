use midnight_proofs::{
    circuit::{groups::RegionsGroup, AssignedCell, Cell},
    halo2curves::ff::Field,
    plonk::Error,
};

pub trait DecomposeInCells {
    fn cells(&self) -> impl IntoIterator<Item = Cell>;

    fn annotate_as_input(&self, group: &mut RegionsGroup) -> Result<(), Error> {
        group.annotate_inputs(self.cells())
    }

    fn annotate_as_output(&self, group: &mut RegionsGroup) -> Result<(), Error> {
        group.annotate_outputs(self.cells())
    }
}

impl DecomposeInCells for Cell {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        [*self]
    }
}

impl<V, F: Field> DecomposeInCells for AssignedCell<V, F> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        [self.cell()]
    }
}

impl DecomposeInCells for u32 {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        std::iter::empty()
    }
}

impl<T: DecomposeInCells, E> DecomposeInCells for Result<T, E> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<T: DecomposeInCells> DecomposeInCells for Option<T> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<T: DecomposeInCells> DecomposeInCells for &[T] {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<T: DecomposeInCells, const N: usize> DecomposeInCells for [T; N] {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<T: DecomposeInCells> DecomposeInCells for Vec<T> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}
