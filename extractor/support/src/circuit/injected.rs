//! Types for creating IR on the fly during synthesis.

use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use halo2_llzk_frontend::ir::stmt::IRStmt;
use midnight_proofs::{circuit::RegionIndex, plonk::Expression};

/// Records additional IR that gets added after synthesis.
pub struct InjectedIR<F>(HashMap<RegionIndex, Vec<IRStmt<(usize, Expression<F>)>>>);

impl<F> InjectedIR<F> {
    /// Adds the IR of the other into self.
    pub fn combine_ir(&mut self, other: Self) {
        for (region, ir) in other {
            self.entry(region).or_default().extend(ir);
        }
    }
}

impl<F> Deref for InjectedIR<F> {
    type Target = HashMap<RegionIndex, Vec<IRStmt<(usize, Expression<F>)>>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F> DerefMut for InjectedIR<F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<F> Default for InjectedIR<F> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<F: std::fmt::Debug> std::fmt::Debug for InjectedIR<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<F> IntoIterator for InjectedIR<F> {
    type Item = (RegionIndex, Vec<IRStmt<(usize, Expression<F>)>>);

    type IntoIter =
        <HashMap<RegionIndex, Vec<IRStmt<(usize, Expression<F>)>>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, F> IntoIterator for &'a InjectedIR<F> {
    type Item = (&'a RegionIndex, &'a Vec<IRStmt<(usize, Expression<F>)>>);

    type IntoIter =
        <&'a HashMap<RegionIndex, Vec<IRStmt<(usize, Expression<F>)>>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

impl<'a, F> IntoIterator for &'a mut InjectedIR<F> {
    type Item = (&'a RegionIndex, &'a mut Vec<IRStmt<(usize, Expression<F>)>>);

    type IntoIter =
        <&'a mut HashMap<RegionIndex, Vec<IRStmt<(usize, Expression<F>)>>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&mut self.0).into_iter()
    }
}
