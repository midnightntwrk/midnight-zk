//! Map instructions interface.
//!
//! It provides (in-circuit) functions for creating a map from a specified input
//! type into another.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::types::{AssignedNative, InnerValue};

/// The set of off-circuit instructions for mapping operations.
pub trait MapCPU<F, Key, Value> {
    /// Initializes a new map where all keys point to `default`.
    fn new(default: &Value) -> Self;

    /// A (cryptographically unequivocal) succinct representation of the map.
    fn succinct_repr(&self) -> F;

    /// Inserts a new key -> value entry into the map.
    fn insert(&mut self, key: &Key, value: &Value);

    /// Returns the value associated to a given key.
    /// Unlike a standard `HashMap` every single key has a value in this
    /// structure (possibly the default value it was created with).
    fn get(&self, key: &Key) -> Value;
}

/// The set of circuit instructions for mapping operations.
pub trait MapInstructions<F, AssignedKey, AssignedValue>
where
    F: PrimeField,
    AssignedKey: InnerValue,
    AssignedValue: InnerValue,
{
    /// The CPU version of the map.
    type MapCPU: MapCPU<F, AssignedKey::Element, AssignedValue::Element>;

    /// Initializes a new in-circuit map from the given off-circuit map.
    fn init(
        &mut self,
        layouter: &mut impl Layouter<F>,
        map: Value<Self::MapCPU>,
    ) -> Result<(), Error>;

    /// A (cryptographically unequivocal) succinct representation of the map.
    fn succinct_repr(&self) -> AssignedNative<F>;

    /// Inserts a new key -> value entry into the map.
    /// This call introduces in-circuit constraints that guarantee that the
    /// insertion was done correctly.
    fn insert(
        &mut self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedKey,
        value: &AssignedValue,
    ) -> Result<(), Error>;

    /// Returns the value associated to a given key.
    /// Unlike a standard `HashMap` every single key has a value in this
    /// structure (possibly the default value it was created with).
    /// This call introduces in-circuit constraints that guarantee that the
    /// returned value is correct.
    fn get(
        &self,
        layouter: &mut impl Layouter<F>,
        key: &AssignedKey,
    ) -> Result<AssignedValue, Error>;
}
