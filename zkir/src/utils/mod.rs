use std::collections::HashMap;

use midnight_circuits::types;
use midnight_curves::JubjubExtended;

use crate::{
    types::{IrType, IrValue},
    Error,
};

pub type F = midnight_curves::Fq;

pub type AssignedBit = types::AssignedBit<F>;
pub type AssignedByte = types::AssignedByte<F>;
pub type AssignedNative = types::AssignedNative<F>;
pub type AssignedBigUint = types::AssignedBigUint<F>;
pub type AssignedJubjubPoint = types::AssignedNativePoint<JubjubExtended>;
pub type AssignedJubjubScalar = types::AssignedScalarOfNativeCurve<JubjubExtended>;

pub mod constants;

pub fn insert<T: Clone>(map: &mut HashMap<String, T>, name: &str, value: &T) -> Result<(), Error> {
    map.insert(name.to_owned(), value.clone())
        .map_or(Ok(()), |_| Err(Error::DuplicatedName(name.to_string())))
}

/// Panics if |names| != |values|.
pub fn insert_many<T: Clone>(
    map: &mut HashMap<String, T>,
    names: &[String],
    values: &[T],
) -> Result<(), Error> {
    assert_eq!(names.len(), values.len());
    names
        .iter()
        .zip(values.iter())
        .try_for_each(|(name, value)| insert(map, name, value))
}

pub fn get_t(
    map: &HashMap<&'static str, IrValue>,
    t: IrType,
    name: &str,
) -> Result<IrValue, Error> {
    match map.get(name).cloned() {
        Some(x) => x.check_type(t).map(|()| x),
        None => Err(Error::NotFound(name.to_string())),
    }
}
