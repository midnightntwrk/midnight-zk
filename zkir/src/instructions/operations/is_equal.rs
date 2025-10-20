use midnight_circuits::{
    compact_std_lib::ZkStdLib,
    instructions::{BinaryInstructions, EqualityInstructions},
};
use midnight_proofs::{circuit::Layouter, plonk};

use crate::{types::CircuitValue, utils::F, Error, Operation};

/// Returns a Boolean indicating whether the given inputs are equal.
///
/// This operation is supported on all types except on `JubjubScalar`.
///
/// # Errors
///
/// This function results in an error if the two inputs are not of the same type
/// or if their type does not support equality comparisons.
//
// NB: The off-circuit version of this function is derived automatically and a
// bit more general (e.g. it works on `JubjubScalar`s).
pub fn is_equal_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<CircuitValue, Error> {
    use CircuitValue::*;
    let b = match (x, y) {
        (Bool(a), Bool(b)) => std_lib.is_equal(layouter, a, b)?,

        (Bytes(v), Bytes(w)) if v.len() == w.len() => {
            let pair_wise_eq = (v.iter().zip(w))
                .map(|(vi, wi)| std_lib.is_equal(layouter, vi, wi))
                .collect::<Result<Vec<_>, plonk::Error>>()?;
            std_lib.and(layouter, &pair_wise_eq)?
        }

        (Native(a), Native(b)) => std_lib.is_equal(layouter, a, b)?,

        (BigUint(a), BigUint(b)) => std_lib.biguint().is_equal(layouter, a, b)?,

        (JubjubPoint(p), JubjubPoint(q)) => std_lib.jubjub().is_equal(layouter, p, q)?,

        _ => {
            return Err(Error::Unsupported(
                Operation::IsEqual,
                vec![x.get_type(), y.get_type()],
            ))
        }
    };

    Ok(Bool(b))
}
