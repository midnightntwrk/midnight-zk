use midnight_circuits::{compact_std_lib::ZkStdLib, instructions::AssertionInstructions};
use midnight_proofs::circuit::Layouter;

use crate::{types::CircuitValue, utils::F, Error, Operation};

/// Asserts in-circuit that the given inputs are equal. The circuit becomes
/// unsatisfiable if they are not.
///
/// This operation is supported on all types except on `JubjubScalar`.
///
/// # Errors
///
/// This function results in an error if the two inputs are not of the same type
/// or if their type does not support equality assertions.
//
// NB: The off-circuit version of this function is derived automatically and a
// bit more general (e.g. it works on `JubjubScalar`s).
pub fn assert_equal_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<(), Error> {
    use CircuitValue::*;
    match (x, y) {
        (Bool(a), Bool(b)) => std_lib.assert_equal(layouter, a, b)?,

        (Bytes(v), Bytes(w)) if v.len() == w.len() => {
            (v.iter().zip(w)).try_for_each(|(vi, wi)| std_lib.assert_equal(layouter, vi, wi))?
        }

        (Native(a), Native(b)) => std_lib.assert_equal(layouter, a, b)?,

        (BigUint(a), BigUint(b)) => std_lib.biguint().assert_equal(layouter, a, b)?,

        (JubjubPoint(p), JubjubPoint(q)) => std_lib.jubjub().assert_equal(layouter, p, q)?,

        _ => {
            return Err(Error::Unsupported(
                Operation::AssertEqual,
                vec![x.get_type(), y.get_type()],
            ))
        }
    }

    Ok(())
}
