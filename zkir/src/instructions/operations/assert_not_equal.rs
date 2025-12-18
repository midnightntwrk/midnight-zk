use midnight_circuits::instructions::AssertionInstructions;
use midnight_proofs::circuit::Layouter;
use midnight_zk_stdlib::ZkStdLib;

use crate::{
    instructions::operations::is_equal_incircuit,
    types::CircuitValue,
    utils::{AssignedBit, F},
    Error, Operation,
};

/// Asserts in-circuit that the given inputs are different. The circuit becomes
/// unsatisfiable if they are equal.
///
/// This operation is supported on all types except on `JubjubScalar`.
///
/// # Errors
///
/// This function results in an error if the two inputs are not of the same type
/// or if their type does not support inequality assertions.
//
// NB: The off-circuit version of this function is derived automatically and a
// bit more general (e.g. it works on `JubjubScalar`s).
pub fn assert_not_equal_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<(), Error> {
    use CircuitValue::*;
    match (x, y) {
        (Bool(a), Bool(b)) => std_lib.assert_not_equal(layouter, a, b)?,

        (Bytes(v), Bytes(w)) if v.len() == w.len() => {
            let b: AssignedBit = is_equal_incircuit(std_lib, layouter, x, y)?.try_into()?;
            std_lib.assert_equal_to_fixed(layouter, &b, false)?
        }

        (Native(a), Native(b)) => std_lib.assert_not_equal(layouter, a, b)?,

        (BigUint(a), BigUint(b)) => std_lib.biguint().assert_not_equal(layouter, a, b)?,

        (JubjubPoint(p), JubjubPoint(q)) => std_lib.jubjub().assert_not_equal(layouter, p, q)?,

        _ => {
            return Err(Error::Unsupported(
                Operation::AssertNotEqual,
                vec![x.get_type(), y.get_type()],
            ))
        }
    }

    Ok(())
}
