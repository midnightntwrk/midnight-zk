use std::ops::Add;

use midnight_circuits::{
    compact_std_lib::ZkStdLib,
    instructions::{ArithInstructions, EccInstructions},
};
use midnight_proofs::circuit::Layouter;

use crate::{
    types::{CircuitValue, IrValue},
    utils::F,
    Error, Operation,
};

/// Adds off-circuit the given inputs.
/// Addition is supported on:
///   - `Native`
///   - `BigUint`
///   - `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
pub fn add_offcircuit(x: &IrValue, y: &IrValue) -> Result<IrValue, Error> {
    use IrValue::*;
    match (x, y) {
        (Native(a), Native(b)) => Ok(Native(a + b)),
        (BigUint(a), BigUint(b)) => Ok(BigUint(a + b)),
        (JubjubPoint(p), JubjubPoint(q)) => Ok(JubjubPoint(p + q)),
        _ => Err(Error::Unsupported(
            Operation::Add,
            vec![x.get_type(), y.get_type()],
        )),
    }
}

/// Adds in-circuit the given inputs.
/// Addition is supported on:
///   - `Native`
///   - `BigUint`
///   - `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
pub fn add_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<CircuitValue, Error> {
    use CircuitValue::*;
    match (x, y) {
        (Native(a), Native(b)) => {
            let r = std_lib.add(layouter, a, b)?;
            Ok(Native(r))
        }
        (BigUint(a), BigUint(b)) => {
            let r = std_lib.biguint().add(layouter, a, b)?;
            Ok(BigUint(r))
        }
        (JubjubPoint(p), JubjubPoint(q)) => {
            let r = std_lib.jubjub().add(layouter, p, q)?;
            Ok(JubjubPoint(r))
        }
        _ => Err(Error::Unsupported(
            Operation::Add,
            vec![x.get_type(), y.get_type()],
        )),
    }
}

impl Add for IrValue {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        add_offcircuit(&self, &rhs).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_curves::{Fr as JubjubFr, JubjubSubgroup};
    use rand_chacha::rand_core::OsRng;

    use super::*;
    use crate::IrType;

    #[test]
    fn test_add() {
        use IrValue::*;
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        let [x, y] = core::array::from_fn(|_| F::random(OsRng));
        let [p, q] = core::array::from_fn(|_| JubjubSubgroup::random(OsRng));
        let r = JubjubFr::random(OsRng);

        assert_eq!(Native(x) + Native(y), Native(x + y));
        assert_eq!(big(123) + big(321), big(444));
        assert_eq!(JubjubPoint(p) + JubjubPoint(q), JubjubPoint(p + q));

        assert_eq!(
            add_offcircuit(&JubjubScalar(r), &JubjubScalar(r)),
            Err(Error::Unsupported(
                Operation::Add,
                vec![IrType::JubjubScalar, IrType::JubjubScalar]
            ))
        );

        assert_eq!(
            add_offcircuit(&Native(x), &Bool(true)),
            Err(Error::Unsupported(
                Operation::Add,
                vec![IrType::Native, IrType::Bool]
            ))
        );
    }
}
