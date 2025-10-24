use std::ops::Sub;

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

/// Subtracts off-circuit the given inputs.
/// Subtraction is supported on:
///   - `Native`
///   - `BigUint`
///   - `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
///
/// Subtracting a larger `BigUint` from a smaller one results in an underflow
/// error.
pub fn sub_offcircuit(x: &IrValue, y: &IrValue) -> Result<IrValue, Error> {
    use IrValue::*;
    match (x, y) {
        (Native(a), Native(b)) => Ok(Native(a - b)),
        (BigUint(a), BigUint(b)) => {
            if a >= b {
                Ok(BigUint(a - b))
            } else {
                Err(Error::Other(format!("underflow subtracting {b} from {a}")))
            }
        }
        (JubjubPoint(p), JubjubPoint(q)) => Ok(JubjubPoint(p - q)),
        _ => Err(Error::Unsupported(
            Operation::Sub,
            vec![x.get_type(), y.get_type()],
        )),
    }
}

/// Subtracts in-circuit the given inputs.
/// Subtracts is supported on:
///   - `Native`
///   - `BigUint`
///   - `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
pub fn sub_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<CircuitValue, Error> {
    use CircuitValue::*;
    match (x, y) {
        (Native(a), Native(b)) => {
            let r = std_lib.sub(layouter, a, b)?;
            Ok(Native(r))
        }
        (BigUint(a), BigUint(b)) => {
            let r = std_lib.biguint().sub(layouter, a, b)?;
            Ok(BigUint(r))
        }
        (JubjubPoint(p), JubjubPoint(q)) => {
            let neg_q = std_lib.jubjub().negate(layouter, q)?;
            let r = std_lib.jubjub().add(layouter, p, &neg_q)?;
            Ok(JubjubPoint(r))
        }
        _ => Err(Error::Unsupported(
            Operation::Sub,
            vec![x.get_type(), y.get_type()],
        )),
    }
}

impl Sub for IrValue {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        sub_offcircuit(&self, &rhs).unwrap()
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
    fn test_sub() {
        use IrValue::*;
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        let [x, y] = core::array::from_fn(|_| F::random(OsRng));
        let [p, q] = core::array::from_fn(|_| JubjubSubgroup::random(OsRng));
        let r = JubjubFr::random(OsRng);

        assert_eq!(Native(x) - Native(y), Native(x - y));
        assert_eq!(big(321) - big(123), big(198));
        assert_eq!(big(15) - big(15), big(0));
        assert_eq!(JubjubPoint(p) - JubjubPoint(q), JubjubPoint(p - q));

        assert_eq!(
            sub_offcircuit(&JubjubScalar(r), &JubjubScalar(r)),
            Err(Error::Unsupported(
                Operation::Sub,
                vec![IrType::JubjubScalar, IrType::JubjubScalar]
            ))
        );

        assert_eq!(
            sub_offcircuit(&big(5), &big(6)),
            Err(Error::Other("underflow subtracting 6 from 5".into()))
        );
    }
}
