use std::ops::Mul;

use midnight_circuits::{compact_std_lib::ZkStdLib, instructions::ArithInstructions};
use midnight_proofs::circuit::Layouter;

use crate::{
    types::{CircuitValue, IrValue},
    utils::F,
    Error, Operation,
};

/// Multiplies off-circuit the given inputs.
/// Multiplication is supported on:
///   - `Native x Native -> Native`
///   - `BigUint x BigUint -> BigUint`
///   - `JubjubScalar x JubjubPoint -> JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
pub fn mul_offcircuit(x: &IrValue, y: &IrValue) -> Result<IrValue, Error> {
    use IrValue::*;
    match (x, y) {
        (Native(a), Native(b)) => Ok(Native(a * b)),
        (BigUint(a), BigUint(b)) => Ok(BigUint(a * b)),
        (JubjubScalar(s), JubjubPoint(p)) => Ok(JubjubPoint(p * s)),
        _ => Err(Error::Unsupported(
            Operation::Mul,
            vec![x.get_type(), y.get_type()],
        )),
    }
}

/// Multiplies in-circuit the given inputs.
/// Multiplication is supported on:
///   - `Native x Native -> Native`
///   - `BigUint x BigUint -> BigUint`
///   - `JubjubScalar x JubjubPoint -> JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
pub fn mul_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    y: &CircuitValue,
) -> Result<CircuitValue, Error> {
    use CircuitValue::*;
    match (x, y) {
        (Native(a), Native(b)) => {
            let r = std_lib.mul(layouter, a, b, None)?;
            Ok(Native(r))
        }
        (BigUint(a), BigUint(b)) => {
            let r = std_lib.biguint().mul(layouter, a, b)?;
            Ok(BigUint(r))
        }
        (JubjubScalar(s), JubjubPoint(p)) => {
            let r = std_lib.jubjub().mul(layouter, s, p)?;
            Ok(JubjubPoint(r))
        }
        _ => Err(Error::Unsupported(
            Operation::Mul,
            vec![x.get_type(), y.get_type()],
        )),
    }
}

impl Mul for IrValue {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        mul_offcircuit(&self, &rhs).unwrap()
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
    fn test_mul() {
        use IrValue::*;
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        let [x, y] = core::array::from_fn(|_| F::random(OsRng));
        let p = JubjubSubgroup::random(OsRng);
        let r = JubjubFr::random(OsRng);

        assert_eq!(Native(x) * Native(y), Native(x * y));
        assert_eq!(big(13) * big(7), big(91));
        assert_eq!(JubjubScalar(r) * JubjubPoint(p), JubjubPoint(p * r));

        assert_eq!(
            mul_offcircuit(&JubjubScalar(r), &JubjubScalar(r)),
            Err(Error::Unsupported(
                Operation::Mul,
                vec![IrType::JubjubScalar, IrType::JubjubScalar]
            ))
        );
    }
}
