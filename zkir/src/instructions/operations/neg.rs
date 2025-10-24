use std::ops::Neg;

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

/// Negates off-circuit the given input.
/// Negation is supported on:
///   - `Native`
///   - `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input type is not supported.
pub fn neg_offcircuit(x: &IrValue) -> Result<IrValue, Error> {
    use IrValue::*;
    match x {
        Native(a) => Ok(Native(-a)),
        JubjubPoint(p) => Ok(JubjubPoint(-p)),
        _ => Err(Error::Unsupported(Operation::Neg, vec![x.get_type()])),
    }
}

/// Negates in-circuit the given input.
/// Negation is supported on:
///   - `Native`
///   - `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input type is not supported.
pub fn neg_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
) -> Result<CircuitValue, Error> {
    use CircuitValue::*;
    match x {
        Native(a) => {
            let r = std_lib.neg(layouter, a)?;
            Ok(Native(r))
        }
        JubjubPoint(p) => {
            let r = std_lib.jubjub().negate(layouter, p)?;
            Ok(JubjubPoint(r))
        }
        _ => Err(Error::Unsupported(Operation::Neg, vec![x.get_type()])),
    }
}

impl Neg for IrValue {
    type Output = Self;

    fn neg(self) -> Self {
        neg_offcircuit(&self).unwrap()
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
    fn test_neg() {
        use IrValue::*;

        let x = F::random(OsRng);
        let p = JubjubSubgroup::random(OsRng);
        let r = JubjubFr::random(OsRng);

        assert_eq!(-Native(x), Native(-x));
        assert_eq!(-JubjubPoint(p), JubjubPoint(-p));

        assert_eq!(
            neg_offcircuit(&JubjubScalar(r)),
            Err(Error::Unsupported(
                Operation::Neg,
                vec![IrType::JubjubScalar]
            ))
        );
    }
}
