use midnight_circuits::compact_std_lib::ZkStdLib;
use midnight_proofs::circuit::Layouter;
use num_bigint::BigUint;

use crate::{
    types::{CircuitValue, IrValue},
    utils::F,
    Error, Operation,
};

/// Modular exponentiation off-circuit. Given x, n, m, returns x^n % m.
/// Here, n is a constant u64 and x, m must have the same type.
///
/// Supported x, m of type:
///   - `BigUint`
///
/// # Errors
///
/// If the input types are not supported.
pub fn mod_exp_offcircuit(x: &IrValue, n: u64, m: &IrValue) -> Result<IrValue, Error> {
    match (x, m) {
        (IrValue::BigUint(x), IrValue::BigUint(m)) => Ok(x.modpow(&BigUint::from(n), m).into()),
        _ => Err(Error::Unsupported(
            Operation::ModExp(n),
            vec![x.get_type(), m.get_type()],
        )),
    }
}

/// Modular exponentiation in-circuit. Given x, n, m, returns x^n % m.
/// Here, n is a constant u64 and x, m must have the same type.
///
/// Supported x, m of type:
///   - `BigUint`
///
/// # Errors
///
/// If the input types are not supported.
pub fn mod_exp_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &CircuitValue,
    n: u64,
    m: &CircuitValue,
) -> Result<CircuitValue, Error> {
    use CircuitValue::BigUint;
    match (x, m) {
        (BigUint(x), BigUint(m)) => {
            let r = std_lib.biguint().mod_exp(layouter, x, n, m)?;
            Ok(BigUint(r))
        }
        _ => Err(Error::Unsupported(
            Operation::ModExp(n),
            vec![x.get_type(), m.get_type()],
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::IrType;

    #[test]
    fn test_mul() {
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        assert_eq!(mod_exp_offcircuit(&big(2), 16, &big(1000)), Ok(big(536)));
        assert_eq!(mod_exp_offcircuit(&big(555), 0, &big(1234)), Ok(big(1)));

        assert_eq!(
            mod_exp_offcircuit(&F::from(2).into(), 16, &F::from(1000).into()),
            Err(Error::Unsupported(
                Operation::ModExp(16),
                vec![IrType::Native, IrType::Native],
            ))
        );
    }
}
