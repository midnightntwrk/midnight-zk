use midnight_circuits::{compact_std_lib::ZkStdLib, instructions::EccInstructions as _};
use midnight_proofs::circuit::Layouter;

use crate::{
    instructions::operations::{add_incircuit, add_offcircuit, mul_incircuit, mul_offcircuit},
    types::{CircuitValue, IrValue},
    utils::{AssignedJubjubPoint, AssignedJubjubScalar, F},
    Error, IrType, Operation,
};

/// Inner-product off-circuit of vector `v` with vector `w`.
///
/// Supported on types:
///
///    v                  w                <v, w>
///   ------------------------------------------------
///    `Native`          `Native`          `Native`
///    `BigUint`         `BigUint`         `BigUint`
///    `JubjubScalar`s   `JubjubPoint`s    `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
/// Also, if |v| != |w| or they are empty.
pub fn inner_product_offcircuit(v: &[IrValue], w: &[IrValue]) -> Result<IrValue, Error> {
    if v.len() != w.len() || v.is_empty() {
        return Err(Error::Other(format!("invalid length")));
    }

    (v.iter().skip(1).zip(w.iter().skip(1)))
        .try_fold(mul_offcircuit(&v[0], &w[0])?, |acc, (vi, wi)| {
            add_offcircuit(&acc, &mul_offcircuit(vi, wi)?)
        })
}

/// Inner-product in-circuit of vector `v` with vector `w`.
///
/// Supported on types:
///
///    v                  w                <v, w>
///   ------------------------------------------------
///    `Native`          `Native`          `Native`
///    `BigUint`         `BigUint`         `BigUint`
///    `JubjubScalar`s   `JubjubPoint`s    `JubjubPoint`
///
/// # Errors
///
/// This function results in an error if the input types are not supported.
pub fn inner_product_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    v: &[CircuitValue],
    w: &[CircuitValue],
) -> Result<CircuitValue, Error> {
    if v.len() != w.len() || v.is_empty() {
        return Err(Error::Other(format!("invalid length")));
    }

    let v_type = v[0].get_type();
    let w_type = w[0].get_type();

    use IrType::*;
    match (v_type, w_type) {
        (Native, Native) | (BigUint(_), BigUint(_)) => (v.iter().skip(1).zip(w.iter().skip(1)))
            .try_fold(
                mul_incircuit(std_lib, layouter, &v[0], &w[0])?,
                |acc, (vi, wi)| {
                    let p = mul_incircuit(std_lib, layouter, vi, wi)?;
                    add_incircuit(std_lib, layouter, &acc, &p)
                },
            ),

        (JubjubScalar, JubjubPoint) => {
            let scalars: Vec<AssignedJubjubScalar> =
                v.iter().map(|vi| vi.clone().try_into()).collect::<Result<_, Error>>()?;
            let points: Vec<AssignedJubjubPoint> =
                w.iter().map(|wi| wi.clone().try_into()).collect::<Result<_, Error>>()?;
            let r = std_lib.jubjub().msm(layouter, &scalars, &points)?;
            Ok(CircuitValue::JubjubPoint(r))
        }

        _ => Err(Error::Unsupported(
            Operation::InnerProduct,
            vec![v_type, w_type],
        )),
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
    fn test_inner_productl() {
        use IrValue::*;
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        let [x, y, z, t] = core::array::from_fn(|_| F::random(OsRng));
        let [p, q] = core::array::from_fn(|_| JubjubSubgroup::random(OsRng));
        let [r, s] = core::array::from_fn(|_| JubjubFr::random(OsRng));

        assert_eq!(
            inner_product_offcircuit(&[x.into(), y.into()], &[z.into(), t.into()]),
            Ok(Native(x * z + y * t))
        );

        assert_eq!(
            inner_product_offcircuit(&[big(10), big(20)], &[big(30), big(40)]),
            Ok(big(10 * 30 + 20 * 40))
        );

        assert_eq!(
            inner_product_offcircuit(&[r.into(), s.into()], &[p.into(), q.into()]),
            Ok(JubjubPoint(p * r + q * s))
        );

        assert_eq!(
            inner_product_offcircuit(&[x.into(), s.into()], &[y.into(), q.into()]),
            Err(Error::Unsupported(
                Operation::Add,
                vec![IrType::Native, IrType::JubjubPoint]
            ))
        );

        assert_eq!(
            inner_product_offcircuit(&[], &[]),
            Err(Error::Other(format!("invalid length")))
        );
    }
}
