use midnight_circuits::{compact_std_lib::ZkStdLib, instructions::AssignmentInstructions};
use midnight_curves::{Fr as JubjubScalar, JubjubSubgroup};
use midnight_proofs::circuit::{Layouter, Value};
use num_bigint::BigUint;

use crate::{
    types::{CircuitValue, IrType, IrValue},
    utils::F,
    Error,
};

/// A sanity check, making sure that the given values are of the given type.
pub fn load_offcircuit(t: IrType, values: &[IrValue]) -> Result<Vec<IrValue>, Error> {
    values.iter().try_for_each(|v| v.check_type(t))?;
    Ok(values.to_vec())
}

/// Initializes fresh in-circuit (potentially secret) values of the given type.
/// The prover is allowed to fill these values freely, but is constrained to
/// respect the type.
///
/// # Error
///
/// This function returns an error if one of the provided values is not of the
/// declared type `t`.
pub fn load_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    t: IrType,
    values: &[Value<IrValue>],
) -> Result<Vec<CircuitValue>, Error> {
    fn convert_values<T: TryFrom<IrValue, Error = Error>>(
        values: &[Value<IrValue>],
    ) -> Result<Vec<Value<T>>, Error> {
        values
            .iter()
            .map(|v| v.as_ref().map_with_result(|x| x.clone().try_into()))
            .collect()
    }

    match t {
        IrType::Bool => std_lib
            .assign_many(layouter, &convert_values::<bool>(values)?)
            .map_err(|e| e.into())
            .map(|xs| xs.into_iter().map(CircuitValue::Bool).collect()),

        IrType::Bytes(n) => {
            let concatenated: Vec<Value<u8>> = convert_values::<Vec<u8>>(values)?
                .into_iter()
                .flat_map(|value| value.transpose_vec(n))
                .collect();
            let assigned = std_lib.assign_many(layouter, &concatenated)?;
            Ok(assigned.chunks(n).map(|chunk| CircuitValue::Bytes(chunk.to_vec())).collect())
        }

        IrType::Native => std_lib
            .assign_many(layouter, &convert_values::<F>(values)?)
            .map_err(|e| e.into())
            .map(|xs| xs.into_iter().map(CircuitValue::Native).collect()),

        IrType::BigUint(nb_bits) => convert_values::<BigUint>(values)?
            .into_iter()
            .map(|value| {
                std_lib
                    .biguint()
                    .assign_biguint(layouter, value, nb_bits)
                    .map_err(|e| e.into())
                    .map(CircuitValue::BigUint)
            })
            .collect(),

        IrType::JubjubPoint => std_lib
            .jubjub()
            .assign_many(layouter, &convert_values::<JubjubSubgroup>(values)?)
            .map_err(|e| e.into())
            .map(|xs| xs.into_iter().map(CircuitValue::JubjubPoint).collect()),

        IrType::JubjubScalar => std_lib
            .jubjub()
            .assign_many(layouter, &convert_values::<JubjubScalar>(values)?)
            .map_err(|e| e.into())
            .map(|xs| xs.into_iter().map(CircuitValue::JubjubScalar).collect()),
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;

    use super::*;

    #[test]
    fn test_load() {
        let big = |x: u64| -> IrValue { num_bigint::BigUint::from(x).into() };

        use IrType::*;
        [
            (Bool, false.into(), None),
            (Bool, F::ONE.into(), Some((Bool, Native))),
            (Bytes(2), vec![0u8, 1u8].into(), None),
            (Bytes(2), vec![255u8].into(), Some((Bytes(2), Bytes(1)))),
            (Native, F::ONE.into(), None),
            (BigUint(10), big(0), None),
            (BigUint(10), big(1023), None),
            (BigUint(10), big(1024), Some((BigUint(10), BigUint(11)))),
        ]
        .into_iter()
        .for_each(
            |(t, v, err_opt): (IrType, IrValue, Option<(IrType, IrType)>)| {
                assert_eq!(
                    load_offcircuit(t, &[v.clone()]),
                    err_opt.map_or(Ok(vec![v]), |(t1, t2)| Err(Error::ExpectingType(t1, t2)))
                )
            },
        );
    }
}
