use midnight_circuits::{
    compact_std_lib::ZkStdLib, instructions::PublicInputInstructions, types::Instantiable,
};
use midnight_proofs::circuit::Layouter;

use crate::{
    types::{CircuitValue, IrType, IrValue},
    utils::{
        AssignedBigUint, AssignedBit, AssignedByte, AssignedJubjubPoint, AssignedJubjubScalar,
        AssignedNative, F,
    },
    Error,
};

impl CircuitValue {
    /// Converts off-circuit IR values into raw public inputs.
    ///
    /// # Error
    ///
    /// This function returns an error if one of the provided values is not of
    /// the declared type `t`.
    pub fn as_public_input(input: &IrValue, t: IrType) -> Result<Vec<F>, Error> {
        input.check_type(t)?;
        use IrValue::*;
        Ok(match input {
            Bool(b) => AssignedBit::as_public_input(b),
            Bytes(v) => v.iter().flat_map(AssignedByte::as_public_input).collect(),
            Native(x) => AssignedNative::as_public_input(x),
            BigUint(big) => {
                use IrType::BigUint;
                let BigUint(nb_bits) = t else { unreachable!() };
                AssignedBigUint::as_public_input(big, nb_bits)
            }
            JubjubPoint(p) => AssignedJubjubPoint::as_public_input(p),
            JubjubScalar(s) => AssignedJubjubScalar::as_public_input(s),
        })
    }
}

/// Constrains the given in-circuit IR values as public inputs.
/// This operation increases the public input vector, which will now expect an
/// extra value of the same type as `input`.
///
/// This function does not take a type (unlike its off-circuit analog). The type
/// of the given `CircuitValue` is inferred automatically. This inference is
/// trivial for most types except those whose size is not fixed (e.g. BigUint).
pub fn publish_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    input: &CircuitValue,
) -> Result<(), Error> {
    use CircuitValue::*;
    match input {
        Bool(b) => std_lib.constrain_as_public_input(layouter, b),
        Bytes(v) => v.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b)),
        Native(x) => std_lib.constrain_as_public_input(layouter, x),
        BigUint(big) => std_lib.biguint().constrain_as_public_input(layouter, big, big.nb_bits()),
        JubjubPoint(p) => std_lib.jubjub().constrain_as_public_input(layouter, p),
        JubjubScalar(s) => std_lib.jubjub().constrain_as_public_input(layouter, s),
    }
    .map_err(|e| e.into())
}

#[cfg(test)]
mod tests {
    use ff::{Field, PrimeField};
    use group::Group;
    use midnight_curves::{Fr as JubjubFr, JubjubSubgroup};

    use super::*;

    #[test]
    fn test_publish() {
        let big = |x: u128| -> IrValue { num_bigint::BigUint::from(x).into() };
        let fe = |s: &str| -> F {
            let mut bytes = const_hex::decode(s.as_bytes()).unwrap();
            bytes.resize(32, 0);
            let bytes: Vec<u8> = bytes.into_iter().rev().collect();
            F::from_bytes_le(&bytes.try_into().unwrap()).unwrap()
        };

        use IrType::*;
        // These test vectors are making assumptions about how the midnight-circuits
        // library converts values to raw public inputs. Beware that some of the
        // expected Ok results may change if midnight-circuits changes.
        [
            (Bool, false.into(), Ok(vec![F::ZERO])),
            (Bool, F::ONE.into(), Err(Error::ExpectingType(Bool, Native))),
            (Bytes(2), vec![0u8, 1u8].into(), Ok(vec![F::ZERO, F::ONE])),
            (Native, (-F::ONE).into(), Ok(vec![-F::ONE])),
            (BigUint(10), big(0), Ok(vec![F::ZERO])),
            (
                BigUint(64),
                big((1u128 << 64) - 1),
                Ok(vec![F::from(0xFFFFFFFF_FFFFFFFF)]),
            ),
            (
                BigUint(64),
                big(1u128 << 64),
                Err(Error::ExpectingType(BigUint(64), BigUint(65))),
            ),
            // Internally BigUints are currently represented in limbs of 96 bits.
            (
                BigUint(96),
                big((1u128 << 96) - 1),
                Ok(vec![F::from_u128((1u128 << 96) - 1)]),
            ),
            (
                BigUint(97),
                big((1u128 << 97) - 1),
                Ok(vec![F::from_u128((1u128 << 96) - 1), F::ONE]),
            ),
            (
                JubjubPoint,
                JubjubSubgroup::generator().into(),
                Ok(vec![
                    fe("0x3ea5c4673a121ca35ed37ee3b172f5ee04315c657fbe375f512dfea318d56fe5"),
                    fe("0x57137b83ea6edb4f78f7d30d3f616cb3b9aa6e8e40808413c10cea38d50c55cb"),
                ]),
            ),
            (
                JubjubScalar,
                (-JubjubFr::ONE).into(),
                Ok(vec![fe(
                    "0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb6",
                )]),
            ),
        ]
        .into_iter()
        .for_each(|(t, v, result): (IrType, IrValue, Result<Vec<F>, Error>)| {
            assert_eq!(CircuitValue::as_public_input(&v, t), result)
        });
    }
}
