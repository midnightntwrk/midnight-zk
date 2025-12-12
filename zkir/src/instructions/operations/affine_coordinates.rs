use midnight_circuits::{compact_std_lib::ZkStdLib, instructions::EccInstructions};
use midnight_curves::{JubjubAffine, JubjubExtended};
use midnight_proofs::circuit::Layouter;

use crate::{types::CircuitValue, utils::F, Error, IrValue, Operation};

/// Returns the off-circuit affine coordinates of the given EC point.
///
/// Supported on types:
///  - `JubjubPoint` -> `(Native, Native)`
///
/// # Errors
///
/// If the input type is not supported.
pub fn affine_coordinates_offcircuit(p: &IrValue) -> Result<(IrValue, IrValue), Error> {
    use IrValue::*;
    match p {
        JubjubPoint(p) => {
            let p_affine: JubjubAffine = Into::<JubjubExtended>::into(*p).into();
            let x = p_affine.get_u();
            let y = p_affine.get_v();
            Ok((Native(x), Native(y)))
        }
        _ => Err(Error::Unsupported(
            Operation::AffineCoordinates,
            vec![p.get_type()],
        )),
    }
}

/// Returns the in-circuit affine coordinates of the given EC point.
///
/// Supported on types:
///  - `JubjubPoint` -> `(Native, Native)`
///
/// # Errors
///
/// If the input type is not supported.
pub fn affine_coordinates_incircuit(
    std_lib: &ZkStdLib,
    _layouter: &mut impl Layouter<F>,
    p: &CircuitValue,
) -> Result<(CircuitValue, CircuitValue), Error> {
    use CircuitValue::*;
    match p {
        JubjubPoint(p) => {
            let x = std_lib.jubjub().x_coordinate(p);
            let y = std_lib.jubjub().y_coordinate(p);
            Ok((Native(x), Native(y)))
        }
        _ => Err(Error::Unsupported(
            Operation::AffineCoordinates,
            vec![p.get_type()],
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
    fn test_affine_coordinates() {
        use IrValue::*;

        let id = JubjubSubgroup::identity();
        let g = JubjubSubgroup::generator();
        let r = JubjubFr::random(OsRng);

        assert_eq!(
            affine_coordinates_offcircuit(&JubjubPoint(id)),
            Ok((Native(F::ZERO), Native(F::ONE)))
        );

        assert_eq!(
            affine_coordinates_offcircuit(&JubjubPoint(g)),
            Ok((
                Native(
                    F::from_u64s_le(&[
                        0x512dfea318d56fe5,
                        0x04315c657fbe375f,
                        0x5ed37ee3b172f5ee,
                        0x3ea5c4673a121ca3
                    ])
                    .unwrap()
                ),
                Native(
                    F::from_u64s_le(&[
                        0xc10cea38d50c55cb,
                        0xb9aa6e8e40808413,
                        0x78f7d30d3f616cb3,
                        0x57137b83ea6edb4f
                    ])
                    .unwrap()
                ),
            ))
        );

        assert_eq!(
            affine_coordinates_offcircuit(&JubjubScalar(r)),
            Err(Error::Unsupported(
                Operation::AffineCoordinates,
                vec![IrType::JubjubScalar]
            ))
        );
    }
}
