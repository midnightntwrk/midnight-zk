use midnight_circuits::{hash::poseidon::PoseidonChip, instructions::hash::HashCPU};
use midnight_proofs::circuit::Layouter;
use midnight_zk_stdlib::ZkStdLib;

use crate::{types::CircuitValue, utils::F, Error, IrValue};

/// Computes Poseidon off-circuit on the given inputs.
///
/// All inputs must be of type `Native`.
///
/// # Errors
///
/// If the inputs are not of type `Native`.
pub fn poseidon_offcircuit(inputs: &[IrValue]) -> Result<IrValue, Error> {
    let inputs = inputs.iter().map(|x| x.clone().try_into()).collect::<Result<Vec<_>, Error>>()?;
    let h = <PoseidonChip<F> as HashCPU<F, F>>::hash(&inputs);
    Ok(IrValue::Native(h))
}

/// Computes Poseidon in-circuit on the given inputs.
///
/// All inputs must be of type `Native`.
///
/// # Errors
///
/// If the inputs are not of type `Native`.
pub fn poseidon_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    inputs: &[CircuitValue],
) -> Result<CircuitValue, Error> {
    let inputs = inputs.iter().map(|x| x.clone().try_into()).collect::<Result<Vec<_>, Error>>()?;
    let h = std_lib.poseidon(layouter, &inputs)?;
    Ok(CircuitValue::Native(h))
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use rand_chacha::rand_core::OsRng;

    use super::*;

    #[test]
    fn test_poseidon_offcircuit() {
        use IrValue::*;

        let [x, y, z] = core::array::from_fn(|_| F::random(OsRng));

        let h = |inputs: &[F]| -> F { <PoseidonChip<F> as HashCPU<F, F>>::hash(inputs) };

        assert_eq!(poseidon_offcircuit(&[Native(x)]), Ok(h(&[x]).into()));

        assert_eq!(
            poseidon_offcircuit(&[Native(x), Native(y)]),
            Ok(h(&[x, y]).into())
        );
        assert_eq!(
            poseidon_offcircuit(&[Native(x), Native(y), Native(z)]),
            Ok(h(&[x, y, z]).into())
        );

        assert_eq!(
            poseidon_offcircuit(&[Bool(true)]),
            Err(Error::Other("cannot convert Bool to \"Native\"".into()))
        );

        assert_eq!(
            poseidon_offcircuit(&[num_bigint::BigUint::from(123u64).into()]),
            Err(Error::Other(
                "cannot convert BigUint(7) to \"Native\"".into()
            ))
        );
    }
}
