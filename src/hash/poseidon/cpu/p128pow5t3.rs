use halo2curves::pasta::{pallas::Base as PallasBase, vesta::Base as VestaBase};

use crate::hash::poseidon::cpu::{Mds, Spec};

/// Poseidon-128 using the $x^5$ S-box, with a width of 3 field elements, and
/// the standard number of rounds for 128-bit security "with margin".
///
/// The standard specification for the Pasta fields uses $R_F = 8, R_P = 56$.
/// This is conveniently an even number of partial rounds, making it easier to
/// construct a Halo 2 circuit.
#[derive(Copy, Clone, Debug)]
pub struct P128Pow5T3;

impl P128Pow5T3 {
    /// Width in number of field elements
    pub const WIDTH: usize = 3;

    /// Rate in number of field elements
    pub const RATE: usize = 2;
}

impl Spec<PallasBase, 3, 2> for P128Pow5T3 {
    fn full_rounds() -> usize {
        8
    }

    fn partial_rounds() -> usize {
        56
    }

    fn constants() -> (Vec<[PallasBase; 3]>, Mds<PallasBase, 3>, Mds<PallasBase, 3>) {
        (
            super::super::params::pallas::ROUND_CONSTANTS[..].to_vec(),
            super::super::params::pallas::MDS,
            super::super::params::pallas::MDS_INV,
        )
    }
}

impl Spec<VestaBase, 3, 2> for P128Pow5T3 {
    fn full_rounds() -> usize {
        8
    }

    fn partial_rounds() -> usize {
        56
    }

    fn constants() -> (Vec<[VestaBase; 3]>, Mds<VestaBase, 3>, Mds<VestaBase, 3>) {
        (
            super::super::params::vesta::ROUND_CONSTANTS[..].to_vec(),
            super::super::params::vesta::MDS,
            super::super::params::vesta::MDS_INV,
        )
    }
}

impl Spec<blstrs::Scalar, 3, 2> for P128Pow5T3 {
    fn full_rounds() -> usize {
        8
    }

    fn partial_rounds() -> usize {
        56
    }

    fn constants() -> (
        Vec<[blstrs::Scalar; 3]>,
        Mds<blstrs::Scalar, 3>,
        Mds<blstrs::Scalar, 3>,
    ) {
        (
            super::super::params::bls::ROUND_CONSTANTS[..].to_vec(),
            super::super::params::bls::MDS,
            super::super::params::bls::MDS_INV,
        )
    }
}

#[cfg(test)]
mod tests {

    use ff::PrimeField;

    use super::{PallasBase, VestaBase};
    use crate::hash::poseidon::{
        cpu::{permute, ConstantLength, Poseidon},
        Spec,
    };

    #[test]
    fn permute_test_vectors() {
        {
            let (round_constants, mds, _) = super::P128Pow5T3::constants();

            for tv in crate::hash::poseidon::test_vectors::fp::permute() {
                let mut state = [
                    PallasBase::from_repr(tv.initial_state[0]).unwrap(),
                    PallasBase::from_repr(tv.initial_state[1]).unwrap(),
                    PallasBase::from_repr(tv.initial_state[2]).unwrap(),
                ];

                permute::<PallasBase, super::P128Pow5T3, 3, 2>(&mut state, &mds, &round_constants);

                for (expected, actual) in tv.final_state.iter().zip(state.iter()) {
                    assert_eq!(&actual.to_repr(), expected);
                }
            }
        }

        {
            let (round_constants, mds, _) = super::P128Pow5T3::constants();

            for tv in crate::hash::poseidon::test_vectors::fq::permute() {
                let mut state = [
                    VestaBase::from_repr(tv.initial_state[0]).unwrap(),
                    VestaBase::from_repr(tv.initial_state[1]).unwrap(),
                    VestaBase::from_repr(tv.initial_state[2]).unwrap(),
                ];

                permute::<VestaBase, super::P128Pow5T3, 3, 2>(&mut state, &mds, &round_constants);

                for (expected, actual) in tv.final_state.iter().zip(state.iter()) {
                    assert_eq!(&actual.to_repr(), expected);
                }
            }
        }
    }

    #[test]
    fn hash_test_vectors() {
        for tv in crate::hash::poseidon::test_vectors::fp::hash() {
            let message = [
                PallasBase::from_repr(tv.input[0]).unwrap(),
                PallasBase::from_repr(tv.input[1]).unwrap(),
            ];

            let result =
                Poseidon::<_, super::P128Pow5T3, _, 3, 2>::init(ConstantLength(2)).hash(&message);

            assert_eq!(result.to_repr(), tv.output);
        }

        for tv in crate::hash::poseidon::test_vectors::fq::hash() {
            let message = [
                VestaBase::from_repr(tv.input[0]).unwrap(),
                VestaBase::from_repr(tv.input[1]).unwrap(),
            ];

            let result =
                Poseidon::<_, super::P128Pow5T3, _, 3, 2>::init(ConstantLength(2)).hash(&message);

            assert_eq!(result.to_repr(), tv.output);
        }
    }
}
