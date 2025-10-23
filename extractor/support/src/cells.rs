//! Types and traits related to loading and storing data from cells.

use ff::PrimeField;
use midnight_proofs::circuit::AssignedCell;
use num_bigint::BigUint;

pub mod ctx;
pub mod load;
pub mod store;

/// Trait for defining how many cells in a circuit's table a type would take.
pub trait CellReprSize {
    /// Number of cells the type occupies.
    const SIZE: usize;
}

impl<const N: usize, T: CellReprSize> CellReprSize for [T; N] {
    const SIZE: usize = N * T::SIZE;
}

impl<F: PrimeField> CellReprSize for AssignedCell<F, F> {
    const SIZE: usize = 1;
}

macro_rules! zero_size_repr {
    ($t:ty) => {
        impl crate::cells::CellReprSize for $t {
            const SIZE: usize = 0;
        }
    };
}

zero_size_repr!(crate::fields::Blstrs);
zero_size_repr!(crate::fields::MidnightFp);
zero_size_repr!(crate::fields::JubjubFr);
zero_size_repr!(crate::fields::Jubjub);
zero_size_repr!(crate::fields::JubjubSubgroup);
zero_size_repr!(crate::fields::G1);
zero_size_repr!(crate::fields::Secp256k1);
zero_size_repr!(crate::fields::Secp256k1Fp);
zero_size_repr!(crate::fields::Secp256k1Fq);
zero_size_repr!(bool);
zero_size_repr!(u8);
zero_size_repr!(usize);
zero_size_repr!(BigUint);
zero_size_repr!(());

macro_rules! tuple_size {
    ($($t:ident),+) => {
        impl<$( $t: CellReprSize, )+> CellReprSize for (
                $( $t, )+
            )
        {
            const SIZE: usize = $( $t::SIZE + )+ 0;
        }
    };
}

tuple_size!(A1, A2);
tuple_size!(A1, A2, A3);
tuple_size!(A1, A2, A3, A4);
tuple_size!(A1, A2, A3, A4, A5);
