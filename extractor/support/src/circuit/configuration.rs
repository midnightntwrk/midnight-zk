//! Traits related to circuit configuration.

use ff::PrimeField;
use midnight_proofs::plonk::{Advice, Column, ConstraintSystem, Fixed, Instance, TableColumn};

/// Helper trait that enables composing types that can handle circuit configuration.
pub trait AutoConfigure<Output = Self> {
    /// Creates an instance of self using the constraint system.
    fn configure<F: PrimeField>(meta: &mut ConstraintSystem<F>) -> Output;
}

macro_rules! auto_conf_impl {
    ($T:ty, $method:ident) => {
        impl AutoConfigure for $T {
            fn configure<F: PrimeField>(meta: &mut ConstraintSystem<F>) -> $T {
                meta.$method()
            }
        }
    };
}

auto_conf_impl!(Column<Fixed>, fixed_column);
auto_conf_impl!(Column<Instance>, instance_column);
auto_conf_impl!(Column<Advice>, advice_column);
auto_conf_impl!(TableColumn, lookup_table_column);

impl<T, const N: usize> AutoConfigure for [T; N]
where
    T: AutoConfigure,
{
    fn configure<F: PrimeField>(meta: &mut ConstraintSystem<F>) -> [T; N] {
        std::array::from_fn(|_| T::configure(meta))
    }
}

impl AutoConfigure for () {
    fn configure<F: PrimeField>(_: &mut ConstraintSystem<F>) -> Self {
        ()
    }
}

macro_rules! tuple_auto_conf_impl {
    ($($t:ident),+) => {
        impl<$( $t: AutoConfigure, )+> AutoConfigure for ( $( $t, )+ ) {
            fn configure<F: PrimeField>(meta: &mut ConstraintSystem<F>) -> ( $( $t, )+ ) {
                (
                    $( $t::configure(meta), )+
                )
            }
        }
    };
}

tuple_auto_conf_impl!(A1, A2);
