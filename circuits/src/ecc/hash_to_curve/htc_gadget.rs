use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{circuit::Layouter, plonk::Error};
#[cfg(any(test, feature = "testing"))]
use {
    crate::testing_utils::FromScratch,
    halo2_proofs::plonk::{Column, ConstraintSystem, Instance},
};

use super::{mtc::MapToCurveInstructions, mtc_cpu::MapToCurveCPU};
use crate::{
    ecc::curves::CircuitCurve,
    instructions::{
        hash_to_curve::HashToCurveCPU, EccInstructions, HashToCurveInstructions, SpongeCPU,
        SpongeInstructions,
    },
    types::InnerValue,
};

#[derive(Clone, Debug)]
/// A gadget for hashing into an elliptic curve. It is parametrized by:
///  - F: the native field,
///  - C: the elliptic curve,
///  - I: the hash input type,
///  - H: a set of in-circuit (sponge-based) hash instructions
///  - E: a set of in-circuit ECC instructions with map-to-curve support.
pub struct HashToCurveGadget<F, C, I, H, E>
where
    F: PrimeField,
    C: CircuitCurve + MapToCurveCPU<C>,
    I: InnerValue,
    H: SpongeInstructions<F, I, E::Coordinate>,
    E: EccInstructions<F, C> + MapToCurveInstructions<F, C>,
{
    sponge_chip: H,
    ecc_chip: E,
    _marker: PhantomData<(F, C, I)>,
}

impl<F, C, I, H, E> HashToCurveGadget<F, C, I, H, E>
where
    F: PrimeField,
    C: CircuitCurve + MapToCurveCPU<C>,
    I: InnerValue,
    H: SpongeInstructions<F, I, E::Coordinate> + Clone,
    E: EccInstructions<F, C> + MapToCurveInstructions<F, C> + Clone,
{
    /// Create a new hash-to-curve gadget.
    pub fn new(sponge_chip: &H, ecc_chip: &E) -> Self {
        Self {
            sponge_chip: sponge_chip.clone(),
            ecc_chip: ecc_chip.clone(),
            _marker: PhantomData,
        }
    }
}

impl<F, C, I, H, E> HashToCurveCPU<C, I::Element> for HashToCurveGadget<F, C, I, H, E>
where
    F: PrimeField,
    C: CircuitCurve + MapToCurveCPU<C>,
    I: InnerValue,
    H: SpongeInstructions<F, I, E::Coordinate>,
    E: EccInstructions<F, C> + MapToCurveInstructions<F, C>,
{
    fn hash_to_curve(inputs: &[I::Element]) -> C::CryptographicGroup {
        let mut state = <H as SpongeCPU<I::Element, C::Base>>::init(None);
        <H as SpongeCPU<I::Element, C::Base>>::absorb(&mut state, inputs);
        let x1 = <H as SpongeCPU<I::Element, C::Base>>::squeeze(&mut state);
        let x2 = <H as SpongeCPU<I::Element, C::Base>>::squeeze(&mut state);
        let p1 = C::map_to_curve(&x1);
        let p2 = C::map_to_curve(&x2);
        p1 + p2
    }
}

impl<F, C, I, H, E> HashToCurveInstructions<F, C, I, E> for HashToCurveGadget<F, C, I, H, E>
where
    F: PrimeField,
    C: CircuitCurve + MapToCurveCPU<C>,
    I: InnerValue,
    H: SpongeInstructions<F, I, E::Coordinate>,
    E: EccInstructions<F, C> + MapToCurveInstructions<F, C>,
{
    fn hash_to_curve(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[I],
    ) -> Result<E::Point, Error> {
        let mut state = self.sponge_chip.init(layouter, None)?;
        self.sponge_chip.absorb(layouter, &mut state, inputs)?;
        let x1 = self.sponge_chip.squeeze(layouter, &mut state)?;
        let x2 = self.sponge_chip.squeeze(layouter, &mut state)?;
        let p1 = self.ecc_chip.map_to_curve(layouter, &x1)?;
        let p2 = self.ecc_chip.map_to_curve(layouter, &x2)?;
        self.ecc_chip.add(layouter, &p1, &p2)
    }

    fn ecc_chip(&self) -> &E {
        &self.ecc_chip
    }
}

#[cfg(any(test, feature = "testing"))]
impl<F, C, I, H, E> FromScratch<F> for HashToCurveGadget<F, C, I, H, E>
where
    F: PrimeField,
    C: CircuitCurve + MapToCurveCPU<C>,
    I: InnerValue,
    H: SpongeInstructions<F, I, E::Coordinate> + FromScratch<F>,
    E: EccInstructions<F, C> + MapToCurveInstructions<F, C> + FromScratch<F>,
{
    type Config = (H::Config, E::Config);

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            sponge_chip: H::new_from_scratch(&config.0),
            ecc_chip: E::new_from_scratch(&config.1),
            _marker: Default::default(),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_column: &Column<Instance>,
    ) -> Self::Config {
        (
            H::configure_from_scratch(meta, instance_column),
            E::configure_from_scratch(meta, instance_column),
        )
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        H::load_from_scratch(layouter, &config.0);
        E::load_from_scratch(layouter, &config.1);
    }
}

#[cfg(test)]
mod tests {

    use blstrs::{JubjubExtended as Jubjub, Scalar as JubjubBase};
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::{
        ecc::native::EccChip,
        hash::poseidon::PoseidonChip,
        types::AssignedNative,
        utils::util::{big_to_fe, fe_to_big},
    };

    fn flip_random_bit<F: PrimeField>(mut rng: impl Rng, x: &F) -> F {
        let i = rng.gen_range(0..F::NUM_BITS) as u64;
        let mut biguint = fe_to_big(*x);
        biguint.set_bit(i, !biguint.bit(i));
        big_to_fe(biguint)
    }

    // The hamming distance between the canonical representation of the x
    // coordinates.
    fn distance<C, F>(p1: C::CryptographicGroup, p2: C::CryptographicGroup) -> u32
    where
        C: CircuitCurve<Base = F>,
        F: PrimeField,
    {
        let [x1, x2]: [F::Repr; 2] = [p1, p2].map(|v| {
            v.into()
                .coordinates()
                .expect("Valid affine point.")
                .0
                .to_repr()
        });

        (x1.as_ref().iter())
            .zip(x2.as_ref().iter())
            .fold(0u32, |acc, (b1, b2)| acc + (b1 ^ b2).count_ones())
    }

    fn test_avalanche_effect<F, C, H>()
    where
        F: PrimeField,
        C: CircuitCurve + MapToCurveCPU<C>,
        H: HashToCurveCPU<C, F>,
    {
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([1u8; 32]);
        const NB_REPETITIONS: usize = 10000;

        let distances = (0..NB_REPETITIONS).map(|_| {
            let input = F::random(&mut rng);
            let other = flip_random_bit(&mut rng, &input);

            let hash_input = H::hash_to_curve(&[input]);
            let hash_other = H::hash_to_curve(&[other]);

            let d = distance::<C, _>(hash_input, hash_other);

            assert!(d >= F::NUM_BITS / 2 - 40);
            assert!(d <= F::NUM_BITS / 2 + 40);

            d
        });

        let distances_mean = distances.sum::<u32>() / NB_REPETITIONS as u32;

        // Assert that, on average, half of the output bits change.
        assert_eq!(distances_mean, F::NUM_BITS / 2);
    }

    #[test]
    fn test_avalanche_hash_to_jubjub() {
        test_avalanche_effect::<
            JubjubBase,
            Jubjub,
            HashToCurveGadget<
                JubjubBase,
                Jubjub,
                AssignedNative<JubjubBase>,
                PoseidonChip<JubjubBase>,
                EccChip<Jubjub>,
            >,
        >()
    }
}
