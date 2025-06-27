// This file is part of MIDNIGHT-ZK.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Elliptic curve operations interface.

use std::fmt::Debug;

use ff::PrimeField;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use super::AssertionInstructions;
use crate::{
    ecc::curves::CircuitCurve,
    instructions::DecompositionInstructions,
    types::{InnerConstants, InnerValue, Instantiable},
};

/// The  set of circuit instructions for EC operations.
pub trait EccInstructions<F: PrimeField, C: CircuitCurve>:
    AssertionInstructions<F, Self::Point>
where
    Self::Point: InnerValue<Element = C::CryptographicGroup>,
    Self::Coordinate: Instantiable<F> + InnerValue<Element = C::Base> + InnerConstants,
    Self::Scalar: InnerValue<Element = C::Scalar>,
{
    /// Type for assigned elliptic curve points.
    type Point: Clone + Debug;

    /// Type for assigned point coordinates (assigned base field values).
    type Coordinate: Clone + Debug;

    /// Type for assigned scalar field values.
    type Scalar: InnerValue;

    /// Performs complete point addition, returning `p + q`.
    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
        q: &Self::Point,
    ) -> Result<Self::Point, Error>;

    /// Performs complete point doubling, returning `2p`, possibly more
    /// efficiently than `add(layouter, p, p)`.
    fn double(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error>;

    /// Performs complete point negation, returning `-p`.
    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &Self::Point,
    ) -> Result<Self::Point, Error>;

    /// Variable-base multi-scalar multiplication, returning
    /// sum_i (scalar_i * base_i).
    /// Potentially more efficiently than folding with mul and add.
    /// The base points can be the identity.
    ///
    /// # Panics
    ///
    /// If `scalars.len() != bases.len()`.
    fn msm(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[Self::Scalar],
        bases: &[Self::Point],
    ) -> Result<Self::Point, Error>;

    /// Variable-base multi-scalar multiplication, returning
    /// sum_i (scalar_i * base_i).
    /// The base points can be the identity.
    ///
    /// The scalars are provided with an upper-bound on the number of bits
    /// necessary to represent them, which can be used to implement the
    /// constraints more efficiently.
    ///
    /// # Precondition
    ///
    ///  `s.0` is a scalar in the range `[0, 2^s.1)`, for all scalars `s`.
    ///
    /// # Panics
    ///
    /// If `scalars.len() != bases.len()`.
    ///
    /// Meeting the precondition is the responsibility of the caller, that is,
    /// the bounds are not enforced with constraints here, but should be
    /// enforced by the caller somewhere else.
    fn msm_by_bounded_scalars(
        &self,
        layouter: &mut impl Layouter<F>,
        scalars: &[(Self::Scalar, usize)],
        bases: &[Self::Point],
    ) -> Result<Self::Point, Error> {
        // This blanket implementation simply ignores all bounds.
        let scalars = scalars.iter().map(|s| s.0.clone()).collect::<Vec<_>>();
        self.msm(layouter, &scalars, bases)
    }

    /// Variable-base multiplication by a constant.
    /// The base can be the identity point.
    fn mul_by_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        scalar: C::Scalar,
        base: &Self::Point,
    ) -> Result<Self::Point, Error>;

    /// Creates an assigned point from a pair of coordinates, asserting that
    /// they satisfy the curve equation.
    /// (The identity cannot be constructed through this function.)
    fn point_from_coordinates(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &Self::Coordinate,
        y: &Self::Coordinate,
    ) -> Result<Self::Point, Error>;

    /// The assigned x-coordinate of an assigned point.
    fn x_coordinate(&self, point: &Self::Point) -> Self::Coordinate;

    /// The assigned y-coordinate of an assigned point.
    fn y_coordinate(&self, point: &Self::Point) -> Self::Coordinate;

    /// A set of arithmetic instructions over the base field.
    fn base_field(&self) -> &impl DecompositionInstructions<F, Self::Coordinate>;
}

#[cfg(test)]
pub mod tests {
    use std::{cmp::min, marker::PhantomData};

    use ff::{Field, FromUniformBytes};
    use group::Group;
    use midnight_proofs::{
        circuit::{Chip, Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem},
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        utils::circuit_modeling::circuit_to_json,
    };

    #[derive(Clone, Copy, Debug)]
    enum Operation {
        Add,
        Double,
        Neg,
        Msm,
        MsmBounded,
        MulByConstant,
        Coordinates,
    }

    #[derive(Clone, Debug)]
    struct TestCircuit<F, C, EccChip>
    where
        F: PrimeField,
        C: CircuitCurve,
    {
        inputs: Vec<C::CryptographicGroup>,
        scalars: Option<Vec<(C::Scalar, usize)>>,
        expected: C::CryptographicGroup,
        operation: Operation,
        _marker: PhantomData<(F, EccChip)>,
    }

    impl<F, C, EccChip> Circuit<F> for TestCircuit<F, C, EccChip>
    where
        F: PrimeField,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        type Config = <EccChip as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let committed_instance_column = meta.instance_column();
            let instance_column = meta.instance_column();
            EccChip::configure_from_scratch(meta, &[committed_instance_column, instance_column])
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let ecc_chip = EccChip::new_from_scratch(&config);
            EccChip::load_from_scratch(&mut layouter, &config);

            // y does not apply in tests of arity-1 functions.
            let y_idx = min(self.inputs.len() - 1, 1);
            let p: EccChip::Point = ecc_chip.assign(&mut layouter, Value::known(self.inputs[0]))?;
            let q: EccChip::Point = ecc_chip.assign_fixed(&mut layouter, self.inputs[y_idx])?;

            let res = match self.operation {
                Operation::Add => ecc_chip.add(&mut layouter, &p, &q),
                Operation::Double => ecc_chip.double(&mut layouter, &p),
                Operation::Neg => ecc_chip.negate(&mut layouter, &p),
                Operation::Msm => {
                    let scalars = self
                        .scalars
                        .clone()
                        .unwrap()
                        .iter()
                        .map(|s| ecc_chip.assign(&mut layouter, Value::known(s.0)))
                        .collect::<Result<Vec<_>, Error>>()?;
                    let bases = self
                        .inputs
                        .iter()
                        .map(|p| ecc_chip.assign_fixed(&mut layouter, *p))
                        .collect::<Result<Vec<_>, Error>>()?;
                    ecc_chip.msm(&mut layouter, &scalars, &bases)
                }
                Operation::MsmBounded => {
                    let scalars = self
                        .scalars
                        .clone()
                        .unwrap()
                        .iter()
                        .map(|s| {
                            let assigned_s = ecc_chip.assign(&mut layouter, Value::known(s.0))?;
                            Ok((assigned_s, s.1))
                        })
                        .collect::<Result<Vec<_>, Error>>()?;
                    let bases = self
                        .inputs
                        .iter()
                        .map(|p| ecc_chip.assign_fixed(&mut layouter, *p))
                        .collect::<Result<Vec<_>, Error>>()?;
                    ecc_chip.msm_by_bounded_scalars(&mut layouter, &scalars, &bases)
                }
                Operation::MulByConstant => {
                    let s = self.scalars.clone().unwrap()[0].0;
                    let base = ecc_chip.assign(&mut layouter, Value::known(self.inputs[0]))?;
                    ecc_chip.mul_by_constant(&mut layouter, s, &base)
                }
                Operation::Coordinates => {
                    let px = ecc_chip.x_coordinate(&p);
                    let py = ecc_chip.y_coordinate(&p);
                    ecc_chip.point_from_coordinates(&mut layouter, &px, &py)
                }
            }?;

            ecc_chip.assert_equal_to_fixed(&mut layouter, &res, self.expected)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run<F, C, EccChip>(
        inputs: &[C::CryptographicGroup],
        scalars: Option<&[(C::Scalar, usize)]>,
        expected: &C::CryptographicGroup,
        operation: Operation,
        must_pass: bool,
        cost_model: bool,
        chip_name: &str,
        op_name: &str,
    ) where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let circuit = TestCircuit::<F, C, EccChip> {
            inputs: inputs.to_vec(),
            scalars: scalars.map(|v| v.to_vec()),
            expected: *expected,
            operation,
            _marker: PhantomData,
        };
        let log2_nb_rows = match operation {
            Operation::Msm => 17,
            Operation::MsmBounded => 16,
            Operation::MulByConstant => 16,
            _ => 10,
        };
        let public_inputs = vec![vec![], vec![]];
        match MockProver::run(log2_nb_rows, &circuit, public_inputs) {
            Ok(prover) => match prover.verify() {
                Ok(()) => assert!(must_pass),
                Err(e) => assert!(!must_pass, "Failed verifier with error {e:?}"),
            },
            Err(e) => assert!(!must_pass, "Failed prover with error {e:?}"),
        }

        if cost_model {
            circuit_to_json(log2_nb_rows, chip_name, op_name, 0, circuit);
        }
    }

    pub fn test_add<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let id = C::CryptographicGroup::identity();
        let gen = C::CryptographicGroup::generator();
        let r = C::CryptographicGroup::random(&mut rng);
        let s = C::CryptographicGroup::random(&mut rng);
        let wrong = C::CryptographicGroup::random(&mut rng);
        let mut cost_model = true;
        [
            (&id, &r),
            (&r, &id),
            (&gen, &r),
            (&r, &gen),
            (&r, &r),
            (&r, &s),
            (&id, &id),
            (&id, &gen),
            (&gen, &id),
            (&gen, &gen),
        ]
        .into_iter()
        .for_each(|(x, y)| {
            let inputs = vec![*x, *y];
            let expected = *x + *y;
            run::<F, C, EccChip>(
                &inputs,
                None,
                &expected,
                Operation::Add,
                true,
                cost_model,
                name,
                "add",
            );
            cost_model = false;
            run::<F, C, EccChip>(&inputs, None, &wrong, Operation::Add, false, false, "", "");
        });
    }

    pub fn test_double<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let wrong = C::CryptographicGroup::random(&mut rng);
        let mut cost_model = true;
        [
            C::CryptographicGroup::identity(),
            C::CryptographicGroup::generator(),
            C::CryptographicGroup::random(&mut rng),
        ]
        .into_iter()
        .for_each(|x| {
            let inputs = vec![x];
            let expected = x + x;
            run::<F, C, EccChip>(
                &inputs,
                None,
                &expected,
                Operation::Double,
                true,
                cost_model,
                name,
                "double",
            );
            cost_model = false;
            run::<F, C, EccChip>(
                &inputs,
                None,
                &wrong,
                Operation::Double,
                false,
                false,
                "",
                "",
            );
        });
    }

    pub fn test_negate<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let wrong = C::CryptographicGroup::random(&mut rng);
        let mut cost_model = true;
        [
            C::CryptographicGroup::random(&mut rng),
            C::CryptographicGroup::identity(),
            C::CryptographicGroup::generator(),
        ]
        .into_iter()
        .for_each(|x| {
            let inputs = vec![x];
            let expected = -x;
            run::<F, C, EccChip>(
                &inputs,
                None,
                &expected,
                Operation::Neg,
                true,
                cost_model,
                name,
                "neg",
            );
            cost_model = false;
            run::<F, C, EccChip>(&inputs, None, &wrong, Operation::Neg, false, false, "", "");
        });
    }

    pub fn test_msm<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let n = 3;
        let inputs = (0..n)
            .map(|_| C::CryptographicGroup::random(&mut rng))
            .collect::<Vec<_>>();
        let scalars = (0..n)
            .map(|_| (C::Scalar::random(&mut rng), C::Scalar::NUM_BITS as usize))
            .collect::<Vec<_>>();
        let expected = inputs
            .clone()
            .into_iter()
            .zip(scalars.clone().iter())
            .fold(C::CryptographicGroup::identity(), |acc, (base, scalar)| {
                acc + (base * scalar.0)
            });
        let wrong = C::CryptographicGroup::random(&mut rng);
        run::<F, C, EccChip>(
            &inputs,
            Some(&scalars),
            &expected,
            Operation::Msm,
            true,
            true,
            name,
            "msm_3",
        );
        run::<F, C, EccChip>(
            &inputs,
            Some(&scalars),
            &wrong,
            Operation::Msm,
            false,
            false,
            "",
            "",
        );
    }

    pub fn test_msm_by_bounded_scalars<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let n = 3;
        let r = C::Scalar::random(&mut rng);
        let inputs = (0..n)
            .map(|_| C::CryptographicGroup::random(&mut rng))
            .collect::<Vec<_>>();
        let scalars = [
            (C::Scalar::from(3), 4),
            (C::Scalar::from(1025), 12),
            (r, C::Scalar::NUM_BITS as usize),
        ]
        .to_vec();
        let expected = inputs
            .clone()
            .into_iter()
            .zip(scalars.clone().iter())
            .fold(C::CryptographicGroup::identity(), |acc, (base, scalar)| {
                acc + (base * scalar.0)
            });
        let wrong = C::CryptographicGroup::random(&mut rng);
        run::<F, C, EccChip>(
            &inputs,
            Some(&scalars),
            &expected,
            Operation::MsmBounded,
            true,
            true,
            name,
            "msm_by_bounded_scalars_3",
        );
        run::<F, C, EccChip>(
            &inputs,
            Some(&scalars),
            &wrong,
            Operation::MsmBounded,
            false,
            false,
            name,
            "",
        );
    }

    pub fn test_mul_by_constant<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let base = C::CryptographicGroup::random(&mut rng);
        let s = C::Scalar::random(&mut rng);
        let mut cost_model = true;
        [
            (base, s, base * s, true),
            (base, C::Scalar::ONE, base, true),
            (base, s, C::CryptographicGroup::identity(), false),
            (
                C::CryptographicGroup::identity(),
                C::Scalar::from(123456),
                C::CryptographicGroup::identity(),
                true,
            ),
            (
                C::CryptographicGroup::generator(),
                C::Scalar::ZERO,
                C::CryptographicGroup::identity(),
                true,
            ),
        ]
        .into_iter()
        .for_each(|(base, s, expected, must_pass)| {
            run::<F, C, EccChip>(
                &[base],
                Some(&[(s, C::Scalar::NUM_BITS as usize)]),
                &expected,
                Operation::MulByConstant,
                must_pass,
                cost_model,
                name,
                "mul_by_constant",
            );
            cost_model = false;
        })
    }

    pub fn test_coordinates<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let wrong = C::CryptographicGroup::random(&mut rng);
        let mut cost_model = true;
        [
            (C::CryptographicGroup::random(&mut rng), true),
            (C::CryptographicGroup::identity(), false),
            (C::CryptographicGroup::generator(), true),
        ]
        .into_iter()
        .for_each(|(x, must_pass)| {
            let inputs = vec![x];
            run::<F, C, EccChip>(
                &inputs,
                None,
                &x,
                Operation::Coordinates,
                must_pass,
                cost_model & must_pass,
                name,
                "coordinates",
            );
            if must_pass {
                cost_model = false
            }
            run::<F, C, EccChip>(
                &inputs,
                None,
                &wrong,
                Operation::Coordinates,
                false,
                false,
                "",
                "",
            );
        });
    }

    /// The identity on Edwards curves is (0, 1) which indeed satisfies the
    /// curve equation. By contrast, the identity on Weierstrass curves is
    /// defined as (0, 0) which does NOT satisfy the curve equation.
    /// To distinguish these two cases, we have to use another test function for
    /// the Edwards coordinates.
    pub fn test_coordinates_edwards<F, C, EccChip>(name: &str)
    where
        F: PrimeField + FromUniformBytes<64> + Ord,
        C: CircuitCurve,
        EccChip: EccInstructions<F, C>
            + AssignmentInstructions<F, EccChip::Point>
            + AssignmentInstructions<F, EccChip::Scalar>
            + AssertionInstructions<F, EccChip::Point>
            + Chip<F>
            + FromScratch<F>,
        EccChip::Point: InnerValue<Element = C::CryptographicGroup> + Clone,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let wrong = C::CryptographicGroup::random(&mut rng);
        let mut cost_model = true;
        [
            // used for identity on Edwards curves
            (C::CryptographicGroup::random(&mut rng), true),
            (C::CryptographicGroup::identity(), true),
            (C::CryptographicGroup::generator(), true),
        ]
        .into_iter()
        .for_each(|(x, must_pass)| {
            let inputs = vec![x];
            run::<F, C, EccChip>(
                &inputs,
                None,
                &x,
                Operation::Coordinates,
                must_pass,
                cost_model & must_pass,
                name,
                "coordinates",
            );
            if must_pass {
                cost_model = false
            }
            run::<F, C, EccChip>(
                &inputs,
                None,
                &wrong,
                Operation::Coordinates,
                false,
                false,
                "",
                "",
            );
        });
    }
}
