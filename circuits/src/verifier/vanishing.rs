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

//! A module for the in-circuit vanishing argument. This is the in-circuit
//! analog of file src/plonk/vanishing/verifier.rs from halo2.

use ff::Field;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    instructions::ArithInstructions,
    verifier::{
        kzg::VerifierQuery,
        msm::AssignedMsm,
        transcript_gadget::TranscriptGadget,
        types::{AssignedPoint, AssignedScalar, ScalarChip, SelfEmulationCurve},
        utils::{mul_add, mul_bounded_scalars, try_reduce, AssignedBoundedScalar},
    },
};

#[derive(Clone, Debug)]
pub(crate) struct Committed<C: SelfEmulationCurve> {
    random_poly_commitment: AssignedPoint<C>,
}

#[derive(Clone, Debug)]
pub(crate) struct Constructed<C: SelfEmulationCurve> {
    h_commitments: Vec<AssignedPoint<C>>,
    random_poly_commitment: AssignedPoint<C>,
}

#[derive(Clone, Debug)]
pub(crate) struct PartiallyEvaluated<C: SelfEmulationCurve> {
    h_commitments: Vec<AssignedPoint<C>>,
    random_poly_commitment: AssignedPoint<C>,
    random_eval: AssignedScalar<C>,
}

#[derive(Clone, Debug)]
pub(crate) struct Evaluated<C: SelfEmulationCurve> {
    h_commitment: AssignedMsm<C>,
    random_poly_commitment: AssignedPoint<C>,
    expected_h_eval: AssignedScalar<C>,
    random_eval: AssignedScalar<C>,
}

pub(crate) fn read_commitments_before_y<C: SelfEmulationCurve>(
    layouter: &mut impl Layouter<C::ScalarField>,
    transcript_gadget: &mut TranscriptGadget<C>,
) -> Result<Committed<C>, Error> {
    let random_poly_commitment = transcript_gadget.read_point(layouter)?;

    Ok(Committed {
        random_poly_commitment,
    })
}

impl<C: SelfEmulationCurve> Committed<C> {
    pub(crate) fn read_commitment_after_y(
        self,
        layouter: &mut impl Layouter<C::ScalarField>,
        transcript_gadget: &mut TranscriptGadget<C>,
        quotient_poly_degree: usize,
    ) -> Result<Constructed<C>, Error> {
        let h_commitments = (0..quotient_poly_degree)
            .map(|_| transcript_gadget.read_point(layouter))
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(Constructed {
            h_commitments,
            random_poly_commitment: self.random_poly_commitment,
        })
    }
}

impl<C: SelfEmulationCurve> Constructed<C> {
    pub(crate) fn evaluate_after_x(
        self,
        layouter: &mut impl Layouter<C::ScalarField>,
        transcript_gadget: &mut TranscriptGadget<C>,
    ) -> Result<PartiallyEvaluated<C>, Error> {
        let random_eval = transcript_gadget.read_scalar(layouter)?;

        Ok(PartiallyEvaluated {
            h_commitments: self.h_commitments,
            random_poly_commitment: self.random_poly_commitment,
            random_eval,
        })
    }
}

impl<C: SelfEmulationCurve> PartiallyEvaluated<C> {
    pub(crate) fn verify(
        &self,
        layouter: &mut impl Layouter<C::ScalarField>,
        scalar_chip: &ScalarChip<C>,
        expressions: &[AssignedScalar<C>],
        y: &AssignedScalar<C>,
        xn: &AssignedScalar<C>,
    ) -> Result<Evaluated<C>, Error> {
        let expected_h_eval = {
            let num = try_reduce(expressions.iter().cloned(), |h_eval, v| {
                // h_eval * y + v
                mul_add(layouter, scalar_chip, &h_eval, y, &v)
            })?;
            let den = scalar_chip.add_constant(layouter, xn, -C::ScalarField::ONE)?;
            scalar_chip.div(layouter, &num, &den)?
        };

        let xn = AssignedBoundedScalar::new(xn, None);
        let mut acc_xn = AssignedBoundedScalar::one(layouter, scalar_chip)?;

        let mut h_commitment = AssignedMsm::from_term(&acc_xn, &self.h_commitments[0]);
        for h_com in self.h_commitments.iter().skip(1) {
            acc_xn = mul_bounded_scalars(layouter, scalar_chip, &acc_xn, &xn)?;
            h_commitment.add_term(&acc_xn, h_com);
        }

        Ok(Evaluated {
            h_commitment,
            random_poly_commitment: self.random_poly_commitment.clone(),
            expected_h_eval,
            random_eval: self.random_eval.clone(),
        })
    }
}

impl<C: SelfEmulationCurve> Evaluated<C> {
    pub(crate) fn queries(
        &self,
        one: &AssignedBoundedScalar<C>, // 1
        x: &AssignedScalar<C>,          // evaluation point x
    ) -> Vec<VerifierQuery<C>> {
        vec![
            VerifierQuery::new_from_msm(x, &self.h_commitment, &self.expected_h_eval),
            VerifierQuery::new(one, x, &self.random_poly_commitment, &self.random_eval),
        ]
    }
}
