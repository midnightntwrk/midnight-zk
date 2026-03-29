// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
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

//! Shared preprocessing for foreign EC multi-scalar multiplication.

use std::{cmp::max, collections::HashMap, hash::Hash};

use ff::Field;
use group::Group;
use midnight_proofs::{circuit::Layouter, plonk::Error};

use crate::{
    ecc::curves::CircuitCurve,
    instructions::{AssignmentInstructions, EccInstructions, ScalarFieldInstructions},
    types::InnerValue,
    CircuitField,
};

/// Preprocessing of MSM inputs.
///
/// Phase 1: Filters out identity bases and separates 1-bit scalars.
/// Phase 2: Deduplicates bases and scalars known to be equal.
pub(crate) fn msm_preprocess<F, C, EI, SFI>(
    ec_chip: &EI,
    scalar_chip: &SFI,
    layouter: &mut impl Layouter<F>,
    scalars: &[(EI::Scalar, usize)],
    bases: &[EI::Point],
) -> Result<
    (
        Vec<(EI::Scalar, usize)>,
        Vec<EI::Point>,
        Vec<(EI::Point, EI::Scalar)>,
    ),
    Error,
>
where
    F: CircuitField,
    C: CircuitCurve,
    EI: EccInstructions<F, C, Scalar = SFI::Scalar> + AssignmentInstructions<F, EI::Point>,
    SFI: ScalarFieldInstructions<F>,
    SFI::Scalar: InnerValue<Element = C::ScalarField>,
    EI::Point: PartialEq + Eq + Hash,
{
    // Phase 1:
    // --------

    // Filter out bases that are known to be the identity at compile time.
    // These contribute nothing to the MSM result.
    let identity = ec_chip.assign_fixed(layouter, C::CryptographicGroup::identity())?;
    let (scalars, bases): (Vec<_>, Vec<_>) = scalars
        .iter()
        .zip(bases.iter())
        .filter(|(_, base)| *base != &identity)
        .map(|(s, b)| (s.clone(), b.clone()))
        .unzip();

    // If any of the scalars is known to be 1, or has a bound of 1 (i.e. it is
    // known to be either 0 or 1) remove it (with its base) from the list and
    // simply add it at the end.
    let one: EI::Scalar = scalar_chip.assign_fixed(layouter, C::ScalarField::ONE)?;
    let mut bases_with_1bit_scalar = vec![];
    let mut filtered_scalars = vec![];
    let mut filtered_bases = vec![];
    for (scalar, base) in scalars.iter().zip(bases.iter()) {
        if scalar.0 == one || scalar.1 == 1 {
            bases_with_1bit_scalar.push((base.clone(), scalar.0.clone()));
        } else {
            filtered_scalars.push(scalar.clone());
            filtered_bases.push(base.clone());
        }
    }

    let scalars = filtered_scalars;
    let bases = filtered_bases;

    // Phase 2:
    // --------

    // If two bases are exactly the same (as symbolic PLONK variables), we
    // deduplicate them by adding their scalars.
    let mut cache_bases: HashMap<EI::Point, (EI::Scalar, usize)> = HashMap::new();
    let mut unique_bases: Vec<EI::Point> = vec![];
    for (base, scalar) in bases.iter().zip(scalars.iter()) {
        if let Some(acc) = cache_bases.insert(base.clone(), scalar.clone()) {
            let new_scalar = scalar_chip.add(layouter, &acc.0, &scalar.0)?;
            let new_bound = max(acc.1, scalar.1) + 1;
            cache_bases.insert(base.clone(), (new_scalar, new_bound));
        } else {
            unique_bases.push(base.clone());
        }
    }
    let scalars = unique_bases
        .iter()
        .map(|b| cache_bases.get(b).unwrap().clone())
        .collect::<Vec<_>>();
    let bases = unique_bases;

    // If two scalars are exactly the same (as symbolic PLONK variables), we
    // deduplicate them by adding their bases.
    let mut cache_scalars: HashMap<(EI::Scalar, usize), EI::Point> = HashMap::new();
    let mut unique_scalars: Vec<(EI::Scalar, usize)> = vec![];
    for (scalar, base) in scalars.iter().zip(bases.iter()) {
        if let Some(acc) = cache_scalars.insert(scalar.clone(), base.clone()) {
            let new_acc = ec_chip.add(layouter, &acc, base)?;
            cache_scalars.insert(scalar.clone(), new_acc);
        } else {
            unique_scalars.push(scalar.clone());
        }
    }
    let bases = unique_scalars
        .iter()
        .map(|s| cache_scalars.get(s).unwrap().clone())
        .collect::<Vec<_>>();
    let scalars = unique_scalars;

    Ok((scalars, bases, bases_with_1bit_scalar))
}
