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

use ff::Field;
use midnight_curves::Fq as F;
use midnight_proofs::{
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem},
};

use super::{layout::pow2, *};
use crate::{
    field::{AssignNative, NativeConfig},
    utils::util::FromScratch,
};

const T: usize = 8;
const NUM_GROUPS: usize = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Load,
    SkipLoad,
    RecordAfterLoad,
    LoadTwice,
    /// Another chip built on the same configuration loads.
    LoadOther,
}

/// Values with the bounds `n` they are asserted against, in order.
struct TestCircuit {
    inputs: Vec<(F, Vec<usize>)>,
    mode: Mode,
}

impl Circuit<F> for TestCircuit {
    type Config = (RangeCheckConfig<F>, Column<Advice>, NativeConfig);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = (0..5 * NUM_GROUPS).map(|_| meta.advice_column()).collect();
        let fixed = (0..NUM_GROUPS + 3).map(|_| meta.fixed_column()).collect();
        let input = meta.advice_column();
        meta.enable_equality(input);
        let instances = [meta.instance_column(), meta.instance_column()];
        let native = NativeChip::configure_from_scratch(meta, &mut vec![], &mut vec![], &instances);
        (
            RangeCheckChip::configure(meta, &(advice, fixed, T)),
            input,
            native,
        )
    }

    fn synthesize(
        &self,
        (config, input, native): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = RangeCheckChip::<F>::new(&config, &NativeChip::new_from_scratch(&native));
        let xs = layouter.assign_region(
            || "inputs",
            |mut region| {
                (self.inputs.iter().enumerate())
                    .map(|(i, (x, _))| region.assign_native(|| "x", input, i, || Value::known(*x)))
                    .collect::<Result<Vec<_>, _>>()
            },
        )?;
        let record = |layouter: &mut _| {
            (xs.iter().zip(&self.inputs)).try_for_each(|(x, (_, ns))| {
                ns.iter().try_for_each(|&n| chip.assert_lower_than_pow2(layouter, x, n))
            })
        };
        match self.mode {
            Mode::Load => record(&mut layouter).and_then(|_| chip.load(&mut layouter)),
            Mode::SkipLoad => record(&mut layouter),
            Mode::RecordAfterLoad => chip.load(&mut layouter).and_then(|_| record(&mut layouter)),
            Mode::LoadTwice => {
                record(&mut layouter)?;
                chip.load(&mut layouter).and_then(|_| chip.load(&mut layouter))
            }
            Mode::LoadOther => {
                record(&mut layouter)?;
                RangeCheckChip::<F>::new(&config, &NativeChip::new_from_scratch(&native))
                    .load(&mut layouter)
            }
        }
    }
}

fn satisfied(inputs: Vec<(F, Vec<usize>)>, mode: Mode) -> bool {
    MockProver::run(&TestCircuit { inputs, mode }, vec![vec![], vec![]])
        .is_ok_and(|prover| prover.verify().is_ok())
}

/// Short checks, values of one group with every kind of top limb, chains of
/// up to three rows, and bounds split in limbs of equal and unequal sizes.
const SIZES: [usize; 13] = [0, 1, 5, 8, 25, 26, 32, 64, 96, 9, 16, 24, 40];

#[test]
fn in_range() {
    let inputs = SIZES
        .iter()
        .flat_map(|&n| {
            [
                (F::ZERO, vec![n]),
                (pow2::<F>(n) - F::ONE, vec![n]),
                (F::from((n > 0) as u64), vec![n]),
            ]
        })
        .chain([(pow2::<F>(25) - F::ONE, vec![32, 25]), (F::ZERO, vec![0])])
        .collect();
    assert!(satisfied(inputs, Mode::Load));
}

#[test]
fn out_of_range() {
    for n in SIZES {
        assert!(
            !satisfied(vec![(pow2::<F>(n), vec![n])], Mode::Load),
            "2^{n} < 2^{n}"
        );
    }
    // The tightest of several bounds is enforced.
    assert!(!satisfied(vec![(pow2::<F>(25), vec![32, 25])], Mode::Load));
}

#[test]
fn loading() {
    let inputs = vec![(F::ONE, vec![1])];
    assert!(!satisfied(inputs.clone(), Mode::SkipLoad));
    assert!(!satisfied(inputs.clone(), Mode::RecordAfterLoad));
    assert!(satisfied(inputs, Mode::LoadTwice));
}

#[test]
fn shared_between_chips() {
    assert!(satisfied(vec![(F::ONE, vec![8])], Mode::LoadOther));
    assert!(!satisfied(vec![(pow2::<F>(8), vec![8])], Mode::LoadOther));
}
