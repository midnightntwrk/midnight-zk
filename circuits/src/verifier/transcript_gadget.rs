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

//! Transcript gadget module, for in-circuit Fiat-Shamir.
//! Shall we adopt the [SAFE API](https://hackmd.io/bHgsH6mMStCVibM_wYvb2w)?

use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    transcript::{CircuitTranscript, Transcript},
};

use crate::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{
        AssignmentInstructions, EccInstructions, PublicInputInstructions, SpongeInstructions,
    },
    types::AssignedNative,
    verifier::{
        types::{AssignedPoint, AssignedScalar, CurveChip, ScalarChip, SpongeChip, SpongeState},
        SelfEmulationCurve,
    },
};

/// Gadget used to run the transcript reader in-circuit.
#[derive(Clone, Debug)]
pub struct TranscriptGadget<C: SelfEmulationCurve> {
    native_chip: ScalarChip<C>,
    curve_chip: CurveChip<C>,
    sponge_chip: SpongeChip<C>,
    sponge_state: Option<SpongeState<C>>,
    // Track the number of field elements we have in the buffer.
    input_len: usize,
    // Transcript reader is included, to help parse the proof. This parsing
    // *does not* need to be verified in-circuit.
    transcript_reader: Option<CircuitTranscript<PoseidonState<C::ScalarExt>>>,
}

impl<C: SelfEmulationCurve> TranscriptGadget<C> {
    /// Creates a new `TranscriptGadget` from the corresponding chips.
    pub fn new(
        scalar_chip: &ScalarChip<C>,
        ecc_chip: &CurveChip<C>,
        poseidon_chip: &PoseidonChip<C::Scalar>,
    ) -> Self {
        Self {
            native_chip: scalar_chip.clone(),
            curve_chip: ecc_chip.clone(),
            sponge_chip: poseidon_chip.clone(),
            sponge_state: None,
            input_len: 0,
            transcript_reader: None,
        }
    }

    /// Initialises the `TranscriptGadget`, by initialising the sponge buffer,
    /// from a given witnessed proof in the form of `Value<Vec<u8>>`.
    pub fn init_with_proof(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        proof: Value<Vec<u8>>,
    ) -> Result<(), Error> {
        self.sponge_state = Some(self.sponge_chip.init(layouter, None)?);

        // Unwrapping the witness. The amount of points read from the proof is
        // fixed for a given `Architecture`, and does not depend on the size of
        // the proof.
        // The caveat with this approach is that our in-circuit verifier will not
        // be able to verify that the proof did not include extra bytes after
        // all the relevant bytes have been read. This is not an issue anyway.
        let mut proof_bytes = Vec::new();
        proof.clone().map(|pi| proof_bytes.extend_from_slice(&pi));
        self.transcript_reader = Some(CircuitTranscript::init_from_bytes(&proof_bytes));

        Ok(())
    }

    /// Absorbs a scalar into the transcript.
    pub fn common_scalar(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        scalar: &AssignedScalar<C>,
    ) -> Result<(), Error> {
        self.input_len += 1;
        let state = self
            .sponge_state
            .as_mut()
            .expect("You must init the transcript gadget");
        self.sponge_chip.absorb(layouter, state, &[scalar.clone()])
    }

    /// Absorbs a point into the transcript.
    pub fn common_point(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
        point: &AssignedPoint<C>,
    ) -> Result<(), Error> {
        let x_as_public_input = self
            .curve_chip
            .base_field_chip()
            .as_public_input(layouter, &self.curve_chip.x_coordinate(point))?;

        let y_as_public_input = self
            .curve_chip
            .base_field_chip()
            .as_public_input(layouter, &self.curve_chip.y_coordinate(point))?;

        let pis = [x_as_public_input, y_as_public_input]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        self.input_len += pis.len();

        let state = self
            .sponge_state
            .as_mut()
            .expect("You must init the transcript gadget");
        self.sponge_chip.absorb(layouter, state, &pis)
    }

    /// Derives a scalar challenge from the current transcript.
    pub fn squeeze_challenge(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
    ) -> Result<AssignedNative<C::ScalarExt>, Error> {
        let state = self
            .sponge_state
            .as_mut()
            .expect("You must init the transcript gadget");
        self.sponge_chip.squeeze(layouter, state)
    }

    /// Reads a point from the reader buffer, and adds it to the transcript.
    /// Think of the read point as a witness freely chosen by the prover.
    pub fn read_point(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
    ) -> Result<AssignedPoint<C>, Error> {
        let reader = self
            .transcript_reader
            .as_mut()
            .expect("You must init the transcript gadget");
        // If an error, do not fail, assign a default point instead.
        // (This allows us to parse dummy proofs.)
        let point: Value<C> = match reader.read::<C::G1Affine>() {
            Ok(point) => Value::known(point.into()),
            Err(_) => Value::known(C::default()),
        };

        let assigned_point = self.curve_chip.assign(layouter, point)?;
        self.common_point(layouter, &assigned_point)?;

        Ok(assigned_point)
    }

    /// Reads a scalar from the reader buffer, and adds it to the transcript.
    /// Think of the read scalar as a witness freely chosen by the prover.
    pub fn read_scalar(
        &mut self,
        layouter: &mut impl Layouter<C::ScalarExt>,
    ) -> Result<AssignedScalar<C>, Error> {
        let reader = self
            .transcript_reader
            .as_mut()
            .expect("You must init the transcript gadget");
        // If an error, do not fail, assign a default scalar instead.
        // (This allows us to parse dummy proofs.)
        let scalar: Value<C::ScalarExt> = match reader.read::<C::ScalarExt>() {
            Ok(scalar) => Value::known(scalar),
            Err(_) => Value::known(C::ScalarExt::ZERO),
        };

        let assigned_scalar = self.native_chip.assign(layouter, scalar)?;
        self.common_scalar(layouter, &assigned_scalar)?;

        Ok(assigned_scalar)
    }
}

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::{Column, ConstraintSystem, Instance};

#[cfg(any(test, feature = "testing"))]
use crate::{
    ecc::foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
    field::decomposition::pow2range::Pow2RangeChip,
    field::native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    field::{decomposition::chip::P2RDecompositionConfig, NativeConfig},
    hash::poseidon::{PoseidonConfig, NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS},
    testing_utils::FromScratch,
    utils::ComposableChip,
    verifier::types::BaseChip,
};

#[cfg(any(test, feature = "testing"))]
impl<C: SelfEmulationCurve> FromScratch<C::Scalar> for TranscriptGadget<C> {
    type Config = (
        NativeConfig,
        P2RDecompositionConfig,
        ForeignEccConfig<C>,
        PoseidonConfig<C::Scalar>,
    );

    fn new_from_scratch(config: &Self::Config) -> Self {
        let max_bit_len = 8;
        let native_chip = NativeChip::new_from_scratch(&config.0);
        let core_decomp_chip = P2RDecompositionChip::new(&config.1, &max_bit_len);
        let native_gadget = NativeGadget::new(core_decomp_chip.clone(), native_chip.clone());
        let scalar_chip = NativeGadget::new(core_decomp_chip, native_chip);
        let curve_chip = { ForeignEccChip::new(&config.2, &scalar_chip, &scalar_chip) };
        let poseidon_chip = PoseidonChip::new(&config.3, &native_gadget);
        TranscriptGadget::new(&scalar_chip, &curve_chip, &poseidon_chip)
    }

    fn load_from_scratch(layouter: &mut impl Layouter<C::Scalar>, config: &Self::Config) {
        let max_bit_len = 8;
        let pow2range_config = config.1.clone().pow2range_config;
        let pow2range_chip = Pow2RangeChip::new(&pow2range_config, max_bit_len);
        let _ = pow2range_chip.load_table(layouter);
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<C::Scalar>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        let nb_advice_cols = nb_foreign_ecc_chip_columns::<C::Scalar, C, C, ScalarChip<C>>();
        let nb_fixed_cols = NB_ARITH_FIXED_COLS;
        let advice_columns: Vec<_> = (0..nb_advice_cols).map(|_| meta.advice_column()).collect();
        let fixed_columns: Vec<_> = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect();
        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_columns[..].try_into().unwrap(),
                *instance_columns,
            ),
        );
        let core_decomp_config = {
            let pow2conf = Pow2RangeChip::configure(meta, &advice_columns[1..NB_ARITH_COLS]);
            P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2conf))
        };

        let curve_config = {
            let base_config = BaseChip::<C>::configure(meta, &advice_columns);
            CurveChip::<C>::configure(meta, &base_config, &advice_columns)
        };

        let poseidon_config = PoseidonChip::configure(
            meta,
            &(
                advice_columns[..NB_POSEIDON_ADVICE_COLS]
                    .try_into()
                    .unwrap(),
                fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
            ),
        );

        (
            native_config,
            core_decomp_config,
            curve_config,
            poseidon_config,
        )
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use group::Group;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
        transcript::{CircuitTranscript, Transcript},
    };
    use rand::rngs::OsRng;

    use super::*;
    use crate::{
        ecc::foreign::ForeignEccConfig,
        field::{decomposition::chip::P2RDecompositionConfig, NativeConfig},
        hash::poseidon::PoseidonConfig,
        instructions::PublicInputInstructions,
    };

    const SIZE: usize = 12;

    type C = blstrs::G1Projective;
    type F = blstrs::Fq;

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        points: Value<[C; SIZE]>,
        scalars: Value<[F; SIZE]>,
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> (
        NativeConfig,
        P2RDecompositionConfig,
        ForeignEccConfig<C>,
        PoseidonConfig<F>,
    ) {
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();
        TranscriptGadget::configure_from_scratch(
            meta,
            &[committed_instance_column, instance_column],
        )
    }

    impl Circuit<F> for TestCircuit {
        type Config = <TranscriptGadget<C> as FromScratch<F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            TestCircuit::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut transcript_gadget = TranscriptGadget::new_from_scratch(&config);
            transcript_gadget.init_with_proof(&mut layouter, Value::unknown())?;

            TranscriptGadget::load_from_scratch(&mut layouter, &config);

            let assigned_scalars = transcript_gadget
                .native_chip
                .assign_many(&mut layouter, &self.scalars.transpose_array())?;

            let assigned_points = transcript_gadget
                .curve_chip
                .assign_many(&mut layouter, &self.points.transpose_array())?;

            for i in 0..(SIZE / 2) {
                transcript_gadget.common_scalar(&mut layouter, &assigned_scalars[i])?;
                transcript_gadget.common_point(&mut layouter, &assigned_points[i])?;
            }

            let challenge_1 = transcript_gadget.squeeze_challenge(&mut layouter)?;
            transcript_gadget
                .native_chip
                .constrain_as_public_input(&mut layouter, &challenge_1)?;

            for i in (SIZE / 2)..SIZE {
                transcript_gadget.common_scalar(&mut layouter, &assigned_scalars[i])?;
                transcript_gadget.common_point(&mut layouter, &assigned_points[i])?;
            }

            let challenge_2 = transcript_gadget.squeeze_challenge(&mut layouter)?;
            transcript_gadget
                .native_chip
                .constrain_as_public_input(&mut layouter, &challenge_2)
        }
    }

    #[test]
    fn test_transcript_gadget() {
        let scalars: [F; SIZE] = core::array::from_fn(|_| F::random(OsRng));
        let points: [C; SIZE] = core::array::from_fn(|_| C::random(OsRng));

        let circuit = TestCircuit {
            points: Value::known(points),
            scalars: Value::known(scalars),
        };

        let mut off_circuit_transcript = CircuitTranscript::<PoseidonState<F>>::init();

        for i in 0..(SIZE / 2) {
            off_circuit_transcript.common(&scalars[i]).unwrap();
            off_circuit_transcript
                .common::<blstrs::G1Affine>(&points[i].into())
                .unwrap();
        }

        let challenge_1: F = off_circuit_transcript.squeeze_challenge();

        for i in (SIZE / 2)..SIZE {
            off_circuit_transcript.common(&scalars[i]).unwrap();
            off_circuit_transcript
                .common::<blstrs::G1Affine>(&points[i].into())
                .unwrap();
        }

        let challenge_2 = off_circuit_transcript.squeeze_challenge();

        let k = 12;
        let public_inputs = vec![vec![], vec![challenge_1, challenge_2]];
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        prover.assert_satisfied();
    }
}
