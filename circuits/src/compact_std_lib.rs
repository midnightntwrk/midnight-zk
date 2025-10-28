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

//! A collection of a full set of functionalities needed by compact &
//! other components of Midnight's stack.
//!
//! This library uses a fixed configuration, meaning that regardless of what one
//! uses, it will always consist of the same columns, lookups, permutation
//! enabled columns, or gates. The motivation for this is twofold:
//!
//! * It facilitates recursion (we always aggregate circuits that have the same
//!   verification logic).
//!
//! * We could optimise the verifier, who can store part of the circuit
//!   description in memory and does not need to reproduce it everytime it
//!   receives a new proof.

use std::{cell::RefCell, cmp::max, convert::TryInto, fmt::Debug, io, rc::Rc};

#[cfg(all(test, feature = "bench-internal"))]
use bench_macros::inner_bench;
use bincode::{config::standard, Decode, Encode};
use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Group};
use halo2curves::secp256k1::{self, Secp256k1};
use midnight_curves::{G1Affine, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::cost_model::{circuit_model, CircuitModel},
    plonk::{k_from_circuit, prepare, Circuit, ConstraintSystem, Error, ProvingKey, VerifyingKey},
    poly::{
        commitment::{Guard, Params},
        kzg::{
            params::{ParamsKZG, ParamsVerifierKZG},
            KZGCommitmentScheme,
        },
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript, TranscriptHash},
    utils::SerdeFormat,
};
use num_bigint::BigUint;
use rand::{CryptoRng, RngCore};

use crate::{
    biguint::biguint_gadget::BigUintGadget,
    ecc::{
        foreign::{nb_foreign_ecc_chip_columns, ForeignEccChip, ForeignEccConfig},
        hash_to_curve::HashToCurveGadget,
        native::{EccChip, EccConfig, NB_EDWARDS_COLS},
    },
    field::{
        decomposition::{
            chip::{P2RDecompositionChip, P2RDecompositionConfig},
            pow2range::Pow2RangeChip,
        },
        foreign::{
            nb_field_chip_columns, params::MultiEmulationParams as MEP, FieldChip, FieldChipConfig,
        },
        native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
        NativeChip, NativeConfig, NativeGadget,
    },
    hash::{
        poseidon::{PoseidonChip, PoseidonConfig, NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS},
        sha256::{Sha256Chip, Sha256Config, NB_SHA256_ADVICE_COLS, NB_SHA256_FIXED_COLS},
        sha512::{Sha512Chip, Sha512Config, NB_SHA512_ADVICE_COLS, NB_SHA512_FIXED_COLS},
    },
    instructions::{public_input::CommittedInstanceInstructions, *},
    map::map_gadget::MapGadget,
    parsing::{
        self,
        automaton_chip::{AutomatonChip, AutomatonConfig, NB_AUTOMATA_COLS},
        Base64Chip, Base64Config, ParserGadget, StdLibParser, NB_BASE64_ADVICE_COLS,
    },
    types::{
        AssignedBit, AssignedByte, AssignedNative, AssignedNativePoint, InnerValue, Instantiable,
    },
    utils::{BlstPLONK, ComposableChip},
    vec::{vector_gadget::VectorGadget, AssignedVector, Vectorizable},
};

type C = midnight_curves::JubjubExtended;
type F = midnight_curves::Fq;

// Type aliases, for readability.
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
type Secp256k1BaseChip = FieldChip<F, secp256k1::Fp, MEP, NG>;
type Secp256k1ScalarChip = FieldChip<F, secp256k1::Fq, MEP, NG>;
type Secp256k1Chip = ForeignEccChip<F, Secp256k1, MEP, Secp256k1ScalarChip, NG>;
type Bls12381BaseChip = FieldChip<F, midnight_curves::Fp, MEP, NG>;
type Bls12381Chip = ForeignEccChip<F, midnight_curves::G1Projective, MEP, NG, NG>;

const ZKSTD_VERSION: u32 = 1;

/// Architecture of the standard library. Specifies what chips need to be
/// configured.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Encode, Decode)]
pub struct ZkStdLibArch {
    /// Enable the Jubjub chip?
    pub jubjub: bool,

    /// Enable the Poseidon chip?
    pub poseidon: bool,

    /// Enable the SHA256 chip?
    pub sha256: bool,

    /// Enable the SHA512 chip?
    pub sha512: bool,

    /// Enable the Secp256k1 chip?
    pub secp256k1: bool,

    /// Enable BLS12-381 chip?
    pub bls12_381: bool,

    /// Enable base64 chip?
    pub base64: bool,

    /// Number of parallel lookups for range checks.
    pub nr_pow2range_cols: u8,

    /// Enable automaton?
    pub automaton: bool,
}

impl Default for ZkStdLibArch {
    fn default() -> Self {
        ZkStdLibArch {
            jubjub: true,
            poseidon: true,
            sha256: true,
            sha512: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            nr_pow2range_cols: 1,
            automaton: false,
        }
    }
}

impl ZkStdLibArch {
    /// Writes the ZKStd architecture to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&ZKSTD_VERSION.to_le_bytes())?;
        bincode::encode_into_std_write(self, writer, standard())
            .map(|_| ())
            .map_err(io::Error::other)
    }

    /// Reads the ZkStd architecture from a buffer.
    pub fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let mut version = [0u8; 4];
        reader.read_exact(&mut version)?;
        let version = u32::from_le_bytes(version);
        match version {
            1 => bincode::decode_from_std_read(reader, standard())
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e)),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Unsupported ZKStd version: {}", version),
            )),
        }
    }

    /// Reads the ZkStdArchitecture from a buffer where a MidnightVK was
    /// serialized. This enables the reader to know the architecture without
    /// the need of deserializing the full verifying key.
    pub fn read_from_serialized_vk<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        // The current serialization of the verifying key places the architecture at
        // the beginning.
        Self::read(reader)
    }

    /// Returns a tuple `(points_in_proof, points_in_vk, points_in_final_msm)`
    /// where:
    ///
    /// * `points_in_proof`: total number of EC points deserialized when reading
    ///   a proof for this relation.
    /// * `points_in_vk`: total number of EC points deserialized when reading
    ///   the verifying key.
    /// * `points_in_final_msm`: number of EC points involved in the final MSM
    ///   operation during verification.
    pub fn nb_points(&self) -> (usize, usize, usize) {
        let mut cs = ConstraintSystem::default();
        let _config = ZkStdLib::configure(&mut cs, *self);

        let nb_perm_chunks =
            (cs.permutation().columns.len().saturating_sub(1) / cs.degree().saturating_sub(2)) + 1;

        let points_in_proof = cs.num_advice_columns() +
            cs.lookups().len() * 3 +
            nb_perm_chunks +
            cs.degree() + // chunks of the vanishing
            2; // points in multiopen argument

        let points_in_vk =
            cs.num_fixed_columns() + cs.num_selectors() + cs.permutation().columns.len();

        let points_in_final_msm = points_in_proof + points_in_vk + 1; // + 1 comes from the the generator in the final check

        (points_in_proof, points_in_vk, points_in_final_msm)
    }
}

#[derive(Debug, Clone)]
/// Configured chips for [ZkStdLib].
pub struct ZkStdLibConfig {
    native_config: NativeConfig,
    core_decomposition_config: P2RDecompositionConfig,
    jubjub_config: Option<EccConfig>,
    sha256_config: Option<Sha256Config>,
    sha512_config: Option<Sha512Config>,
    poseidon_config: Option<PoseidonConfig<midnight_curves::Fq>>,
    secp256k1_scalar_config: Option<FieldChipConfig>,
    secp256k1_config: Option<ForeignEccConfig<Secp256k1>>,
    bls12_381_config: Option<ForeignEccConfig<midnight_curves::G1Projective>>,
    base64_config: Option<Base64Config>,
    automaton_config: Option<AutomatonConfig<StdLibParser, midnight_curves::Fq>>,
}

/// The `ZkStdLib` exposes all tools that are used in circuit generation.
#[derive(Clone, Debug)]
#[allow(clippy::type_complexity)]
pub struct ZkStdLib {
    native_gadget: NG,
    core_decomposition_chip: P2RDecompositionChip<F>,
    jubjub_chip: Option<EccChip<C>>,
    sha256_chip: Option<Sha256Chip<F>>,
    sha512_chip: Option<Sha512Chip<F>>,
    poseidon_gadget: Option<PoseidonChip<F>>,
    htc_gadget: Option<HashToCurveGadget<F, C, AssignedNative<F>, PoseidonChip<F>, EccChip<C>>>,
    map_gadget: Option<MapGadget<F, NG, PoseidonChip<F>>>,
    biguint_gadget: BigUintGadget<F, NG>,
    secp256k1_scalar_chip: Option<Secp256k1ScalarChip>,
    secp256k1_curve_chip: Option<Secp256k1Chip>,
    bls12_381_curve_chip: Option<Bls12381Chip>,
    base64_chip: Option<Base64Chip<F>>,
    parser_gadget: ParserGadget<F, NG>,
    vector_gadget: VectorGadget<F>,
    automaton_chip: Option<AutomatonChip<StdLibParser, F>>,

    // Flags that indicate if certain chips have been used. This way we can load the tables only
    // when necessary (thus reducing the min_k in some cases).
    used_sha256: Rc<RefCell<bool>>,
    used_sha512: Rc<RefCell<bool>>,
    used_secp256k1_scalar: Rc<RefCell<bool>>,
    used_secp256k1_curve: Rc<RefCell<bool>>,
    used_bls12_381_curve: Rc<RefCell<bool>>,
    used_base64: Rc<RefCell<bool>>,
    used_automaton: Rc<RefCell<bool>>,
}

impl ZkStdLib {
    /// Creates a new [ZkStdLib] given its config.
    pub fn new(config: &ZkStdLibConfig, max_bit_len: usize) -> Self {
        let native_chip = NativeChip::new(&config.native_config, &());
        let core_decomposition_chip =
            P2RDecompositionChip::new(&config.core_decomposition_config, &max_bit_len);
        let native_gadget = NativeGadget::new(core_decomposition_chip.clone(), native_chip.clone());
        let jubjub_chip = (config.jubjub_config.as_ref())
            .map(|jubjub_config| EccChip::new(jubjub_config, &native_gadget));
        let sha256_chip = (config.sha256_config.as_ref())
            .map(|sha256_config| Sha256Chip::new(sha256_config, &native_gadget));
        let sha512_chip = (config.sha512_config.as_ref())
            .map(|sha512_config| Sha512Chip::new(sha512_config, &native_gadget));
        let poseidon_gadget = (config.poseidon_config.as_ref())
            .map(|poseidon_config| PoseidonChip::new(poseidon_config, &native_chip));
        let htc_gadget = (jubjub_chip.as_ref())
            .zip(poseidon_gadget.as_ref())
            .map(|(ecc_chip, poseidon_gadget)| HashToCurveGadget::new(poseidon_gadget, ecc_chip));
        let biguint_gadget = BigUintGadget::new(&native_gadget);
        let map_gadget = poseidon_gadget
            .as_ref()
            .map(|poseidon_gadget| MapGadget::new(&native_gadget, poseidon_gadget));
        let secp256k1_scalar_chip = (config.secp256k1_scalar_config.as_ref())
            .map(|scalar_config| FieldChip::new(scalar_config, &native_gadget));
        let secp256k1_curve_chip = (config.secp256k1_config.as_ref())
            .zip(secp256k1_scalar_chip.as_ref())
            .map(|(curve_config, scalar_chip)| {
                ForeignEccChip::new(curve_config, &native_gadget, scalar_chip)
            });
        let bls12_381_curve_chip = (config.bls12_381_config.as_ref())
            .map(|curve_config| ForeignEccChip::new(curve_config, &native_gadget, &native_gadget));

        let base64_chip = (config.base64_config.as_ref())
            .map(|base64_config| Base64Chip::new(base64_config, &native_gadget));

        let parser_gadget = ParserGadget::new(&native_gadget);
        let vector_gadget = VectorGadget::new(&native_gadget);
        let automaton_chip =
            config.automaton_config.as_ref().map(|c| AutomatonChip::new(c, &native_gadget));

        Self {
            native_gadget,
            core_decomposition_chip,
            jubjub_chip,
            sha256_chip,
            sha512_chip,
            poseidon_gadget,
            map_gadget,
            htc_gadget,
            biguint_gadget,
            secp256k1_scalar_chip,
            secp256k1_curve_chip,
            bls12_381_curve_chip,
            base64_chip,
            parser_gadget,
            vector_gadget,
            automaton_chip,
            used_sha256: Rc::new(RefCell::new(false)),
            used_sha512: Rc::new(RefCell::new(false)),
            used_secp256k1_scalar: Rc::new(RefCell::new(false)),
            used_secp256k1_curve: Rc::new(RefCell::new(false)),
            used_bls12_381_curve: Rc::new(RefCell::new(false)),
            used_base64: Rc::new(RefCell::new(false)),
            used_automaton: Rc::new(RefCell::new(false)),
        }
    }

    /// Configure [ZkStdLib] from scratch.
    pub fn configure(meta: &mut ConstraintSystem<F>, arch: ZkStdLibArch) -> ZkStdLibConfig {
        let nb_advice_cols = [
            NB_ARITH_COLS,
            arch.nr_pow2range_cols as usize,
            arch.jubjub as usize * NB_EDWARDS_COLS,
            arch.poseidon as usize * NB_POSEIDON_ADVICE_COLS,
            arch.sha256 as usize * NB_SHA256_ADVICE_COLS,
            arch.sha512 as usize * NB_SHA512_ADVICE_COLS,
            arch.secp256k1 as usize
                * max(
                    nb_field_chip_columns::<F, secp256k1::Fq, MEP>(),
                    nb_foreign_ecc_chip_columns::<F, Secp256k1, MEP, secp256k1::Fq>(),
                ),
            arch.bls12_381 as usize
                * max(
                    nb_field_chip_columns::<F, midnight_curves::Fp, MEP>(),
                    nb_foreign_ecc_chip_columns::<
                        F,
                        midnight_curves::G1Projective,
                        MEP,
                        midnight_curves::Fp,
                    >(),
                ),
            arch.base64 as usize * NB_BASE64_ADVICE_COLS,
            NB_AUTOMATA_COLS,
        ]
        .into_iter()
        .max()
        .unwrap_or(0);

        let nb_fixed_cols = [
            NB_ARITH_FIXED_COLS,
            arch.poseidon as usize * NB_POSEIDON_FIXED_COLS,
            arch.sha256 as usize * NB_SHA256_FIXED_COLS,
            arch.sha512 as usize * NB_SHA512_FIXED_COLS,
        ]
        .into_iter()
        .max()
        .unwrap_or(0);

        let advice_columns = (0..nb_advice_cols).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed_columns = (0..nb_fixed_cols).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let committed_instance_column = meta.instance_column();
        let instance_column = meta.instance_column();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_columns[..NB_ARITH_FIXED_COLS].try_into().unwrap(),
                [committed_instance_column, instance_column],
            ),
        );

        let pow2range_config =
            Pow2RangeChip::configure(meta, &advice_columns[1..=arch.nr_pow2range_cols as usize]);

        let core_decomposition_config =
            P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2range_config));

        let jubjub_config = arch.jubjub.then(|| {
            EccChip::<C>::configure(meta, &advice_columns[..NB_EDWARDS_COLS].try_into().unwrap())
        });

        let sha256_config = arch.sha256.then(|| {
            Sha256Chip::configure(
                meta,
                &(
                    advice_columns[..NB_SHA256_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[..NB_SHA256_FIXED_COLS].try_into().unwrap(),
                ),
            )
        });

        let sha512_config = arch.sha512.then(|| {
            Sha512Chip::configure(
                meta,
                &(
                    advice_columns[..NB_SHA512_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[..NB_SHA512_FIXED_COLS].try_into().unwrap(),
                ),
            )
        });

        let poseidon_config = arch.poseidon.then(|| {
            PoseidonChip::configure(
                meta,
                &(
                    advice_columns[..NB_POSEIDON_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[..NB_POSEIDON_FIXED_COLS].try_into().unwrap(),
                ),
            )
        });

        let secp256k1_scalar_config =
            arch.secp256k1.then(|| Secp256k1ScalarChip::configure(meta, &advice_columns));

        let secp256k1_config = arch.secp256k1.then(|| {
            let base_config = Secp256k1BaseChip::configure(meta, &advice_columns);
            Secp256k1Chip::configure(meta, &base_config, &advice_columns)
        });

        let bls12_381_config = arch.bls12_381.then(|| {
            let base_config = Bls12381BaseChip::configure(meta, &advice_columns);
            Bls12381Chip::configure(meta, &base_config, &advice_columns)
        });

        let base64_config = arch.base64.then(|| {
            Base64Chip::configure(
                meta,
                advice_columns[..NB_BASE64_ADVICE_COLS].try_into().unwrap(),
            )
        });

        let automaton_config = arch.automaton.then(|| {
            AutomatonChip::configure(
                meta,
                &(
                    advice_columns[..NB_AUTOMATA_COLS].try_into().unwrap(),
                    parsing::spec_library(),
                ),
            )
        });

        ZkStdLibConfig {
            native_config,
            core_decomposition_config,
            jubjub_config,
            sha256_config,
            sha512_config,
            poseidon_config,
            secp256k1_scalar_config,
            secp256k1_config,
            bls12_381_config,
            base64_config,
            automaton_config,
        }
    }
}

impl ZkStdLib {
    /// Native EccChip.
    pub fn jubjub(&self) -> &EccChip<C> {
        self.jubjub_chip.as_ref().expect("ZkStdLibArch must enable jubjub")
    }

    /// Gadget for performing in-circuit big-unsigned integer operations.
    pub fn biguint(&self) -> &BigUintGadget<F, NG> {
        &self.biguint_gadget
    }

    /// Gadget for performing map and non-map checks
    pub fn map_gadget(&self) -> &MapGadget<F, NG, PoseidonChip<F>> {
        self.map_gadget
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable poseidon"))
    }

    /// Chip for performing in-circuit operations over the Secp256k1 scalar
    /// field.
    pub fn secp256k1_scalar(&self) -> &Secp256k1ScalarChip {
        *self.used_secp256k1_scalar.borrow_mut() = true;
        self.secp256k1_scalar_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable secp256k1"))
    }

    /// Chip for performing in-circuit operations over the Secp256k1 curve.
    pub fn secp256k1_curve(&self) -> &Secp256k1Chip {
        *self.used_secp256k1_curve.borrow_mut() = true;
        self.secp256k1_curve_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable secp256k1"))
    }

    /// Chip for performing in-circuit operations over the BLS12-381 curve.
    /// Note that this is the whole BLS curve (whose order is a 381-bits
    /// integer). If you need to work over the BLS subgroup, you may want to
    /// use [Bls12381Chip::assert_in_bls12_381_subgroup].
    pub fn bls12_381_curve(&self) -> &Bls12381Chip {
        *self.used_bls12_381_curve.borrow_mut() = true;
        self.bls12_381_curve_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable bls12_381"))
    }

    /// Chip for performing in-circuit base64 decoding.
    pub fn base64(&self) -> &Base64Chip<F> {
        *self.used_base64.borrow_mut() = true;
        self.base64_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable base64"))
    }

    /// Gadget for parsing properties of a JSON object.
    pub fn parser(&self) -> &ParserGadget<F, NG> {
        &self.parser_gadget
    }

    /// Chip for performing automaton-based parsing.
    pub fn automaton(&self) -> &AutomatonChip<StdLibParser, F> {
        *self.used_automaton.borrow_mut() = true;
        (self.automaton_chip.as_ref())
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable automaton"))
    }

    /// Assert that a given assigned bit is true.
    ///
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 13, {
    /// let input: AssignedBit<F> = chip.assign_fixed(layouter, true)?;
    /// chip.assert_true(layouter, &input)?;
    /// # });
    /// ```
    pub fn assert_true(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_gadget.assert_equal_to_fixed(layouter, input, true)
    }

    /// Assert that a given assigned bit is false
    pub fn assert_false(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedBit<F>,
    ) -> Result<(), Error> {
        self.native_gadget.assert_equal_to_fixed(layouter, input, false)
    }

    /// Returns `1` iff `x < y`.
    ///
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 13, {
    /// let x: AssignedNative<F> = chip.assign_fixed(layouter, F::from(127))?;
    /// let y: AssignedNative<F> = chip.assign_fixed(layouter, F::from(212))?;
    /// let condition = chip.lower_than(layouter, &x, &y, 8)?;
    ///
    /// chip.assert_true(layouter, &condition)?;
    /// # });
    /// ```
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If `x` or `y` are not in the range `[0, 2^n)`.
    ///
    /// ```should_panic
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 13, {
    /// let x: AssignedNative<F> = chip.assign_fixed(layouter, F::from(127))?;
    /// let y: AssignedNative<F> = chip.assign_fixed(layouter, F::from(212))?;
    /// let _condition = chip.lower_than(layouter, &x, &y, 7)?;
    /// # });
    /// ```
    ///
    /// Setting `n > (F::NUM_BITS - 1) / 2` will result in a compile-time
    /// error.
    pub fn lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        n: u32,
    ) -> Result<AssignedBit<F>, Error> {
        let bounded_x = self.native_gadget.bounded_of_element(layouter, n as usize, x)?;
        let bounded_y = self.native_gadget.bounded_of_element(layouter, n as usize, y)?;
        self.native_gadget.lower_than(layouter, &bounded_x, &bounded_y)
    }

    /// Poseidon hash from a slice of native valure into a native value.
    ///
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 13, {
    /// let x: AssignedNative<F> = chip.assign_fixed(layouter, F::from(127))?;
    /// let y: AssignedNative<F> = chip.assign_fixed(layouter, F::from(212))?;
    ///
    /// let _hash = chip.poseidon(layouter, &[x, y])?;
    /// # });
    /// ```
    pub fn poseidon(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedNative<F>],
    ) -> Result<AssignedNative<F>, Error> {
        self.poseidon_gadget
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable poseidon"))
            .hash(layouter, input)
    }

    /// Hashes a slice of assigned values into `(x, y)` coordinates which are
    /// guaranteed to be in the curve `C`. For usage, see [HashToCurveGadget].
    pub fn hash_to_curve(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[AssignedNative<F>],
    ) -> Result<AssignedNativePoint<C>, Error> {
        self.htc_gadget
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable poseidon and jubjub"))
            .hash_to_curve(layouter, inputs)
    }

    /// Sha256.
    /// Takes as input a slice of assigned bytes and returns the assigned
    /// input/output in bytes.
    /// We assume the field uses little endian encoding.
    /// ```
    /// # midnight_circuits::run_test_std_lib!(chip, layouter, 13, {
    /// let input = chip.assign_many(
    ///     layouter,
    ///     &[
    ///         Value::known(13),
    ///         Value::known(226),
    ///         Value::known(119),
    ///         Value::known(5),
    ///     ],
    /// )?;
    ///
    /// let _hash = chip.sha256(layouter, &input)?;
    /// # });
    /// ```
    pub fn sha256(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>], // F -> decompose_bytes -> hash
    ) -> Result<[AssignedByte<F>; 32], Error> {
        *self.used_sha256.borrow_mut() = true;
        self.sha256_chip
            .as_ref()
            .expect("ZkStdLibArch must enable sha256")
            .hash(layouter, input)
    }

    /// Sha512.
    pub fn sha512(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>], // F -> decompose_bytes -> hash
    ) -> Result<[AssignedByte<F>; 64], Error> {
        *self.used_sha512.borrow_mut() = true;
        self.sha512_chip
            .as_ref()
            .expect("ZkStdLibArch must enable sha512")
            .hash(layouter, input)
    }
}

impl Bls12381Chip {
    /// Asserts that the given point belongs to the BLS subgroup.
    pub fn assert_in_bls12_381_subgroup(
        &self,
        layouter: &mut impl Layouter<F>,
        p: &<Bls12381Chip as EccInstructions<F, G1Projective>>::Point,
    ) -> Result<(), Error> {
        // We exhibit a COFACTOR "root" (an element that, multiplied by the cofactor
        // results in p). This is more efficient that powering `p` to the subgroup order
        // and checking it results in the identity.
        let cofactor = F::from_raw([0x8c00aaab0000aaab, 0x396c8c005555e156, 0, 0]);
        let cofactor_root: <Bls12381Chip as EccInstructions<F, G1Projective>>::Point =
            self.assign(layouter, p.value().map(|p| p * cofactor.invert().unwrap()))?;

        let cofactor_root_times_cofactor =
            self.mul_by_constant(layouter, cofactor, &cofactor_root)?;

        self.assert_equal(layouter, p, &cofactor_root_times_cofactor)
    }
}

impl<T> AssignmentInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    T::Element: Clone,
    NG: AssignmentInstructions<F, T>,
{
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<T::Element>,
    ) -> Result<T, Error> {
        self.native_gadget.assign(layouter, value)
    }

    fn assign_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: T::Element,
    ) -> Result<T, Error> {
        self.native_gadget.assign_fixed(layouter, constant)
    }

    fn assign_many(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[Value<T::Element>],
    ) -> Result<Vec<T>, Error> {
        self.native_gadget.assign_many(layouter, values)
    }
}

impl<T> PublicInputInstructions<F, T> for ZkStdLib
where
    T: Instantiable<F>,
    T::Element: Clone,
    NG: PublicInputInstructions<F, T>,
{
    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_gadget.as_public_input(layouter, assigned)
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<(), Error> {
        self.native_gadget.constrain_as_public_input(layouter, assigned)
    }

    fn assign_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<<T>::Element>,
    ) -> Result<T, Error> {
        self.native_gadget.assign_as_public_input(layouter, value)
    }
}

impl<T> CommittedInstanceInstructions<F, T> for ZkStdLib
where
    F: PrimeField,
    T: Instantiable<F>,
    NG: CommittedInstanceInstructions<F, T>,
{
    fn constrain_as_committed_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        assigned: &T,
    ) -> Result<(), Error> {
        self.native_gadget.constrain_as_committed_public_input(layouter, assigned)
    }
}

impl<T> AssertionInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    NG: AssertionInstructions<F, T>,
{
    fn assert_equal(&self, layouter: &mut impl Layouter<F>, x: &T, y: &T) -> Result<(), Error> {
        self.native_gadget.assert_equal(layouter, x, y)
    }

    fn assert_not_equal(&self, layouter: &mut impl Layouter<F>, x: &T, y: &T) -> Result<(), Error> {
        self.native_gadget.assert_not_equal(layouter, x, y)
    }

    fn assert_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<(), Error> {
        self.native_gadget.assert_equal_to_fixed(layouter, x, constant)
    }

    fn assert_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<(), Error> {
        self.native_gadget.assert_not_equal_to_fixed(layouter, x, constant)
    }
}

impl<T> EqualityInstructions<F, T> for ZkStdLib
where
    T: InnerValue,
    NG: EqualityInstructions<F, T>,
{
    fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        y: &T,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_equal(layouter, x, y)
    }

    fn is_not_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        y: &T,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_not_equal(layouter, x, y)
    }

    fn is_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_equal_to_fixed(layouter, x, constant)
    }

    fn is_not_equal_to_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &T,
        constant: T::Element,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.is_not_equal_to_fixed(layouter, x, constant)
    }
}

impl<T1, T2> ConversionInstructions<F, T1, T2> for ZkStdLib
where
    T1: InnerValue,
    T2: InnerValue,
    NG: ConversionInstructions<F, T1, T2>,
{
    fn convert_value(&self, x: &T1::Element) -> Option<T2::Element> {
        ConversionInstructions::<_, T1, T2>::convert_value(&self.native_gadget, x)
    }

    fn convert(&self, layouter: &mut impl Layouter<F>, x: &T1) -> Result<T2, Error> {
        self.native_gadget.convert(layouter, x)
    }
}

impl CanonicityInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn le_bits_lower_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.le_bits_lower_than(layouter, bits, bound)
    }

    fn le_bits_geq_than(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
        bound: BigUint,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.le_bits_geq_than(layouter, bits, bound)
    }
}

impl DecompositionInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn assigned_to_le_bits(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits: Option<usize>,
        enforce_canonical: bool,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        self.native_gadget.assigned_to_le_bits(layouter, x, nb_bits, enforce_canonical)
    }

    fn assigned_to_le_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bytes: Option<usize>,
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        self.native_gadget.assigned_to_le_bytes(layouter, x, nb_bytes)
    }

    fn assigned_to_le_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        nb_bits_per_chunk: usize,
        nb_chunks: Option<usize>,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        self.native_gadget
            .assigned_to_le_chunks(layouter, x, nb_bits_per_chunk, nb_chunks)
    }

    fn sgn0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.sgn0(layouter, x)
    }
}

impl ArithInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn linear_combination(
        &self,
        layouter: &mut impl Layouter<F>,
        terms: &[(F, AssignedNative<F>)],
        constant: F,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.linear_combination(layouter, terms, constant)
    }

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
        multiplying_constant: Option<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.mul(layouter, x, y, multiplying_constant)
    }

    fn div(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        y: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.div(layouter, x, y)
    }

    fn inv(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.inv(layouter, x)
    }

    fn inv0(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.inv0(layouter, x)
    }
}

impl ZeroInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl<Assigned> ControlFlowInstructions<F, Assigned> for ZkStdLib
where
    Assigned: InnerValue,
    NG: ControlFlowInstructions<F, Assigned>,
{
    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<Assigned, Error> {
        self.native_gadget.select(layouter, cond, x, y)
    }

    fn cond_swap(
        &self,
        layouter: &mut impl Layouter<F>,
        cond: &AssignedBit<F>,
        x: &Assigned,
        y: &Assigned,
    ) -> Result<(Assigned, Assigned), Error> {
        self.native_gadget.cond_swap(layouter, cond, x, y)
    }
}

impl FieldInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn order(&self) -> BigUint {
        self.native_gadget.order()
    }
}

impl RangeCheckInstructions<F, AssignedNative<F>> for ZkStdLib {
    fn assign_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
        bound: &BigUint,
    ) -> Result<AssignedNative<F>, Error> {
        self.native_gadget.assign_lower_than_fixed(layouter, value, bound)
    }

    fn assert_lower_than_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        x: &AssignedNative<F>,
        bound: &BigUint,
    ) -> Result<(), Error> {
        self.native_gadget.assert_lower_than_fixed(layouter, x, bound)
    }
}

impl DivisionInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl BinaryInstructions<F> for ZkStdLib {
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.and(layouter, bits)
    }

    fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.or(layouter, bits)
    }

    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        bits: &[AssignedBit<F>],
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.xor(layouter, bits)
    }

    fn not(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: &AssignedBit<F>,
    ) -> Result<AssignedBit<F>, Error> {
        self.native_gadget.not(layouter, bit)
    }
}

impl BitwiseInstructions<F, AssignedNative<F>> for ZkStdLib {}

impl<const M: usize, const A: usize, T> VectorInstructions<F, T, M, A> for ZkStdLib
where
    T: Vectorizable,
    T::Element: Copy,
    NG: AssignmentInstructions<F, T> + ControlFlowInstructions<F, T>,
{
    fn trim_beginning(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
        n_elems: usize,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        self.vector_gadget.trim_beginning(layouter, input, n_elems)
    }

    fn padding_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<[AssignedBit<F>; M], Error> {
        self.vector_gadget.padding_flag(layouter, input)
    }

    fn get_limits(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, T, M, A>,
    ) -> Result<(AssignedNative<F>, AssignedNative<F>), Error> {
        self.vector_gadget.get_limits(layouter, input)
    }

    fn resize<const L: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedVector<F, T, M, A>,
    ) -> Result<AssignedVector<F, T, L, A>, Error> {
        self.vector_gadget.resize(layouter, input)
    }

    fn assign_with_filler(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<Vec<<T>::Element>>,
        filler: Option<<T>::Element>,
    ) -> Result<AssignedVector<F, T, M, A>, Error> {
        self.vector_gadget.assign_with_filler(layouter, value, filler)
    }
}

/// Circuit structure which is used to create any circuit that can be compiled
/// into keys using the ZK standard library.
#[derive(Clone, Debug)]
pub struct MidnightCircuit<'a, R: Relation> {
    relation: &'a R,
    max_bit_len: u8,
    instance: Value<R::Instance>,
    witness: Value<R::Witness>,
    nb_public_inputs: Rc<RefCell<Option<usize>>>,
}

impl<'a, R: Relation> MidnightCircuit<'a, R> {
    /// A MidnightCircuit with unknown instance-witness for the given relation.
    pub fn from_relation(relation: &'a R) -> Self {
        MidnightCircuit::new(relation, Value::unknown(), Value::unknown(), None)
    }

    /// Creates a new MidnightCircuit for the given relation. If not provided,
    /// this function selects the optimal max_bit_len for the pow2range table.
    pub fn new(
        relation: &'a R,
        instance: Value<R::Instance>,
        witness: Value<R::Witness>,
        max_bit_len_opt: Option<u8>,
    ) -> Self {
        if let Some(max_bit_len) = max_bit_len_opt {
            return MidnightCircuit {
                relation,
                max_bit_len,
                instance,
                witness,
                nb_public_inputs: Rc::new(RefCell::new(None)),
            };
        }

        let model_with_max_bit_len = |max_bit_len: u8| -> CircuitModel {
            circuit_model::<_, 48, 32>(&MidnightCircuit {
                relation,
                max_bit_len,
                instance: Value::unknown(),
                witness: Value::unknown(),
                nb_public_inputs: Rc::new(RefCell::new(None)),
            })
        };

        let mut best_k = u32::MAX;
        let mut best_max_bit_len = 8;

        // Loop for finding the optimal `max_bit_len`.
        for max_bit_len in 8..25 {
            let model = model_with_max_bit_len(max_bit_len);

            if model.k < best_k {
                best_k = model.k;
                best_max_bit_len = max_bit_len;
            }

            // Stop when the table becomes the bottleneck.
            if model.rows < (1 << (max_bit_len + 1)) {
                break;
            }
        }

        MidnightCircuit {
            relation,
            max_bit_len: best_max_bit_len,
            instance,
            witness,
            nb_public_inputs: Rc::new(RefCell::new(None)),
        }
    }

    /// The minimum `k` necessary to implement this circuit.
    pub fn min_k(&self) -> u32 {
        k_from_circuit(self)
    }
}

/// A verifier key of a Midnight circuit.
#[derive(Clone, Debug)]
pub struct MidnightVK {
    architecture: ZkStdLibArch,
    max_bit_len: u8,
    nb_public_inputs: usize,
    vk: VerifyingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>>,
}

impl MidnightVK {
    /// Writes a verifying key to a buffer.
    ///
    /// Depending on the `format`:
    /// - `Processed`: Takes less space, but more time to read.
    /// - `RawBytes`: Takes more space, but faster to read.
    ///
    /// Using `RawBytesUnchecked` will have the same effect as `RawBytes`,
    /// but it is not recommended.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.architecture.write(writer)?;

        writer.write_all(&[self.max_bit_len])?;

        writer.write_all(&(self.nb_public_inputs as u32).to_le_bytes())?;

        self.vk.write(writer, format)
    }

    /// Reads a verification key from a buffer.
    ///
    /// The `format` must match the one that was used when writing the key.
    /// If the key was written with `RawBytes`, it can be read with `RawBytes`
    /// or `RawBytesUnchecked` (which is faster).
    ///
    /// # WARNING
    /// Use `RawBytesUnchecked` only if you trust the party who wrote the key.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let architecture = ZkStdLibArch::read(reader)?;

        let mut byte = [0u8; 1];
        reader.read_exact(&mut byte)?;
        let max_bit_len = byte[0];

        let mut bytes = [0u8; 4];
        reader.read_exact(&mut bytes)?;
        let nb_public_inputs = u32::from_le_bytes(bytes) as usize;

        let mut cs = ConstraintSystem::default();
        let _config = ZkStdLib::configure(&mut cs, architecture);

        let vk = VerifyingKey::read_from_cs::<R>(reader, format, cs)?;

        Ok(MidnightVK {
            architecture,
            max_bit_len,
            nb_public_inputs,
            vk,
        })
    }

    /// The size of the domain associated to this verifying key.
    pub fn k(&self) -> u8 {
        self.vk.get_domain().k() as u8
    }

    /// The underlying midnight-proofs verifying key.
    pub fn vk(
        &self,
    ) -> &VerifyingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>> {
        &self.vk
    }
}

/// A proving key of a Midnight circuit.
#[derive(Clone, Debug)]
pub struct MidnightPK<R: Relation> {
    max_bit_len: u8,
    k: u8,
    relation: R,
    pk: ProvingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>>,
}

impl<Rel: Relation> MidnightPK<Rel> {
    /// Writes a proving key to a buffer.
    ///
    /// Depending on the `format`:
    /// - `Processed`: Takes less space, but more time to read.
    /// - `RawBytes`: Takes more space, but faster to read.
    ///
    /// Using `RawBytesUnchecked` will have the same effect as `RawBytes`,
    /// but it is not recommended.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_all(&[self.max_bit_len])?;
        writer.write_all(&[self.k])?;

        Rel::write_relation(&self.relation, writer)?;

        self.pk.write(writer, format)
    }

    /// Reads a proving key from a buffer.
    ///
    /// The `format` must match the one that was used when writing the key.
    /// If the key was written with `RawBytes`, it can be read with `RawBytes`
    /// or `RawBytesUnchecked` (which is faster).
    ///
    /// # WARNING
    /// Use `RawBytesUnchecked` only if you trust the party who wrote the key.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let mut byte = [0u8; 1];

        reader.read_exact(&mut byte)?;
        let max_bit_len = byte[0];

        reader.read_exact(&mut byte)?;
        let k = byte[0];

        let relation = Rel::read_relation(reader)?;

        let pk = ProvingKey::read::<R, MidnightCircuit<Rel>>(
            reader,
            format,
            MidnightCircuit::new(
                &relation,
                Value::unknown(),
                Value::unknown(),
                Some(max_bit_len),
            )
            .params(),
        )?;

        Ok(MidnightPK {
            max_bit_len,
            k,
            relation,
            pk,
        })
    }

    /// The size of the domain associated to this proving key.
    pub fn k(&self) -> u8 {
        self.k
    }

    /// The underlying midnight-proofs proving key.
    pub fn pk(
        &self,
    ) -> &ProvingKey<midnight_curves::Fq, KZGCommitmentScheme<midnight_curves::Bls12>> {
        &self.pk
    }
}

/// Helper trait, used to abstract the circuit developer from Halo2's
/// boilerplate.
///
/// `Relation` has a default implementation for loading only the tables
/// needed for the requested chips. The developer needs to implement the
/// function [Relation::circuit], which essentially contains the
/// statement of the proof we are creating.
///
/// # Important note
///
/// The API provided here guarantees that the number of public inputs
/// used during verification matches the number of public inputs (as raw
/// scalars) declared in [Relation::circuit] through the
/// [PublicInputInstructions] interface. Proof verification will fail if
/// this requirement is not met.
///
/// # Example
///
/// ```
/// # use midnight_circuits::{
/// #     compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
/// #     instructions::{AssignmentInstructions, PublicInputInstructions},
/// #     testing_utils::plonk_api::filecoin_srs,
/// #     types::{AssignedByte, Instantiable},
/// # };
/// # use midnight_proofs::{
/// #     circuit::{Layouter, Value},
/// #     plonk::Error,
/// # };
/// # use rand::{rngs::OsRng, Rng, SeedableRng};
/// # use rand_chacha::ChaCha8Rng;
/// # use sha2::Digest;
/// #
/// type F = midnight_curves::Fq;
///
/// #[derive(Clone, Default)]
/// struct ShaPreImageCircuit;
///
/// impl Relation for ShaPreImageCircuit {
///     // When defining a circuit, one must clearly state the instance and the witness
///     // of the underlying NP-relation.
///     type Instance = [u8; 32];
///     type Witness = [u8; 24]; // 192 = 24 * 8
///
///     // We must specify how the instance is converted into raw field elements to
///     // be process by the prover/verifier. The order here must be consistent with
///     // the order in which public inputs are constrained/assigned in [circuit].
///     fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
///         Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
///     }
///
///     // Define the logic of the NP-relation being proved.
///     fn circuit(
///         &self,
///         std_lib: &ZkStdLib,
///         layouter: &mut impl Layouter<F>,
///         _instance: Value<Self::Instance>,
///         witness: Value<Self::Witness>,
///     ) -> Result<(), Error> {
///         let assigned_input = std_lib.assign_many(layouter, &witness.transpose_array())?;
///         let output = std_lib.sha256(layouter, &assigned_input)?;
///         output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
///     }
///
///     fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
///         Ok(())
///     }
///
///     fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
///         Ok(ShaPreImageCircuit)
///     }
/// }
///
/// const K: u32 = 13;
/// let mut srs = filecoin_srs(K);
///
/// let relation = ShaPreImageCircuit;
///
/// let vk = compact_std_lib::setup_vk(&mut srs, &relation);
/// let pk = compact_std_lib::setup_pk(&relation, &vk);
///
/// let mut rng = ChaCha8Rng::from_entropy();
/// let witness: [u8; 24] = core::array::from_fn(|_| rng.gen());
/// let instance = sha2::Sha256::digest(witness).into();
///
/// let proof = compact_std_lib::prove::<ShaPreImageCircuit, blake2b_simd::State>(
///     &srs, &pk, &relation, &instance, witness, OsRng,
/// )
/// .expect("Proof generation should not fail");
///
/// assert!(
///     compact_std_lib::verify::<ShaPreImageCircuit, blake2b_simd::State>(
///         &srs.verifier_params(),
///         &vk,
///         &instance,
///         None,
///         &proof
///     )
///     .is_ok()
/// )
/// ```
pub trait Relation: Clone {
    /// The instance of the NP-relation described by this circuit.
    type Instance: Clone;

    /// The witness of the NP-relation described by this circuit.
    type Witness: Clone;

    /// Produces a vector of field elements in PLONK format representing the
    /// given [Self::Instance].
    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error>;

    /// Produces a vector of field elements in PLONK format representing the
    /// data inside the committed instance.
    fn format_committed_instances(_witness: &Self::Witness) -> Vec<F> {
        vec![]
    }

    /// Defines the circuit's logic.
    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error>;

    /// Specifies what chips are enabled in the standard library. A chip needs
    /// to be enabled if it is used in [Self::circuit], but it can also be
    /// enabled even if it is not used (possibly to share the same architecture
    /// with other circuits).
    ///
    /// The blanket implementation enables:
    ///  - jubjub
    ///  - poseidon
    ///  - sha256
    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch::default()
    }

    /// Writes a relation to a buffer.
    fn write_relation<W: io::Write>(&self, writer: &mut W) -> io::Result<()>;

    /// Reads a relation from a buffer.
    fn read_relation<R: io::Read>(reader: &mut R) -> io::Result<Self>;
}

impl<R: Relation> Circuit<F> for MidnightCircuit<'_, R> {
    type Config = ZkStdLibConfig;

    // FIXME: this could be parametrised by MidnightCircuit.
    type FloorPlanner = SimpleFloorPlanner;

    type Params = ZkStdLibArch;

    fn without_witnesses(&self) -> Self {
        unreachable!()
    }

    fn params(&self) -> Self::Params {
        self.relation.used_chips()
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, arch: ZkStdLibArch) -> Self::Config {
        ZkStdLib::configure(meta, arch)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ZkStdLib::configure(meta, ZkStdLibArch::default())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let zk_std_lib = ZkStdLib::new(&config, self.max_bit_len as usize);

        self.relation.circuit(
            &zk_std_lib,
            &mut layouter.namespace(|| "Running logic circuit"),
            self.instance.clone(),
            self.witness.clone(),
        )?;

        // After the circuit function has been called, we can update the expected
        // number of raw public inputs in [Self] (via a RefCell). This number will
        // be stored in the MidnightVK so that we can make sure it matches the number of
        // public inputs provided during verification.
        *self.nb_public_inputs.borrow_mut() =
            Some(zk_std_lib.native_gadget.native_chip.nb_public_inputs());

        // We load the tables at the end, once we have figured out what chips/gadgets
        // were actually used.
        zk_std_lib.core_decomposition_chip.load(&mut layouter)?;

        if let Some(sha256_chip) = zk_std_lib.sha256_chip {
            if *zk_std_lib.used_sha256.borrow() {
                sha256_chip.load(&mut layouter)?;
            }
        }

        if let Some(sha512_chip) = zk_std_lib.sha512_chip {
            if *zk_std_lib.used_sha512.borrow() {
                sha512_chip.load(&mut layouter)?;
            }
        }

        if let Some(b64_chip) = zk_std_lib.base64_chip {
            if *zk_std_lib.used_base64.borrow() {
                b64_chip.load(&mut layouter)?;
            }
        }

        if let Some(automaton_chip) = zk_std_lib.automaton_chip {
            if *zk_std_lib.used_automaton.borrow() {
                automaton_chip.load(&mut layouter)?;
            }
        }

        Ok(())
    }
}

/// Downsizes the given SRS to the size required by the given circuit (which is
/// computed automatically). This step does not need to be done if you know that
/// the SRS already has the correct size.
pub fn downsize_srs_for_relation<R: Relation>(
    srs: &mut ParamsKZG<midnight_curves::Bls12>,
    relation: &R,
) {
    srs.downsize_from_circuit(&MidnightCircuit::from_relation(relation))
}

/// Generates a verifying key for a `MidnightCircuit<R>` circuit. Downsizes the
/// parameters to match the size of the Relation.
pub fn setup_vk<R: Relation>(
    params: &ParamsKZG<midnight_curves::Bls12>,
    relation: &R,
) -> MidnightVK {
    let circuit = MidnightCircuit::from_relation(relation);
    let vk = BlstPLONK::<MidnightCircuit<R>>::setup_vk(params, &circuit);

    // During the call to [setup_vk] the circuit RefCell on public inputs has been
    // mutated with the correct value. The following [unwrap] is safe here.
    let nb_public_inputs = circuit.nb_public_inputs.clone().borrow().unwrap();

    MidnightVK {
        architecture: relation.used_chips(),
        max_bit_len: circuit.max_bit_len,
        nb_public_inputs,
        vk,
    }
}

/// Generates a proving key for a `MidnightCircuit<R>` circuit.
pub fn setup_pk<R: Relation>(relation: &R, vk: &MidnightVK) -> MidnightPK<R> {
    let circuit = MidnightCircuit::new(
        relation,
        Value::unknown(),
        Value::unknown(),
        Some(vk.max_bit_len),
    );
    let pk = BlstPLONK::<MidnightCircuit<R>>::setup_pk(&circuit, &vk.vk);
    MidnightPK {
        max_bit_len: vk.max_bit_len,
        k: vk.vk.get_domain().k() as u8,
        relation: relation.clone(),
        pk,
    }
}

#[cfg_attr(all(test, feature = "bench-internal"), inner_bench)]
/// Produces a proof of relation `R` for the given instance (using the given
/// proving key and witness).
pub fn prove<R: Relation, H: TranscriptHash>(
    params: &ParamsKZG<midnight_curves::Bls12>,
    pk: &MidnightPK<R>,
    relation: &R,
    instance: &R::Instance,
    witness: R::Witness,
    rng: impl RngCore + CryptoRng,
) -> Result<Vec<u8>, Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    let pi = R::format_instance(instance)?;
    let com_inst = R::format_committed_instances(&witness);
    let circuit = MidnightCircuit::new(
        relation,
        Value::known(instance.clone()),
        Value::known(witness),
        Some(pk.max_bit_len),
    );
    BlstPLONK::<MidnightCircuit<R>>::prove::<H>(
        params,
        &pk.pk,
        &circuit,
        1,
        &[com_inst.as_slice(), &pi],
        rng,
        #[cfg(all(test, feature = "bench-internal"))]
        _group,
    )
}

/// Verifies the given proof of relation `R` with respect to the given instance.
/// Returns `Ok(())` if the proof is valid.
pub fn verify<R: Relation, H: TranscriptHash>(
    params_verifier: &ParamsVerifierKZG<midnight_curves::Bls12>,
    vk: &MidnightVK,
    instance: &R::Instance,
    committed_instance: Option<G1Affine>,
    proof: &[u8],
) -> Result<(), Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    let pi = R::format_instance(instance)?;
    let committed_pi = committed_instance.unwrap_or(G1Affine::identity());
    if pi.len() != vk.nb_public_inputs {
        return Err(Error::InvalidInstances);
    }
    BlstPLONK::<MidnightCircuit<R>>::verify::<H>(
        params_verifier,
        &vk.vk,
        &[committed_pi],
        &[&pi],
        proof,
    )
}

/// Verifies a batch of proofs with respect to their corresponding vk.
/// This method does not need to know the `Relation` the proofs are associated
/// to and, indeed, it can verify proofs from different `Relation`s.
/// For that, this function does not take `instance`s, but public inputs
/// in raw format (`Vec<F>`).
///
/// Returns `Ok(())` if all proofs are valid.
pub fn batch_verify<H: TranscriptHash>(
    params_verifier: &ParamsVerifierKZG<midnight_curves::Bls12>,
    vks: &[MidnightVK],
    pis: &[Vec<F>],
    proofs: &[Vec<u8>],
) -> Result<(), Error>
where
    G1Projective: Hashable<H>,
    F: Hashable<H> + Sampleable<H>,
{
    // TODO: For the moment, committed instances are not supported.
    let n = vks.len();
    if pis.len() != n || proofs.len() != n {
        // TODO: have richer types in halo2
        return Err(Error::InvalidInstances);
    }

    let mut r_transcript = CircuitTranscript::init();

    let guards = vks
        .iter()
        .zip(pis.iter())
        .zip(proofs.iter())
        .map(|((vk, pi), proof)| {
            if pi.len() != vk.nb_public_inputs {
                return Err(Error::InvalidInstances);
            }

            let mut transcript = CircuitTranscript::init_from_bytes(proof);
            let dual_msm = prepare::<
                midnight_curves::Fq,
                KZGCommitmentScheme<midnight_curves::Bls12>,
                CircuitTranscript<H>,
            >(
                &vk.vk,
                &[&[midnight_curves::G1Projective::identity()]],
                // TODO: We could batch here proofs with the same vk.
                &[&[pi]],
                &mut transcript,
            )?;
            let summary: F = transcript.squeeze_challenge();
            r_transcript.common(&summary)?;
            transcript.assert_empty().map_err(|_| Error::Opening)?;
            Ok(dual_msm)
        })
        .collect::<Result<Vec<_>, Error>>()?;

    let r = r_transcript.squeeze_challenge();

    let mut acc_guard = guards[0].clone();
    for guard in guards.into_iter().skip(1) {
        acc_guard.scale(r);
        acc_guard.add_msm(guard);
    }
    // TODO: Have richer error types
    acc_guard.verify(params_verifier).map_err(|_| Error::Opening)
}

/// Cost model of the given relation.
pub fn cost_model<R: Relation>(relation: &R) -> CircuitModel {
    let circuit = MidnightCircuit::from_relation(relation);
    circuit_model::<_, 48, 32>(&circuit)
}
