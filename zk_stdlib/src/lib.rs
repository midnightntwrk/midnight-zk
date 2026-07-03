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

#![doc = include_str!("../README.md")]

mod external;
mod instructions;
pub mod interface;
pub mod utils;

use std::{cell::RefCell, cmp::max, convert::TryInto, fmt::Debug, io, rc::Rc};

use bincode::{config::standard, Decode, Encode};
use blake2b::blake2b::{
    blake2b_chip::{Blake2bChip, Blake2bConfig},
    NB_BLAKE2B_ADVICE_COLS,
};
pub use interface::*;
use keccak_sha3::packed_chip::{PackedChip, PackedConfig, PACKED_ADVICE_COLS, PACKED_FIXED_COLS};
use midnight_circuits::{
    biguint::biguint_gadget::BigUintGadget,
    ecc::{
        foreign::{
            edwards_chip::{
                nb_foreign_edwards_chip_columns, ForeignEdwardsEccChip, ForeignEdwardsEccConfig,
            },
            weierstrass_chip::{
                nb_foreign_ecc_chip_columns, ForeignWeierstrassEccChip, ForeignWeierstrassEccConfig,
            },
        },
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
        native::NB_EXTRA_ARITH_FIXED_COLS,
        NativeChip, NativeConfig, NativeGadget,
    },
    hash::{
        poseidon::{
            constants::RATE, PoseidonChip, PoseidonConfig, VarLenPoseidonGadget,
            NB_POSEIDON_ADVICE_COLS, NB_POSEIDON_FIXED_COLS,
        },
        sha256::{
            Sha256Chip, Sha256Config, VarLenSha256Gadget, NB_SHA256_ADVICE_COLS,
            NB_SHA256_FIXED_COLS,
        },
        sha512::{Sha512Chip, Sha512Config, NB_SHA512_ADVICE_COLS, NB_SHA512_FIXED_COLS},
    },
    instructions::{hash::VarHashInstructions, *},
    map::map_gadget::MapGadget,
    parsing::{
        self,
        scanner::{ScannerChip, ScannerConfig, NB_SCANNER_ADVICE_COLS, NB_SCANNER_FIXED_COLS},
        Base64Chip, Base64Config, ParserGadget, NB_BASE64_ADVICE_COLS,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, AssignedNativePoint, ComposableChip},
    vec::{vector_gadget::VectorGadget, AssignedVector},
    verifier::{BlstrsEmulation, VerifierGadget},
};
use midnight_curves::{
    curve25519::{self as curve25519_mod, Curve25519},
    k256::{self as k256_mod, K256},
    p256::{self as p256_mod, P256},
    Fq,
};
use midnight_proofs::{
    circuit::Layouter,
    plonk::{ConstraintSystem, Error},
};

use crate::external::{blake2b::Blake2bWrapper, keccak_sha3::KeccakSha3Wrapper};

type C = midnight_curves::JubjubExtended;
type F = midnight_curves::Fq;

// Type aliases, for readability.
type NG = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;
type Secp256k1BaseChip = FieldChip<F, k256_mod::Fp, MEP, NG>;
type Secp256k1ScalarChip = FieldChip<F, k256_mod::Fq, MEP, NG>;
type Secp256k1Chip = ForeignWeierstrassEccChip<F, K256, MEP, Secp256k1ScalarChip, NG>;
type P256BaseChip = FieldChip<F, p256_mod::Fp, MEP, NG>;
type P256ScalarChip = FieldChip<F, p256_mod::Fq, MEP, NG>;
type P256Chip = ForeignWeierstrassEccChip<F, P256, MEP, P256ScalarChip, NG>;
type Bls12381BaseChip = FieldChip<F, midnight_curves::Fp, MEP, NG>;
type Bls12381Chip = ForeignWeierstrassEccChip<
    F,
    midnight_curves::G1Projective,
    midnight_curves::G1Projective,
    NG,
    NG,
>;
type Curve25519BaseChip = FieldChip<F, curve25519_mod::Fp, MEP, NG>;
type Curve25519ScalarChip = FieldChip<F, curve25519_mod::Scalar, MEP, NG>;
type Curve25519Chip = ForeignEdwardsEccChip<F, Curve25519, MEP, Curve25519ScalarChip, NG>;

const ZKSTD_VERSION: u32 = 2;

/// Number of instance columns given in committed form in a ZK stdlib proof.
const NB_COMMITTED_INSTANCES: usize = 1;

/// Architecture of the standard library. Specifies what chips need to be
/// configured.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Encode, Decode)]
pub struct ZkStdLibArch {
    /// Enable the Jubjub chip?
    pub jubjub: bool,

    /// Enable the Poseidon chip?
    pub poseidon: bool,

    /// Enable the SHA256 chip?
    pub sha2_256: bool,

    /// Enable the SHA512 chip?
    pub sha2_512: bool,

    /// Enable the Keccak chip? (third-party implementation)
    ///
    /// Note: is configured using the same columns and tables as sha3_256,
    /// meaning enabling either of the two, or both, requires the same
    /// configuration resources.
    pub keccak_256: bool,

    /// Enable the Sha3 chip? (third-party implementation)
    ///
    /// Note: is configured using the same columns and tables as keccak_256,
    /// meaning enabling either of the two, or both, requires the same
    /// configuration resources.
    pub sha3_256: bool,

    /// Enable the Blake2b chip? (third-party implementation)
    pub blake2b: bool,

    /// Enable the Secp256k1 chip?
    pub secp256k1: bool,

    /// Enable the P256 chip?
    pub p256: bool,

    /// Enable BLS12-381 chip?
    pub bls12_381: bool,

    /// Enable Curve25519 chip?
    pub curve25519: bool,

    /// Enable base64 chip?
    pub base64: bool,

    /// Enable scanner chip (automaton-based parsing and substring checks)?
    pub automaton: bool,

    /// Number of columns for the arithmetic identity. The higher, the more
    /// terms can be added in a single row. This number also limits the number
    /// of range-check parallel lookups.
    ///
    /// Must be at least 5.
    pub nb_arith_cols: u8,

    /// Number of parallel lookups for range checks.
    ///
    /// Must be strictly smaller than `nb_arith_cols`.
    pub nr_pow2range_cols: u8,
}

impl Default for ZkStdLibArch {
    fn default() -> Self {
        ZkStdLibArch {
            jubjub: false,
            poseidon: false,
            sha2_256: false,
            sha2_512: false,
            sha3_256: false,
            keccak_256: false,
            blake2b: false,
            secp256k1: false,
            p256: false,
            bls12_381: false,
            curve25519: false,
            base64: false,
            automaton: false,
            nb_arith_cols: 5,
            nr_pow2range_cols: 1,
        }
    }
}

/// Serialized layout of [`ZkStdLibArch`] as it existed in
/// `midnight-zk-stdlib` v1.0.0 (ZKSTD_VERSION 1). Used only for migration
/// when reading old serialized verifying keys.
#[derive(Decode)]
struct ZkStdLibArchV1 {
    jubjub: bool,
    poseidon: bool,
    sha2_256: bool,
    sha2_512: bool,
    keccak_256: bool,
    sha3_256: bool,
    blake2b: bool,
    secp256k1: bool,
    bls12_381: bool,
    base64: bool,
    automaton: bool,
    nr_pow2range_cols: u8,
}

impl From<ZkStdLibArchV1> for ZkStdLibArch {
    fn from(v1: ZkStdLibArchV1) -> Self {
        ZkStdLibArch {
            jubjub: v1.jubjub,
            poseidon: v1.poseidon,
            sha2_256: v1.sha2_256,
            sha2_512: v1.sha2_512,
            keccak_256: v1.keccak_256,
            sha3_256: v1.sha3_256,
            blake2b: v1.blake2b,
            secp256k1: v1.secp256k1,
            p256: false,
            bls12_381: v1.bls12_381,
            curve25519: false,
            base64: v1.base64,
            automaton: v1.automaton,
            nb_arith_cols: 5,
            nr_pow2range_cols: v1.nr_pow2range_cols,
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
            1 => bincode::decode_from_std_read::<ZkStdLibArchV1, _, _>(reader, standard())
                .map(ZkStdLibArch::from)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e)),
            2 => bincode::decode_from_std_read(reader, standard())
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e)),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Unsupported ZKStd version: {}", version),
            )),
        }
    }

    /// Reads the ZkStdLib architecture from a buffer where a MidnightVK was
    /// serialized. This enables the reader to know the architecture without
    /// the need of deserializing the full verifying key.
    pub fn read_from_serialized_vk<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        // The current serialization of the verifying key places the architecture at
        // the beginning.
        Self::read(reader)
    }
}

#[derive(Debug, Clone)]
/// Configured chips for [ZkStdLib].
pub struct ZkStdLibConfig {
    native_config: NativeConfig,
    core_decomposition_config: P2RDecompositionConfig,
    jubjub_config: Option<EccConfig>,
    sha2_256_config: Option<Sha256Config>,
    sha2_512_config: Option<Sha512Config>,
    poseidon_config: Option<PoseidonConfig<midnight_curves::Fq>>,
    secp256k1_scalar_config: Option<FieldChipConfig>,
    secp256k1_config: Option<ForeignWeierstrassEccConfig<K256>>,
    p256_scalar_config: Option<FieldChipConfig>,
    p256_config: Option<ForeignWeierstrassEccConfig<P256>>,
    bls12_381_config: Option<ForeignWeierstrassEccConfig<midnight_curves::G1Projective>>,
    curve25519_scalar_config: Option<FieldChipConfig>,
    curve25519_config: Option<ForeignEdwardsEccConfig<Curve25519>>,
    base64_config: Option<Base64Config>,
    scanner_config: Option<ScannerConfig>,

    // Configuration of external libraries.
    keccak_sha3_config: Option<PackedConfig>,
    blake2b_config: Option<Blake2bConfig>,
}

/// The `ZkStdLib` exposes all tools that are used in circuit generation.
#[derive(Clone, Debug)]
#[allow(clippy::type_complexity)]
pub struct ZkStdLib {
    // Internal chips and gadgets.
    native_gadget: NG,
    core_decomposition_chip: P2RDecompositionChip<F>,
    jubjub_chip: Option<EccChip<C>>,
    sha2_256_chip: Option<Sha256Chip<F>>,
    varlen_sha2_256_gadget: Option<VarLenSha256Gadget<F>>,
    sha2_512_chip: Option<Sha512Chip<F>>,
    poseidon_gadget: Option<PoseidonChip<F>>,
    varlen_poseidon_gadget: Option<VarLenPoseidonGadget<F>>,
    htc_gadget: Option<HashToCurveGadget<F, C, AssignedNative<F>, PoseidonChip<F>, EccChip<C>>>,
    map_gadget: Option<MapGadget<F, NG, PoseidonChip<F>>>,
    biguint_gadget: BigUintGadget<F, NG>,
    secp256k1_chip: Option<Secp256k1Chip>,
    p256_chip: Option<P256Chip>,
    bls12_381_chip: Option<Bls12381Chip>,
    curve25519_chip: Option<Curve25519Chip>,
    base64_chip: Option<Base64Chip<F>>,
    parser_gadget: ParserGadget<F, NG>,
    scanner_chip: Option<ScannerChip<F>>,
    vector_gadget: VectorGadget<F>,
    verifier_gadget: Option<VerifierGadget<BlstrsEmulation>>,

    // Third-party chips.
    keccak_sha3_chip: Option<KeccakSha3Wrapper<F>>,
    blake2b_chip: Option<Blake2bWrapper<F>>,

    // Flags that indicate if certain chips have been used. This way we can load the tables only
    // when necessary (thus reducing the min_k in some cases).
    // Such a usage flag has to be added and updated correctly for each new chip using tables.
    used_sha2_256: Rc<RefCell<bool>>,
    used_sha2_512: Rc<RefCell<bool>>,
    used_secp256k1: Rc<RefCell<bool>>,
    used_p256: Rc<RefCell<bool>>,
    used_bls12_381: Rc<RefCell<bool>>,
    used_curve25519: Rc<RefCell<bool>>,
    used_base64: Rc<RefCell<bool>>,
    used_scanner: Rc<RefCell<bool>>,
    used_keccak_or_sha3: Rc<RefCell<bool>>,
    used_blake2b: Rc<RefCell<bool>>,
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
        let sha2_256_chip = (config.sha2_256_config.as_ref())
            .map(|sha256_config| Sha256Chip::new(sha256_config, &native_gadget));
        let varlen_sha2_256_gadget = sha2_256_chip.as_ref().map(VarLenSha256Gadget::new);
        let sha2_512_chip = (config.sha2_512_config.as_ref())
            .map(|sha512_config| Sha512Chip::new(sha512_config, &native_gadget));
        let poseidon_gadget = (config.poseidon_config.as_ref())
            .map(|poseidon_config| PoseidonChip::new(poseidon_config, &native_chip));
        let varlen_poseidon_gadget = (poseidon_gadget.as_ref())
            .map(|poseidon| VarLenPoseidonGadget::new(poseidon, &native_gadget));
        let htc_gadget = (jubjub_chip.as_ref())
            .zip(poseidon_gadget.as_ref())
            .map(|(ecc_chip, poseidon_gadget)| HashToCurveGadget::new(poseidon_gadget, ecc_chip));
        let biguint_gadget = BigUintGadget::new(&native_gadget);
        let map_gadget = poseidon_gadget
            .as_ref()
            .map(|poseidon_gadget| MapGadget::new(&native_gadget, poseidon_gadget));
        let secp256k1_scalar_chip = (config.secp256k1_scalar_config.as_ref())
            .map(|scalar_config| FieldChip::new(scalar_config, &native_gadget));
        let secp256k1_chip = (config.secp256k1_config.as_ref())
            .zip(secp256k1_scalar_chip.as_ref())
            .map(|(curve_config, scalar_chip)| {
                ForeignWeierstrassEccChip::new(curve_config, &native_gadget, scalar_chip)
            });
        let p256_scalar_chip = (config.p256_scalar_config.as_ref())
            .map(|scalar_config| FieldChip::new(scalar_config, &native_gadget));
        let p256_chip = (config.p256_config.as_ref()).zip(p256_scalar_chip.as_ref()).map(
            |(curve_config, scalar_chip)| {
                ForeignWeierstrassEccChip::new(curve_config, &native_gadget, scalar_chip)
            },
        );
        let bls12_381_chip = (config.bls12_381_config.as_ref()).map(|curve_config| {
            ForeignWeierstrassEccChip::new(curve_config, &native_gadget, &native_gadget)
        });
        let curve25519_scalar_chip = (config.curve25519_scalar_config.as_ref())
            .map(|scalar_config| FieldChip::new(scalar_config, &native_gadget));
        let curve25519_chip = (config.curve25519_config.as_ref())
            .zip(curve25519_scalar_chip.as_ref())
            .map(|(curve_config, scalar_chip)| {
                ForeignEdwardsEccChip::new(curve_config, &native_gadget, scalar_chip)
            });

        let base64_chip = (config.base64_config.as_ref())
            .map(|base64_config| Base64Chip::new(base64_config, &native_gadget));

        let parser_gadget = ParserGadget::new(&native_gadget);
        let scanner_chip =
            config.scanner_config.as_ref().map(|c| ScannerChip::new(c, &native_gadget));
        let vector_gadget = VectorGadget::new(&native_gadget);

        let verifier_gadget = bls12_381_chip.as_ref().zip(poseidon_gadget.as_ref()).map(
            |(curve_chip, sponge_chip)| {
                VerifierGadget::<BlstrsEmulation>::new(curve_chip, &native_gadget, sponge_chip)
            },
        );

        let keccak_sha3_chip = config
            .keccak_sha3_config
            .as_ref()
            .map(|sha3_config| KeccakSha3Wrapper::new(sha3_config, &native_gadget));
        let blake2b_chip = config
            .blake2b_config
            .as_ref()
            .map(|blake2b_config| Blake2bWrapper::new(blake2b_config, &native_gadget));

        Self {
            native_gadget,
            core_decomposition_chip,
            jubjub_chip,
            sha2_256_chip,
            varlen_sha2_256_gadget,
            sha2_512_chip,
            poseidon_gadget,
            varlen_poseidon_gadget,
            map_gadget,
            htc_gadget,
            biguint_gadget,
            secp256k1_chip,
            p256_chip,
            bls12_381_chip,
            curve25519_chip,
            base64_chip,
            parser_gadget,
            scanner_chip,
            vector_gadget,
            verifier_gadget,
            keccak_sha3_chip,
            blake2b_chip,
            used_sha2_256: Rc::new(RefCell::new(false)),
            used_sha2_512: Rc::new(RefCell::new(false)),
            used_secp256k1: Rc::new(RefCell::new(false)),
            used_p256: Rc::new(RefCell::new(false)),
            used_bls12_381: Rc::new(RefCell::new(false)),
            used_curve25519: Rc::new(RefCell::new(false)),
            used_base64: Rc::new(RefCell::new(false)),
            used_scanner: Rc::new(RefCell::new(false)),
            used_keccak_or_sha3: Rc::new(RefCell::new(false)),
            used_blake2b: Rc::new(RefCell::new(false)),
        }
    }

    /// Configure [ZkStdLib] from scratch.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        (arch, max_bit_len): (ZkStdLibArch, u8),
    ) -> ZkStdLibConfig {
        let nb_advice_cols = [
            arch.nb_arith_cols as usize,
            arch.nr_pow2range_cols as usize,
            arch.jubjub as usize * NB_EDWARDS_COLS,
            arch.poseidon as usize * NB_POSEIDON_ADVICE_COLS,
            arch.sha2_256 as usize * NB_SHA256_ADVICE_COLS,
            arch.sha2_512 as usize * NB_SHA512_ADVICE_COLS,
            arch.secp256k1 as usize
                * max(
                    nb_field_chip_columns::<F, k256_mod::Fq, MEP>(),
                    nb_foreign_ecc_chip_columns::<F, K256, MEP, k256_mod::Fq>(),
                ),
            arch.p256 as usize
                * max(
                    nb_field_chip_columns::<F, p256_mod::Fq, MEP>(),
                    nb_foreign_ecc_chip_columns::<F, P256, MEP, p256_mod::Fq>(),
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
            arch.curve25519 as usize
                * max(
                    nb_field_chip_columns::<F, curve25519_mod::Scalar, MEP>(),
                    nb_foreign_edwards_chip_columns::<F, Curve25519, MEP>(),
                ),
            arch.base64 as usize * NB_BASE64_ADVICE_COLS,
            arch.automaton as usize * NB_SCANNER_ADVICE_COLS,
            (arch.keccak_256 || arch.sha3_256) as usize * PACKED_ADVICE_COLS,
            arch.blake2b as usize * NB_BLAKE2B_ADVICE_COLS,
        ]
        .into_iter()
        .max()
        .unwrap_or(0);

        let nb_arith_fixed_cols = arch.nb_arith_cols as usize + NB_EXTRA_ARITH_FIXED_COLS;

        let nb_fixed_cols = [
            nb_arith_fixed_cols,
            arch.poseidon as usize * NB_POSEIDON_FIXED_COLS,
            arch.sha2_256 as usize * NB_SHA256_FIXED_COLS,
            arch.sha2_512 as usize * NB_SHA512_FIXED_COLS,
            (arch.keccak_256 || arch.sha3_256) as usize * PACKED_FIXED_COLS,
            arch.automaton as usize * NB_SCANNER_FIXED_COLS,
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
                advice_columns[..arch.nb_arith_cols as usize].to_vec(),
                fixed_columns[..nb_arith_fixed_cols].to_vec(),
                [committed_instance_column, instance_column],
            ),
        );

        let nb_parallel_range_checks = arch.nr_pow2range_cols as usize;
        let max_bit_len = max_bit_len as u32;

        let pow2range_config =
            Pow2RangeChip::configure(meta, &advice_columns[1..=arch.nr_pow2range_cols as usize]);

        let core_decomposition_config =
            P2RDecompositionChip::configure(meta, &(native_config.clone(), pow2range_config));

        let jubjub_config = arch.jubjub.then(|| {
            EccChip::<C>::configure(meta, &advice_columns[..NB_EDWARDS_COLS].try_into().unwrap())
        });

        let sha2_256_config = arch.sha2_256.then(|| {
            Sha256Chip::configure(
                meta,
                &(
                    advice_columns[..NB_SHA256_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[..NB_SHA256_FIXED_COLS].try_into().unwrap(),
                ),
            )
        });

        let sha2_512_config = arch.sha2_512.then(|| {
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

        let secp256k1_scalar_config = arch.secp256k1.then(|| {
            Secp256k1ScalarChip::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            )
        });

        let secp256k1_config = arch.secp256k1.then(|| {
            let base_config = Secp256k1BaseChip::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            );
            Secp256k1Chip::configure(
                meta,
                &base_config,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            )
        });

        let p256_scalar_config = arch.p256.then(|| {
            P256ScalarChip::configure(meta, &advice_columns, nb_parallel_range_checks, max_bit_len)
        });

        let p256_config = arch.p256.then(|| {
            let base_config = P256BaseChip::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            );
            P256Chip::configure(
                meta,
                &base_config,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            )
        });

        let bls12_381_config = arch.bls12_381.then(|| {
            let base_config = Bls12381BaseChip::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            );
            Bls12381Chip::configure(
                meta,
                &base_config,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            )
        });

        let curve25519_scalar_config = arch.curve25519.then(|| {
            Curve25519ScalarChip::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            )
        });

        let curve25519_config = arch.curve25519.then(|| {
            let base_config = Curve25519BaseChip::configure(
                meta,
                &advice_columns,
                nb_parallel_range_checks,
                max_bit_len,
            );
            Curve25519Chip::configure(
                meta,
                &base_config,
                &advice_columns,
                &fixed_columns,
                nb_parallel_range_checks,
                max_bit_len,
            )
        });

        let base64_config = arch.base64.then(|| {
            Base64Chip::configure(
                meta,
                advice_columns[..NB_BASE64_ADVICE_COLS].try_into().unwrap(),
            )
        });

        let scanner_config = arch.automaton.then(|| {
            ScannerChip::configure(
                meta,
                &(
                    advice_columns[..NB_SCANNER_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[0],
                    parsing::spec_library(),
                ),
            )
        });

        let constant_column =
            (arch.keccak_256 || arch.sha3_256 || arch.blake2b).then(|| meta.fixed_column());

        let keccak_sha3_config = (arch.keccak_256 || arch.sha3_256).then(|| {
            PackedChip::configure(
                meta,
                constant_column.unwrap(),
                advice_columns[..PACKED_ADVICE_COLS].try_into().unwrap(),
                fixed_columns[..PACKED_FIXED_COLS].try_into().unwrap(),
            )
        });

        let blake2b_config = arch.blake2b.then(|| {
            Blake2bChip::configure(
                meta,
                constant_column.unwrap(),
                advice_columns[0],
                advice_columns[1..NB_BLAKE2B_ADVICE_COLS].try_into().unwrap(),
            )
        });

        ZkStdLibConfig {
            native_config,
            core_decomposition_config,
            jubjub_config,
            sha2_256_config,
            sha2_512_config,
            poseidon_config,
            secp256k1_scalar_config,
            secp256k1_config,
            p256_scalar_config,
            p256_config,
            bls12_381_config,
            curve25519_scalar_config,
            curve25519_config,
            base64_config,
            scanner_config,
            keccak_sha3_config,
            blake2b_config,
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

    /// Chip for performing in-circuit operations over the Secp256k1 curve, its
    /// scalar field or its base field.
    pub fn secp256k1(&self) -> &Secp256k1Chip {
        *self.used_secp256k1.borrow_mut() = true;
        self.secp256k1_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable secp256k1"))
    }

    /// Chip for performing in-circuit operations over the P256 curve, its
    /// scalar field or its base field.
    pub fn p256(&self) -> &P256Chip {
        *self.used_p256.borrow_mut() = true;
        self.p256_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable p256"))
    }

    /// Chip for performing in-circuit operations over the BLS12-381 curve, its
    /// scalar field or its base field.
    pub fn bls12_381(&self) -> &Bls12381Chip {
        *self.used_bls12_381.borrow_mut() = true;
        self.bls12_381_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable bls12_381"))
    }

    /// Chip for performing in-circuit operations over Curve25519.
    pub fn curve25519(&self) -> &Curve25519Chip {
        *self.used_curve25519.borrow_mut() = true;
        self.curve25519_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable curve25519"))
    }

    /// Chip for performing in-circuit base64 decoding.
    pub fn base64(&self) -> &Base64Chip<F> {
        *self.used_base64.borrow_mut() = true;
        self.base64_chip
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable base64"))
    }

    /// Gadget for column-free parsing helpers (fetch_bytes, date_to_int, etc.).
    /// Always available (no arch flag needed).
    pub fn parser(&self) -> &ParserGadget<F, NG> {
        &self.parser_gadget
    }

    /// Chip for various scanning functions based on lookups. This includes
    /// automaton-based parsing ([`ScannerChip::parse`]) and substring checks
    /// ([`ScannerChip::check_subsequence`], [`ScannerChip::check_bytes`]).
    ///
    /// Returns the scanner chip for automaton-based parsing and substring
    /// checks. The static automaton table is loaded automatically when
    /// `parse` is called with a `Static(..)` variant.
    pub fn scanner(&self) -> &ScannerChip<F> {
        *self.used_scanner.borrow_mut() = true;
        (self.scanner_chip.as_ref()).unwrap_or_else(|| panic!("ZkStdLibArch must enable automaton"))
    }

    /// Chip for performing in-circuit verification of proofs
    /// (generated with Poseidon as the Fiat-Shamir transcript hash).
    pub fn verifier(&self) -> &VerifierGadget<BlstrsEmulation> {
        *self.used_bls12_381.borrow_mut() = true;
        self.verifier_gadget
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable bls12_381 & poseidon"))
    }

    /// Assert that a given assigned bit is true.
    ///
    /// ```
    /// # midnight_zk_stdlib::run_test_stdlib!(chip, layouter, 13, {
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
    /// # midnight_zk_stdlib::run_test_stdlib!(chip, layouter, 13, {
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
    /// # midnight_zk_stdlib::run_test_stdlib!(chip, layouter, 13, {
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

    /// Poseidon hash from a slice of native values into a native value.
    ///
    /// ```
    /// # midnight_zk_stdlib::run_test_stdlib!(chip, layouter, 13, {
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

    /// Poseidon hash over a payload whose element count can vary between
    /// proofs.
    ///
    /// Unlike [`poseidon`](Self::poseidon), which takes a plain slice whose
    /// length is structurally fixed in the circuit (the same for every proof),
    /// this variant takes an [`AssignedVector`]: a specialized structure for
    /// carrying data of varying length, up to a maximum capacity of `M`
    /// elements.
    ///
    /// `M` must be a multiple of 2 (the Poseidon absorption rate).
    pub fn poseidon_varlen<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, AssignedNative<F>, M, RATE>,
    ) -> Result<AssignedNative<F>, Error> {
        assert!(
            M.is_multiple_of(RATE),
            "poseidon_varlen only supports assigned vector whose maxlen M is a multiple of {RATE} (here M = {M})"
        );
        self.varlen_poseidon_gadget
            .as_ref()
            .unwrap_or_else(|| panic!("ZkStdLibArch must enable poseidon"))
            .poseidon_varlen(layouter, input)
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

    /// SHA2-256.
    /// Takes as input a slice of assigned bytes and returns the assigned
    /// input/output in bytes.
    /// We assume the field uses little endian encoding.
    /// ```
    /// # midnight_zk_stdlib::run_test_stdlib!(chip, layouter, 13, {
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
    /// let _hash = chip.sha2_256(layouter, &input)?;
    /// # });
    /// ```
    pub fn sha2_256(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>], // F -> decompose_bytes -> hash
    ) -> Result<[AssignedByte<F>; 32], Error> {
        *self.used_sha2_256.borrow_mut() = true;
        self.sha2_256_chip
            .as_ref()
            .expect("ZkStdLibArch must enable sha256")
            .hash(layouter, input)
    }

    /// SHA-256 hash over a payload whose byte count can vary between proofs.
    ///
    /// Unlike [`sha2_256`](Self::sha2_256), which takes a plain slice whose
    /// length is structurally fixed in the circuit (the same for every proof),
    /// this variant takes an [`AssignedVector`]: a specialized structure for
    /// carrying data of varying length, up to a maximum capacity of `M` bytes.
    ///
    /// `M` must be a multiple of 64 (the SHA-256 block size).
    pub fn sha2_256_varlen<const M: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedVector<F, AssignedByte<F>, M, 64>,
    ) -> Result<[AssignedByte<F>; 32], Error> {
        *self.used_sha2_256.borrow_mut() = true;
        assert!(
            M.is_multiple_of(64),
            "sha2_256_varlen only supports assigned vector whose maxlen M is a multiple of 64 (here M = {M})"
        );
        self.varlen_sha2_256_gadget
            .as_ref()
            .expect("ZkStdLibArch must enable sha256")
            .varhash(layouter, input)
    }

    /// SHA2-512 hash.
    pub fn sha2_512(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>], // F -> decompose_bytes -> hash
    ) -> Result<[AssignedByte<F>; 64], Error> {
        *self.used_sha2_512.borrow_mut() = true;
        self.sha2_512_chip
            .as_ref()
            .expect("ZkStdLibArch must enable sha512")
            .hash(layouter, input)
    }

    /// SHA3-256 hash (third-party implementation).
    pub fn sha3_256(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<Fq>; 32], Error> {
        *self.used_keccak_or_sha3.borrow_mut() = true;
        let chip = self
            .keccak_sha3_chip
            .as_ref()
            .expect("ZkStdLibArch must enable sha3 (or keccak)");
        chip.sha3_256_digest(layouter, input)
    }

    /// Keccak-256 hash (third-party implementation).
    pub fn keccak_256(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<Fq>; 32], Error> {
        *self.used_keccak_or_sha3.borrow_mut() = true;
        let chip = self
            .keccak_sha3_chip
            .as_ref()
            .expect("ZkStdLibArch must enable keccak (or sha3)");
        chip.keccak_256_digest(layouter, input)
    }

    /// Blake2b hash with a 256-bit output, unkeyed (third-party
    /// implementation).
    pub fn blake2b_256(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 32], Error> {
        *self.used_blake2b.borrow_mut() = true;
        let chip = self.blake2b_chip.as_ref().expect("ZkStdLibArch must enable blake2b");
        chip.blake2b_256_digest(layouter, input)
    }

    /// Blake2b hash with a 512-bit output, unkeyed (third-party
    /// implementation).
    pub fn blake2b_512(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedByte<F>],
    ) -> Result<[AssignedByte<F>; 64], Error> {
        *self.used_blake2b.borrow_mut() = true;
        let chip = self.blake2b_chip.as_ref().expect("ZkStdLibArch must enable blake2b");
        chip.blake2b_512_digest(layouter, input)
    }
}
