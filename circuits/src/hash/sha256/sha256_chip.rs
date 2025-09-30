//! This file implements a chip providing support for in-circuit evaluation of
//! the SHA256 hash function.
//!
//! Throughout the file, we use the notation from NIST FIPS PUB 180-4:
//! <https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf> (Section 6.2).
//!
//! This implementation uses the amazing trick of a plain-spreaded table,
//! devised by the Zcash team (to the best of our knowledge):
//! See <https://zcash.github.io/halo2/design/gadgets/sha256/table16.html>.
//!
//! In a nutshell, the "spreaded" form of a u32 is the u64 resulting from
//! inserting a zero between all its bits. For example, the spreaded version
//! of 13 = 0b1101 is 0b01010001 = 81.
//!                     ^ ^ ^ ^
//! We denote the spreaded form of a value X: u32 by ~X: u64.
//!
//! The spreaded form can be used to enforce bit-wise operations very
//! efficiently, essentially with a single native field addition (which can be
//! seen as an integer addition since values are guaranteed to not wrap-around
//! the native modulus).
//!
//! For example, the bit-wise XOR of two values X and Y is encoded in the
//! even bits of ~X + ~Y (and the odd bits encode their bit-wise AND).
//! Thus, for X, Y in [0, 2^32), Z = X ⊕ Y can be enforced as
//! ~Z + 2 * ~W = ~X + ~Y and Z, W in [0, 2^32); where W is an auxiliary
//! variable. The consistency between X, Y, Z, W and ~X, ~Y, ~Z, ~W (and, by the
//! way, their range condition) be enforced with a lookup table.
//!
//! In this chip we use a lookup table with 3 columns of the form (n, X, ~X)
//! which guarantees that ~X is the spreaded form of X and that X has n-bits,
//! i.e. X in [0, 2^n).
//!
//! Our 32-bit values are represented in limbs of at most 12 bits. This allows
//! us to have a small table with (only) values in the range n = 2..=12
//! (n = 8 is an exception, intentionally not included, to give room for the ZK
//! unused rows, this way the table fits in a K = 13 domain).
//!
//! We have 2 parallel lookups, which allow us to call such plain-spreaded table
//! twice per row; on columns named (T0, A0, A1) and (T1, A2, A3).

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Selector,
        TableColumn,
    },
    poly::Rotation,
};
use num_integer::Integer;

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    hash::sha256::{
        types::{
            AssignedMessageWord, AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded,
            CompressionState, LimbsOfA, LimbsOfE,
        },
        utils::{
            expr_pow2_ip, expr_pow4_ip, gen_spread_table, get_even_and_odd_bits, negate_spreaded,
            spread, spreaded_Sigma_0, spreaded_Sigma_1, spreaded_maj, spreaded_sigma_0,
            spreaded_sigma_1, u32_in_be_limbs, MASK_EVN_64,
        },
    },
    instructions::{assignments::AssignmentInstructions, DecompositionInstructions},
    types::{AssignedByte, AssignedNative},
    utils::{
        util::{fe_to_u32, fe_to_u64, u32_to_fe, u64_to_fe},
        ComposableChip,
    },
};

/// Number of advice columns used by the identities of the SHA256 chip.
pub const NB_SHA256_ADVICE_COLS: usize = 8;

/// Number of fixed columns used by the identities of the SHA256 chip.
pub const NB_SHA256_FIXED_COLS: usize = 2;

pub(super) const ROUND_CONSTANTS: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub(super) const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Tag for the even and odd 11-11-10 decompositions.
enum Parity {
    Evn,
    Odd,
}

/// Plain-Spreaded lookup table.
#[derive(Clone, Debug)]
struct SpreadTable {
    nbits_col: TableColumn,
    plain_col: TableColumn,
    sprdd_col: TableColumn,
}

/// Configuration of Sha256Chip.
#[derive(Clone, Debug)]
pub struct Sha256Config {
    advice_cols: [Column<Advice>; NB_SHA256_ADVICE_COLS],
    fixed_cols: [Column<Fixed>; NB_SHA256_FIXED_COLS],

    q_lookup: Selector,
    table: SpreadTable,

    q_maj: Selector,
    q_half_ch: Selector,
    q_Sigma_0: Selector,
    q_Sigma_1: Selector,
    q_sigma_0: Selector,
    q_sigma_1: Selector,

    q_11_11_10: Selector,
    q_10_9_11_2: Selector,
    q_7_12_2_5_6: Selector,
    q_12_1x3_7_3_4_3: Selector,
    q_add_mod_2_32: Selector,
}

/// Chip for SHA256.
#[derive(Clone, Debug)]
pub struct Sha256Chip<F: PrimeField> {
    config: Sha256Config,
    pub(super) native_gadget: NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>,
}

impl<F: PrimeField> Chip<F> for Sha256Chip<F> {
    type Config = Sha256Config;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> ComposableChip<F> for Sha256Chip<F> {
    type SharedResources = (
        [Column<Advice>; NB_SHA256_ADVICE_COLS],
        [Column<Fixed>; NB_SHA256_FIXED_COLS],
    );

    type InstructionDeps = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    fn new(config: &Sha256Config, native_gadget: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: native_gadget.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> Sha256Config {
        let fixed_cols = shared_res.1;

        // Columns A0 and A2 do not need to be copy-enabled.
        // We have the convention that chips enable copy in a prefix of their shared
        // advice columns. Thus we let A0 and A2 be the last two columns of the given
        // shared resources.
        let advice_cols = [6, 0, 7, 1, 2, 3, 4, 5].map(|i| shared_res.0[i]);
        for (i, column) in advice_cols.iter().enumerate() {
            if i != 0 && i != 2 {
                meta.enable_equality(*column);
            }
        }

        let q_lookup = meta.complex_selector();
        let table = SpreadTable {
            nbits_col: meta.lookup_table_column(),
            plain_col: meta.lookup_table_column(),
            sprdd_col: meta.lookup_table_column(),
        };

        let q_maj = meta.selector();
        let q_half_ch = meta.selector();
        let q_Sigma_0 = meta.selector();
        let q_Sigma_1 = meta.selector();
        let q_sigma_0 = meta.selector();
        let q_sigma_1 = meta.selector();

        let q_11_11_10 = meta.selector();
        let q_10_9_11_2 = meta.selector();
        let q_7_12_2_5_6 = meta.selector();
        let q_12_1x3_7_3_4_3 = meta.selector();
        let q_add_mod_2_32 = meta.selector();

        (0..2).for_each(|idx| {
            meta.lookup("plain-spreaded lookup", |meta| {
                let q_lookup = meta.query_selector(q_lookup);

                let nbits = meta.query_fixed(fixed_cols[idx], Rotation(0));
                let plain = meta.query_advice(advice_cols[2 * idx], Rotation(0));
                let sprdd = meta.query_advice(advice_cols[2 * idx + 1], Rotation(0));

                vec![
                    (q_lookup.clone() * nbits, table.nbits_col),
                    (q_lookup.clone() * plain, table.plain_col),
                    (q_lookup * sprdd, table.sprdd_col),
                ]
            });
        });

        meta.create_gate("Maj(A, B, C)", |meta| {
            // See function `maj` for a description of the following layout.
            let sA = meta.query_advice(advice_cols[5], Rotation(-1));
            let sB = meta.query_advice(advice_cols[6], Rotation(-1));
            let sC = meta.query_advice(advice_cols[5], Rotation(0));
            let s_odd_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_odd_010 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_evn_010 = meta.query_advice(advice_cols[3], Rotation(1));

            let s_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_010]);
            let s_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_010]);

            let id = (sA + sB + sC) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_maj, vec![("Maj", id)])
        });

        meta.create_gate("half Ch(E, F, G)", |meta| {
            // See function `ch` for a description of the following layout.
            let sX = meta.query_advice(advice_cols[5], Rotation(-1));
            let sY = meta.query_advice(advice_cols[6], Rotation(-1));
            let s_odd_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_odd_010 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_evn_010 = meta.query_advice(advice_cols[3], Rotation(1));
            let summand_1 = meta.query_advice(advice_cols[4], Rotation(0));
            let summand_2 = meta.query_advice(advice_cols[5], Rotation(0));
            let sum = meta.query_advice(advice_cols[6], Rotation(0));

            let s_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_010]);
            let s_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_010]);

            let sprdd_id = (sX + sY) - (s_evn + Expression::from(2) * s_odd);
            let sum_id = (summand_1 + summand_2) - sum;

            Constraints::with_selector(
                q_half_ch,
                vec![
                    ("Half-Ch spreadded", sprdd_id),
                    ("Half Ch sum (2 terms)", sum_id),
                ],
            )
        });

        meta.create_gate("Σ₀(A)", |meta| {
            // See function `Sigma_0` for a description of the following layout.
            let s10 = meta.query_advice(advice_cols[5], Rotation(-1));
            let s09 = meta.query_advice(advice_cols[6], Rotation(-1));
            let s11 = meta.query_advice(advice_cols[5], Rotation(0));
            let s02 = meta.query_advice(advice_cols[6], Rotation(0));
            let s_evn_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_010 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_010 = meta.query_advice(advice_cols[3], Rotation(1));

            let s_1st_rot = expr_pow4_ip([30, 20, 11, 0], [&s02, &s10, &s09, &s11]);
            let s_2nd_rot = expr_pow4_ip([21, 19, 9, 0], [&s11, &s02, &s10, &s09]);
            let s_3rd_rot = expr_pow4_ip([23, 12, 10, 0], [&s09, &s11, &s02, &s10]);

            let s_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_010]);
            let s_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_010]);

            let id = (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_Sigma_0, vec![("Sigma_0", id)])
        });

        meta.create_gate("Σ₁(E)", |meta| {
            // See function `Sigma_1` for a description of the following layout.
            let s07 = meta.query_advice(advice_cols[5], Rotation(-1));
            let s12 = meta.query_advice(advice_cols[6], Rotation(-1));
            let s02 = meta.query_advice(advice_cols[5], Rotation(0));
            let s05 = meta.query_advice(advice_cols[6], Rotation(0));
            let s06 = meta.query_advice(advice_cols[5], Rotation(1));
            let s_evn_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_10 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_10 = meta.query_advice(advice_cols[3], Rotation(1));

            let s_1st_rot = expr_pow4_ip([26, 19, 7, 5, 0], [&s06, &s07, &s12, &s02, &s05]);
            let s_2nd_rot = expr_pow4_ip([27, 21, 14, 2, 0], [&s05, &s06, &s07, &s12, &s02]);
            let s_3rd_rot = expr_pow4_ip([20, 18, 13, 7, 0], [&s12, &s02, &s05, &s06, &s07]);

            let s_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_10]);
            let s_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_10]);

            let id = (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_Sigma_1, vec![("Sigma_1", id)])
        });

        meta.create_gate("σ₀(W)", |meta| {
            // See function `sigma_0` for a description of the following layout.
            let s12 = meta.query_advice(advice_cols[5], Rotation(-1));
            let s1a = meta.query_advice(advice_cols[6], Rotation(-1));
            let s1b = meta.query_advice(advice_cols[4], Rotation(0));
            let s1c = meta.query_advice(advice_cols[5], Rotation(0));
            let s07 = meta.query_advice(advice_cols[6], Rotation(0));
            let s3a = meta.query_advice(advice_cols[4], Rotation(1));
            let s04 = meta.query_advice(advice_cols[5], Rotation(1));
            let s3b = meta.query_advice(advice_cols[6], Rotation(1));
            let s_evn_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_10 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_10 = meta.query_advice(advice_cols[3], Rotation(1));

            let sprdd_1st_shift = expr_pow4_ip(
                [17, 16, 15, 14, 7, 4, 0],
                [&s12, &s1a, &s1b, &s1c, &s07, &s3a, &s04],
            );
            let sprdd_2nd_rot = expr_pow4_ip(
                [28, 25, 13, 12, 11, 10, 3, 0],
                [&s04, &s3b, &s12, &s1a, &s1b, &s1c, &s07, &s3a],
            );
            let sprdd_3rd_rot = expr_pow4_ip(
                [31, 24, 21, 17, 14, 2, 1, 0],
                [&s1c, &s07, &s3a, &s04, &s3b, &s12, &s1a, &s1b],
            );

            let sprdd_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_10]);
            let sprdd_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_10]);

            let id = (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot)
                - (sprdd_evn + Expression::from(2) * sprdd_odd);

            Constraints::with_selector(q_sigma_0, vec![("sigma_0", id)])
        });

        meta.create_gate("σ₁(W)", |meta| {
            // See function `sigma_1` for a description of the following layout.
            let s12 = meta.query_advice(advice_cols[5], Rotation(-1));
            let s1a = meta.query_advice(advice_cols[6], Rotation(-1));
            let s1b = meta.query_advice(advice_cols[4], Rotation(0));
            let s1c = meta.query_advice(advice_cols[5], Rotation(0));
            let s07 = meta.query_advice(advice_cols[6], Rotation(0));
            let s3a = meta.query_advice(advice_cols[4], Rotation(1));
            let s04 = meta.query_advice(advice_cols[5], Rotation(1));
            let s3b = meta.query_advice(advice_cols[6], Rotation(1));
            let s_evn_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_10 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_10 = meta.query_advice(advice_cols[3], Rotation(1));

            let sprdd_1st_shift = expr_pow4_ip([10, 9, 8, 7, 0], [&s12, &s1a, &s1b, &s1c, &s07]);
            let sprdd_2nd_rot = expr_pow4_ip(
                [25, 22, 18, 15, 3, 2, 1, 0],
                [&s07, &s3a, &s04, &s3b, &s12, &s1a, &s1b, &s1c],
            );
            let sprdd_3rd_rot = expr_pow4_ip(
                [31, 30, 23, 20, 16, 13, 1, 0],
                [&s1b, &s1c, &s07, &s3a, &s04, &s3b, &s12, &s1a],
            );

            let sprdd_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_10]);
            let sprdd_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_10]);

            let id = (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot)
                - (sprdd_evn + Expression::from(2) * sprdd_odd);

            Constraints::with_selector(q_sigma_1, vec![("sigma_1", id)])
        });

        meta.create_gate("11-11-10 decomposition", |meta| {
            // See function `assign_sprdd_11_11_10` for a description of the following
            // layout.
            let p11a = meta.query_advice(advice_cols[0], Rotation(-1));
            let p11b = meta.query_advice(advice_cols[0], Rotation(0));
            let p_10 = meta.query_advice(advice_cols[0], Rotation(1));
            let output = meta.query_advice(advice_cols[4], Rotation(-1));

            let id = expr_pow2_ip([21, 10, 0], [&p11a, &p11b, &p_10]) - output;

            Constraints::with_selector(q_11_11_10, vec![("11-11-10 decomposition", id)])
        });

        meta.create_gate("10-9-11-2 decomposition", |meta| {
            // See function `prepare_A` for a description of the following layout.
            let p10 = meta.query_advice(advice_cols[0], Rotation(-1));
            let p09 = meta.query_advice(advice_cols[2], Rotation(-1));
            let p11 = meta.query_advice(advice_cols[0], Rotation(0));
            let p02 = meta.query_advice(advice_cols[2], Rotation(0));
            let s10 = meta.query_advice(advice_cols[1], Rotation(-1));
            let s09 = meta.query_advice(advice_cols[3], Rotation(-1));
            let s11 = meta.query_advice(advice_cols[1], Rotation(0));
            let s02 = meta.query_advice(advice_cols[3], Rotation(0));
            let plain = meta.query_advice(advice_cols[4], Rotation(-1));
            let sprdd = meta.query_advice(advice_cols[4], Rotation(0));

            let plain_id = expr_pow2_ip([22, 13, 2, 0], [&p10, &p09, &p11, &p02]) - plain;
            let sprdd_id = expr_pow4_ip([22, 13, 2, 0], [&s10, &s09, &s11, &s02]) - sprdd;

            Constraints::with_selector(
                q_10_9_11_2,
                vec![
                    ("10_9_11_2 decomposition plain", plain_id),
                    ("10_9_11_2 decomposition sprdd", sprdd_id),
                ],
            )
        });

        meta.create_gate("7-12-2-5-6 decomposition", |meta| {
            // See function `prepare_E` for a description of the following layout.
            let p07 = meta.query_advice(advice_cols[0], Rotation(-1));
            let p12 = meta.query_advice(advice_cols[2], Rotation(-1));
            let p02 = meta.query_advice(advice_cols[0], Rotation(0));
            let p05 = meta.query_advice(advice_cols[2], Rotation(0));
            let p06 = meta.query_advice(advice_cols[0], Rotation(1));
            let s07 = meta.query_advice(advice_cols[1], Rotation(-1));
            let s12 = meta.query_advice(advice_cols[3], Rotation(-1));
            let s02 = meta.query_advice(advice_cols[1], Rotation(0));
            let s05 = meta.query_advice(advice_cols[3], Rotation(0));
            let s06 = meta.query_advice(advice_cols[1], Rotation(1));
            let plain = meta.query_advice(advice_cols[4], Rotation(-1));
            let sprdd = meta.query_advice(advice_cols[4], Rotation(0));

            let plain_id = expr_pow2_ip([25, 13, 11, 6, 0], [&p07, &p12, &p02, &p05, &p06]) - plain;
            let sprdd_id = expr_pow4_ip([25, 13, 11, 6, 0], [&s07, &s12, &s02, &s05, &s06]) - sprdd;

            Constraints::with_selector(
                q_7_12_2_5_6,
                vec![
                    ("7_12_2_5_6 decomposition plain", plain_id),
                    ("7_12_2_5_6 decomposition sprdd", sprdd_id),
                ],
            )
        });

        meta.create_gate("12-1x3-7-3-4-3 decomposition", |meta| {
            // See function `prepare_message_word` for a description of the following
            // layout.
            let w12 = meta.query_advice(advice_cols[0], Rotation(-1));
            let w07 = meta.query_advice(advice_cols[2], Rotation(-1));
            let w3a = meta.query_advice(advice_cols[0], Rotation(0));
            let w04 = meta.query_advice(advice_cols[2], Rotation(0));
            let w3b = meta.query_advice(advice_cols[0], Rotation(1));
            let w1a = meta.query_advice(advice_cols[7], Rotation(-1));
            let w1b = meta.query_advice(advice_cols[7], Rotation(0));
            let w1c = meta.query_advice(advice_cols[7], Rotation(1));
            let plain = meta.query_advice(advice_cols[4], Rotation(-1));

            let plain_id = expr_pow2_ip(
                [20, 19, 18, 17, 10, 7, 3, 0],
                [&w12, &w1a, &w1b, &w1c, &w07, &w3a, &w04, &w3b],
            ) - plain;

            // 1-bit check for W.1a, W.1b and W.1c
            let w_1a_check = w1a.clone() * (w1a - Expression::from(1));
            let w_1b_check = w1b.clone() * (w1b - Expression::from(1));
            let w_1c_check = w1c.clone() * (w1c - Expression::from(1));

            Constraints::with_selector(
                q_12_1x3_7_3_4_3,
                vec![
                    ("12_1x3_7_3_4_3 decomposition ", plain_id),
                    ("W.1a 1-bit check", w_1a_check),
                    ("W.1b 1-bit check", w_1b_check),
                    ("W.1c 1-bit check", w_1c_check),
                ],
            )
        });

        meta.create_gate("add mod 2^32", |meta| {
            // See function `assign_add_mod_2_32` for a description of the following layout.
            let s0 = meta.query_advice(advice_cols[5], Rotation(-1));
            let s1 = meta.query_advice(advice_cols[6], Rotation(-1));
            let s2 = meta.query_advice(advice_cols[5], Rotation(0));
            let s3 = meta.query_advice(advice_cols[6], Rotation(0));
            let s4 = meta.query_advice(advice_cols[4], Rotation(1));
            let s5 = meta.query_advice(advice_cols[5], Rotation(1));
            let s6 = meta.query_advice(advice_cols[6], Rotation(1));

            let carry = meta.query_advice(advice_cols[2], Rotation(1));
            let result = meta.query_advice(advice_cols[4], Rotation(-1));

            let summands = [s0, s1, s2, s3, s4, s5, s6];
            let lhs = summands.into_iter().reduce(|acc, x| acc + x).unwrap();
            let rhs = result + carry * Expression::Constant(F::from(1u64 << 32));

            Constraints::with_selector(q_add_mod_2_32, vec![("add_mod_2_32", lhs - rhs)])
        });

        Sha256Config {
            advice_cols,
            fixed_cols,

            q_lookup,
            table,

            q_maj,
            q_half_ch,
            q_Sigma_0,
            q_Sigma_1,
            q_sigma_0,
            q_sigma_1,

            q_11_11_10,
            q_10_9_11_2,
            q_7_12_2_5_6,
            q_12_1x3_7_3_4_3,
            q_add_mod_2_32,
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let SpreadTable {
            nbits_col,
            plain_col,
            sprdd_col,
        } = self.config().table;

        layouter.assign_table(
            || "spread table",
            |mut table| {
                for (index, triple) in gen_spread_table::<F>().enumerate() {
                    table.assign_cell(|| "nbits", nbits_col, index, || Value::known(triple.0))?;
                    table.assign_cell(|| "plain", plain_col, index, || Value::known(triple.1))?;
                    table.assign_cell(|| "sprdd", sprdd_col, index, || Value::known(triple.2))?;
                }
                Ok(())
            },
        )
    }
}

impl<F: PrimeField> Sha256Chip<F> {
    /// In-circuit SHA256 computation, the protagonist of this chip.
    pub(super) fn sha256(
        &self,
        layouter: &mut impl Layouter<F>,
        input_bytes: &[AssignedByte<F>],
    ) -> Result<[AssignedPlain<F, 32>; 8], Error> {
        let mut state = CompressionState::<F>::fixed(layouter, &self.native_gadget, IV)?;

        for block_bytes in self.pad(layouter, input_bytes)?.chunks(64) {
            let block = self.block_from_bytes(layouter, block_bytes.try_into().unwrap())?;
            let message_blocks = self.message_schedule(layouter, &block)?;
            let mut compression_state = state.clone();
            for i in 0..64 {
                compression_state = self.compression_round(
                    layouter,
                    &compression_state,
                    ROUND_CONSTANTS[i],
                    &message_blocks[i],
                )?;
            }
            state = state.add(self, layouter, &compression_state)?;
        }

        Ok(state.plain())
    }

    /// Pads the input byte array to be a multiple of 64 bytes (512 bits).
    fn pad(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let l = 8 * bytes.len();
        let k = 512 - (l + 65) % 512;

        let mut padded = bytes.to_vec();
        padded.push(self.native_gadget.assign_fixed(layouter, 128u8)?); // k is always 7 mod 8
        padded.extend(vec![self.native_gadget.assign_fixed(layouter, 0u8)?; k / 8]);
        for byte in u64::to_be_bytes(l as u64) {
            padded.push(self.native_gadget.assign_fixed(layouter, byte)?);
        }

        Ok(padded)
    }

    /// Given a byte array of exactly 64 bytes, this function converts it into a
    /// block of 16 `AssignedPlain` values, each (32 bits) value representing 4
    /// bytes in big-endian.
    pub(super) fn block_from_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>; 64],
    ) -> Result<[AssignedPlain<F, 32>; 16], Error> {
        Ok(bytes
            .chunks(4)
            .map(|word_bytes| {
                self.native_gadget
                    .assigned_from_be_bytes(layouter, word_bytes)
                    .map(AssignedPlain)
            })
            .collect::<Result<Vec<_>, Error>>()?
            .try_into()
            .unwrap())
    }

    /// Takes a 512-bits block, represented with 16 `AssignedPlain<32>` words.
    /// Outputs the 64 `AssignedPlain<32>` words Wi from SHA256's message
    /// schedule.
    pub(super) fn message_schedule(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &[AssignedPlain<F, 32>; 16],
    ) -> Result<[AssignedPlain<F, 32>; 64], Error> {
        let message_word = self.prepare_message_word(layouter, &[block[0].clone()])?;
        let mut message_words: [AssignedMessageWord<F>; 64] =
            core::array::from_fn(|_| message_word.clone());

        // The first 16 message words are got by decomposing the block words
        // into 12-1x3-7-3-4-3 limbs directly.
        for word_idx in 1..16 {
            message_words[word_idx] =
                self.prepare_message_word(layouter, &[block[word_idx].clone()])?;
        }
        // The remaining 48 message words are computed using the recurrence relation
        // W.i = W.(i-16) + W.(i-7) + σ₀(W.(i-15)) + σ₁(W.(i-2))
        // and decomposing into 12-1x3-7-3-4-3 limbs.
        for word_idx in 16..64 {
            let sigma0_w_i_minus_15 = &self.sigma_0(layouter, &message_words[word_idx - 15])?;
            let sigma1_w_i_minus_2 = &self.sigma_1(layouter, &message_words[word_idx - 2])?;
            message_words[word_idx] = self.prepare_message_word(
                layouter,
                &[
                    message_words[word_idx - 16].combined_plain.clone(),
                    message_words[word_idx - 7].combined_plain.clone(),
                    sigma0_w_i_minus_15.clone(),
                    sigma1_w_i_minus_2.clone(),
                ],
            )?;
        }

        Ok(message_words.map(|w| w.combined_plain))
    }

    /// A compression round. This is called 64 times per block.
    pub(super) fn compression_round(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &CompressionState<F>,
        round_k: u32,
        round_w: &AssignedPlain<F, 32>,
    ) -> Result<CompressionState<F>, Error> {
        let round_k = AssignedPlain::<F, 32>::fixed(layouter, &self.native_gadget, round_k)?;

        let Sigma_0_of_a = self.Sigma_0(layouter, &state.a)?;
        let Maj_of_a_b_c = self.maj(
            layouter,
            &state.a.combined.spreaded,
            &state.b.spreaded,
            &state.c.spreaded,
        )?;
        let Sigma_1_of_e = self.Sigma_1(layouter, &state.e)?;
        let Ch_of_e_f_g = self.ch(
            layouter,
            &state.e.combined.spreaded,
            &state.f.spreaded,
            &state.g.spreaded,
        )?;

        let next_a_summands = [
            state.h.clone(),
            Sigma_1_of_e.clone(),
            Ch_of_e_f_g.clone(),
            round_k.clone(),
            round_w.clone(),
            Sigma_0_of_a,
            Maj_of_a_b_c,
        ];

        let next_e_summands = [
            state.d.clone(),
            state.h.clone(),
            Sigma_1_of_e,
            Ch_of_e_f_g,
            round_k.clone(),
            round_w.clone(),
        ];

        Ok(CompressionState {
            a: self.prepare_A(layouter, &next_a_summands)?,
            b: state.a.combined.clone(),
            c: state.b.clone(),
            d: state.c.plain.clone(),
            e: self.prepare_E(layouter, &next_e_summands)?,
            f: state.e.combined.clone(),
            g: state.f.clone(),
            h: state.g.plain.clone(),
        })
    }

    /// Computes Maj(A, B, C).
    fn maj(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_a: &AssignedSpreaded<F, 32>,
        sprdd_b: &AssignedSpreaded<F, 32>,
        sprdd_c: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We need to compute:
            Maj(A, B, C) = (A ∧ B) ⊕ (A ∧ C) ⊕ (B ∧ C)

        Note that the "majority" function (bit-wise most commont value) between A, B, C
        is encoded in the odd bits of (~A + ~B + ~C). This is because, for every bit
        position i, iff at least two out of three are 1, the sum A_i + B_i + C_i will
        overflow, leaving a carry bit of 1 (the result of majority for that bit).

        Maj can be encoded by

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Odd:
              2^21 * Odd.11a + 2^10 * Odd.11b + Odd.10
            = Odd

        3) asserting the major identity regarding the spreaded values:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10)
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             = ~A + ~B + ~C

        The output is Odd.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0   |     A1   | T1 |    A2   |    A3    |  A4 | A5 | A6 |
        |----|---------|----------|----|---------|----------|-----|----|----|
        | 11 | Odd.11a | ~Odd.11a | 11 | Evn.11a | ~Evn.11a | Odd | ~A | ~B |
        | 11 | Odd.11b | ~Odd.11b | 11 | Evn.11b | ~Evn.11b |     | ~C |    | <- q_maj
        | 10 | Odd.10  | ~Odd.10  | 10 | Evn.10  | ~Evn.10  |     |    |    |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Maj(A, B, C)",
            |mut region| {
                self.config().q_maj.enable(&mut region, 1)?;

                sprdd_a.0.copy_advice(|| "~A", &mut region, adv_cols[5], 0)?;
                sprdd_b.0.copy_advice(|| "~B", &mut region, adv_cols[6], 0)?;
                sprdd_c.0.copy_advice(|| "~C", &mut region, adv_cols[5], 1)?;

                let val_of_sprdd_forms: Value<[u64; 3]> = Value::from_iter([
                    sprdd_a.0.value().copied().map(fe_to_u64),
                    sprdd_b.0.value().copied().map(fe_to_u64),
                    sprdd_c.0.value().copied().map(fe_to_u64),
                ])
                .map(|sprdd_forms: Vec<u64>| sprdd_forms.try_into().unwrap());

                self.assign_sprdd_11_11_10(
                    &mut region,
                    val_of_sprdd_forms.map(spreaded_maj),
                    Parity::Odd,
                    0,
                )
            },
        )
    }

    /// Computes Ch(E, F, G)
    fn ch(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_E: &AssignedSpreaded<F, 32>,
        sprdd_F: &AssignedSpreaded<F, 32>,
        sprdd_G: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We need to compute:
            Ch(E, F, G) = (E ∧ F) ⊕ (¬E ∧ G)

        which can be achieved by

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd,
           for both (~E + ~F) and (~(¬E) + ~G):
             Evn_EF: (Evn_EF.11a, Evn_EF.11b, Evn_EF.10)
             Odd_EF: (Odd_EF.11a, Odd_EF.11b, Odd_EF.10)

             Evn_nEG: (Evn_nEG.11a, Evn_nEG.11b, Evn_nEG.10)
             Odd_nEG: (Odd_nEG.11a, Odd_nEG.11b, Odd_nEG.10)

        2) asserting the 11-11-10 decomposition identity for Odd_EF and Odd_nEG:
              2^21 * Odd_EF.11a + 2^10 * Odd_EF.11b + Odd_EF.10
            = Odd_EF

              2^21 * Odd_nEG.11a + 2^10 * Odd_nEG.11b + Odd_nEG.10
            = Odd_nEG

        3) asserting the spreaded addition identity for (~E + ~F) and (~(¬E) + ~G):
              (4^21 * ~Evn_EF.11a + 4^10 * ~Evn_EF.11b + ~Evn_EF.10)
          2 * (4^21 * ~Odd_EF.11a + 4^10 * ~Odd_EF.11b + ~Odd_EF.10)
             = ~E + ~F

              (4^21 * ~Evn_nEG.11a + 4^10 * ~Evn_nEG.11b + ~Evn_nEG.10)
          2 * (4^21 * ~Odd_nEG.11a + 4^10 * ~Odd_nEG.11b + ~Odd_nEG.10)
             = ~(¬E) + ~G

        4) asserting the following two addition identities:
                    Ret = Odd_EF + Odd_nEG
            MASK_EVN_64 = ~E + ~(¬E)

        The output is Ret.

        We distribute these values in the PLONK table as follows.

        | T0 |      A0     |      A1      | T1 |      A2     |      A3      |    A4   |    A5   |      A6     |
        |----|-------------|--------------|----|-------------|--------------|---------|---------|-------------|
        | 11 |  Odd_EF.11a |  ~Odd_EF.11a | 11 |  Evn_EF.11a |  ~Evn_EF.11a | Odd_EF  |   ~E    |      ~F     |
        | 11 |  Odd_EF.11b |  ~Odd_EF.11b | 11 |  Evn_EF.11b |  ~Evn_EF.11b | Odd_EF  | Odd_nEG |     Ret     | <- q_ch
        | 10 |  Odd_EF.10  |   ~Odd_EF.10 | 10 |  Evn_EF.10  |  ~Evn_EF.10  |         |         |             |
        | 11 | Odd_nEG.11a | ~Odd_nEG.11a | 11 | Evn_nEG.11a | ~Evn_nEG.11a | Odd_nEG |  ~(¬E)  |      ~G     |
        | 11 | Odd_nEG.11b | ~Odd_nEG.11b | 11 | Evn_nEG.11b | ~Evn_nEG.11b |   ~E    |  ~(¬E)  | MASK_EVN_64 | <- q_ch
        | 10 | Odd_nEG.10  |  ~Odd_nEG.10 | 10 | Evn_nEG.10  | ~Evn_nEG.10  |         |         |             |
        */

        let adv_cols = self.config().advice_cols;

        let sprdd_E_val = sprdd_E.0.value().copied().map(fe_to_u64);
        let sprdd_F_val = sprdd_F.0.value().copied().map(fe_to_u64);
        let sprdd_G_val = sprdd_G.0.value().copied().map(fe_to_u64);
        let sprdd_nE_val = sprdd_E_val.map(negate_spreaded);

        let EpF_val = sprdd_E_val + sprdd_F_val;
        let nEpG_val = sprdd_nE_val + sprdd_G_val;
        let sprdd_nE_val: Value<F> = sprdd_nE_val.map(u64_to_fe);

        let mask_evn_64: AssignedNative<F> =
            self.native_gadget.assign_fixed(layouter, F::from(MASK_EVN_64))?;

        layouter.assign_region(
            || "Ch(E, F, G)",
            |mut region| {
                self.config().q_half_ch.enable(&mut region, 1)?;
                self.config().q_half_ch.enable(&mut region, 4)?;

                sprdd_E.0.copy_advice(|| "~E", &mut region, adv_cols[5], 0)?;
                sprdd_E.0.copy_advice(|| "~E", &mut region, adv_cols[4], 4)?;

                sprdd_F.0.copy_advice(|| "~F", &mut region, adv_cols[6], 0)?;
                sprdd_G.0.copy_advice(|| "~G", &mut region, adv_cols[6], 3)?;

                let sprdd_nE = region.assign_advice(|| "~(¬E)", adv_cols[5], 3, || sprdd_nE_val)?;
                sprdd_nE.copy_advice(|| "~(¬E)", &mut region, adv_cols[5], 4)?;

                mask_evn_64.copy_advice(|| "MASK_EVN_64", &mut region, adv_cols[6], 4)?;

                let odd_EF = self.assign_sprdd_11_11_10(&mut region, EpF_val, Parity::Odd, 0)?;
                odd_EF.0.copy_advice(|| "Odd_EF", &mut region, adv_cols[4], 1)?;

                let odd_nEG = self.assign_sprdd_11_11_10(&mut region, nEpG_val, Parity::Odd, 3)?;
                odd_nEG.0.copy_advice(|| "Odd_nEG", &mut region, adv_cols[5], 1)?;

                let ret_val = odd_EF.0.value().copied() + odd_nEG.0.value().copied();
                region
                    .assign_advice(|| "Ret", adv_cols[6], 1, || ret_val)
                    .map(AssignedPlain::<F, 32>)
            },
        )
    }

    /// Computes Σ₀(A).
    fn Sigma_0(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &LimbsOfA<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        Given
                    A:  ( A.10 || A.09 || A.11 || A.02 )

        We need to compute:
            A >>>  2 :  ( A.02 || A.10 || A.09 || A.11 )
          ⊕ A >>> 13 :  ( A.11 || A.02 || A.10 || A.09 )
          ⊕ A >>> 22 :  ( A.09 || A.11 || A.02 || A.10 )

        which can be achieved by

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Evn:
              2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             = 4^30 * ~A.02 + 4^20 * ~A.10 + 4^11 * ~A.09 + ~A.11
             + 4^21 * ~A.11 + 4^19 * ~A.02 + 4^9  * ~A.10 + ~A.09
             + 4^23 * ~A.09 + 4^12 * ~A.11 + 4^10 * ~A.02 + ~A.10

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |   A5  |   A6  |
        |----|---------|----------|----|---------|----------|-----|-------|-------|
        | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn | ~A.10 | ~A.09 |
        | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     | ~A.11 | ~A.02 | <- q_Sigma_0
        | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₀(A)",
            |mut region| {
                self.config().q_Sigma_0.enable(&mut region, 1)?;

                // Copy and assign the input.
                a.spreaded_limb_10.0.copy_advice(|| "~A.10", &mut region, adv_cols[5], 0)?;
                a.spreaded_limb_09.0.copy_advice(|| "~A.09", &mut region, adv_cols[6], 0)?;
                a.spreaded_limb_11.0.copy_advice(|| "~A.11", &mut region, adv_cols[5], 1)?;
                a.spreaded_limb_02.0.copy_advice(|| "~A.02", &mut region, adv_cols[6], 1)?;

                // Compute the spreaded Σ₀(A) off-circuit, assign the 11-11-10 limbs
                // of its even and odd bits into the circuit, enable the q_11_11_10 selector
                // for the even part and q_lookup selector for the related rows, return the
                // assigned 32 even bits.
                let val_of_sprdd_limbs: Value<[u64; 4]> = Value::from_iter([
                    a.spreaded_limb_10.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_09.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_11.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_02.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                self.assign_sprdd_11_11_10(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_Sigma_0),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Computes Σ₁(E).
    fn Sigma_1(
        &self,
        layouter: &mut impl Layouter<F>,
        e: &LimbsOfE<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        Given
                    E:  ( E.07 || E.12 || E.02 || E.05 || E.06 )

        We need to compute:
            E >>>  6 :  ( E.06 || E.07 || E.12 || E.02 || E.05 )
          ⊕ E >>> 11 :  ( E.05 || E.06 || E.07 || E.12 || E.02 )
          ⊕ E >>> 25 :  ( E.12 || E.02 || E.05 || E.06 || E.07 )

        which can be achieved by

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Evn:
              2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
            = Evn

         3) asserting the Sigma_1 identity regarding the spreaded values:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             = 4^26 * ~E.06 + 4^19 * ~E.07 + 4^7  * ~E.12 + 4^5 * ~E.02 + ~E.05
             + 4^27 * ~E.05 + 4^21 * ~E.06 + 4^14 * ~E.07 + 4^2 * ~E.12 + ~E.02
             + 4^20 * ~E.12 + 4^18 * ~E.02 + 4^13 * ~E.05 + 4^7 * ~E.06 + ~E.07

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |  A5  |   A6  |
        |----|---------|----------|----|---------|----------|-----|------|-------|
        | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn | ~E.7 | ~E.12 |
        | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     | ~E.2 | ~E.5  | <- q_Sigma_1
        | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     | ~E.6 |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₁(E)",
            |mut region| {
                self.config().q_Sigma_1.enable(&mut region, 1)?;

                // Copy and assign the input.
                e.spreaded_limb_07.0.copy_advice(|| "~E.07", &mut region, adv_cols[5], 0)?;
                e.spreaded_limb_12.0.copy_advice(|| "~E.12", &mut region, adv_cols[6], 0)?;
                e.spreaded_limb_02.0.copy_advice(|| "~E.02", &mut region, adv_cols[5], 1)?;
                e.spreaded_limb_05.0.copy_advice(|| "~E.05", &mut region, adv_cols[6], 1)?;
                e.spreaded_limb_06.0.copy_advice(|| "~E.06", &mut region, adv_cols[5], 2)?;

                // Compute the spreaded Σ₁(E) off-circuit, assign the 11-11-10 limbs
                // of its even and odd bits into the circuit, enable the q_11_11_10 selector
                // for the even part and q_lookup selector for the related rows, return the
                // assigned 32 even bits.
                let val_of_sprdd_limbs: Value<[u64; 5]> = Value::from_iter([
                    e.spreaded_limb_07.0.value().copied().map(fe_to_u64),
                    e.spreaded_limb_12.0.value().copied().map(fe_to_u64),
                    e.spreaded_limb_02.0.value().copied().map(fe_to_u64),
                    e.spreaded_limb_05.0.value().copied().map(fe_to_u64),
                    e.spreaded_limb_06.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                self.assign_sprdd_11_11_10(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_Sigma_1),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Computes σ₀(W).
    fn sigma_0(
        &self,
        layouter: &mut impl Layouter<F>,
        w: &AssignedMessageWord<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        Given
                    W:  ( W.12 || W.1a || W.1b || W.1c || W.07 || W.3a || W.04 || W.3b )

         We need to compute:
            W  >>  3 :          ( W.12 || W.1a || W.1b || W.1c || W.07 || W.3a || W.04 )
          ⊕ W >>>  7 :  ( W.04 || W.3b || W.12 || W.1a || W.1b || W.1c || W.07 || W.3a )
          ⊕ W >>> 18 :  ( W.1c || W.07 || W.3a || W.04 || W.3b || W.12 || W.1a || W.1b )

        which can be achieved by

         1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Evn:
              2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
            = Evn

        3) asserting the sigma_0 identity regarding the spreaded values:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             =                4^17 * ~W.12 + 4^16 * ~W.1a + 4^15 * ~W.1b + 4^14 * ~W.1c +  4^7 * ~W.07 + 4^4 * ~W.3a + ~W.04
             + 4^28 * ~W.04 + 4^25 * ~W.3b + 4^13 * ~W.12 + 4^12 * ~W.1a + 4^11 * ~W.1b + 4^10 * ~W.1c + 4^3 * ~W.07 + ~W.3a
             + 4^31 * ~W.1c + 4^24 * ~W.07 + 4^21 * ~W.3a + 4^17 * ~W.04 + 4^14 * ~W.3b +  4^2 * ~W.12 + 4^1 * ~W.1a + ~W.1b

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |   A_2   |    A3    |   A4  |   A5  |   A6  |
        |----|----------|-----------|----|---------|----------|-------|-------|-------|
        | 11 | Even.11a | ~Even.11a | 11 | Odd.11a | ~Odd.11a |  Evn  | ~W.12 | ~W.1a |
        | 11 | Even.11b | ~Even.11b | 11 | Odd.11b | ~Odd.11b | ~W.1b | ~W.1c | ~W.7  | <- q_sigma_0
        | 10 | Even.10  | ~Even.10  | 10 | Odd.10  | ~Odd.10  | ~W.3a | ~W.4  | ~W.3b |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "σ₀(W)",
            |mut region| {
                self.config().q_sigma_0.enable(&mut region, 1)?;

                w.spreaded_w_12.0.copy_advice(|| "~W.12", &mut region, adv_cols[5], 0)?;
                w.spreaded_w_1a.0.copy_advice(|| "~W.1a", &mut region, adv_cols[6], 0)?;
                w.spreaded_w_1b.0.copy_advice(|| "~W.1b", &mut region, adv_cols[4], 1)?;
                w.spreaded_w_1c.0.copy_advice(|| "~W.1c", &mut region, adv_cols[5], 1)?;
                w.spreaded_w_07.0.copy_advice(|| "~W.07", &mut region, adv_cols[6], 1)?;
                w.spreaded_w_3a.0.copy_advice(|| "~W.3a", &mut region, adv_cols[4], 2)?;
                w.spreaded_w_04.0.copy_advice(|| "~W.04", &mut region, adv_cols[5], 2)?;
                w.spreaded_w_3b.0.copy_advice(|| "~W.3b", &mut region, adv_cols[6], 2)?;

                let val_of_sprdd_limbs: Value<[u64; 8]> = Value::from_iter([
                    w.spreaded_w_12.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_1a.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_1b.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_1c.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_07.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_3a.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_04.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_3b.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                self.assign_sprdd_11_11_10(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_sigma_0),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Computes σ₁(W).
    fn sigma_1(
        &self,
        layouter: &mut impl Layouter<F>,
        w: &AssignedMessageWord<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        Given
                    W:  ( W.12 || W.1a || W.1b || W.1c || W.07 || W.3a || W.04 || W.3b )

         We need to compute:
            W  >> 10 :                          ( W.12 || W.1a || W.1b || W.1c || W.07 )
          ⊕ W >>> 17 :  ( W.07 || W.3a || W.04 || W.3b || W.12 || W.1a || W.1b || W.1c )
          ⊕ W >>> 19 :  ( W.1b || W.1c || W.07 || W.3a || W.04 || W.3b || W.12 || W.1a )

        which can be achieved by

         1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Evn:
              2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
            = Evn

        3) asserting the sigma_0 identity regarding the spreaded values:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             =                                              4^10 * ~W.12 +  4^9 * ~W.1a +  4^8 * ~W.1b + 4^7 * ~W.1c + ~W.07
             + 4^25 * ~W.07 + 4^22 * ~W.3a + 4^18 * ~W.04 + 4^15 * ~W.3b +  4^3 * ~W.12 +  4^2 * ~W.1a + 4^1 * ~W.1b + ~W.1c
             + 4^31 * ~W.1b + 4^30 * ~W.1c + 4^23 * ~W.07 + 4^20 * ~W.3a + 4^16 * ~W.04 + 4^13 * ~W.3b + 4^1 * ~W.12 + ~W.1a

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |    A2   |    A3    |   A4  |   A5  |   A6  |
        |----|----------|-----------|----|---------|----------|-------|-------|-------|
        | 11 | Even.11a | ~Even.11a | 11 | Odd.11a | ~Odd.11a |  Evn  | ~W.12 | ~W.1a |
        | 11 | Even.11b | ~Even.11b | 11 | Odd.11b | ~Odd.11b | ~W.1b | ~W.1c | ~W.7  | <- q_sigma_1
        | 10 | Even.10  | ~Even.10  | 10 | Odd.10  | ~Odd.10  | ~W.3a | ~W.4  | ~W.3b |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "σ₁(W)",
            |mut region| {
                self.config().q_sigma_1.enable(&mut region, 1)?;

                w.spreaded_w_12.0.copy_advice(|| "~W.12", &mut region, adv_cols[5], 0)?;
                w.spreaded_w_1a.0.copy_advice(|| "~W.1a", &mut region, adv_cols[6], 0)?;
                w.spreaded_w_1b.0.copy_advice(|| "~W.1b", &mut region, adv_cols[4], 1)?;
                w.spreaded_w_1c.0.copy_advice(|| "~W.1c", &mut region, adv_cols[5], 1)?;
                w.spreaded_w_07.0.copy_advice(|| "~W.07", &mut region, adv_cols[6], 1)?;
                w.spreaded_w_3a.0.copy_advice(|| "~W.3a", &mut region, adv_cols[4], 2)?;
                w.spreaded_w_04.0.copy_advice(|| "~W.04", &mut region, adv_cols[5], 2)?;
                w.spreaded_w_3b.0.copy_advice(|| "~W.3b", &mut region, adv_cols[6], 2)?;

                let val_of_sprdd_limbs: Value<[u64; 8]> = Value::from_iter([
                    w.spreaded_w_12.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_1a.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_1b.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_1c.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_07.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_3a.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_04.0.value().copied().map(fe_to_u64),
                    w.spreaded_w_3b.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                self.assign_sprdd_11_11_10(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_sigma_1),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Given a u64, representing a spreaded value, this function fills a
    /// lookup table with the limbs of its even and odd parts (or vice versa)
    /// and returns the former or the latter, depending on the desired value
    /// `even_or_odd`.
    ///
    /// If `even_or_odd` = `Parity::Evn`:
    ///
    ///  | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |
    ///  |----|---------|----------|----|---------|----------|-----|
    ///  | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn |
    ///  | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     | <- q_11_11_10
    ///  | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |
    ///
    /// and returns `Evn`.
    ///
    /// If `even_or_odd` = `Parity::Odd`:
    ///
    ///  | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |
    ///  |----|---------|----------|----|---------|----------|-----|
    ///  | 11 | Odd.11a | ~Odd.11a | 11 | Evn.11a | ~Evn.11a | Odd |
    ///  | 11 | Odd.11b | ~Odd.11b | 11 | Evn.11b | ~Evn.11b |     | <- q_11_11_10
    ///  | 10 | Odd.10  | ~Odd.10  | 10 | Evn.10  | ~Evn.10  |     |
    ///
    /// and returns `Odd`.
    ///
    /// This function guarantees that the returned value is consistent with
    /// the values in the filled lookup table.
    fn assign_sprdd_11_11_10(
        &self,
        region: &mut Region<'_, F>,
        value: Value<u64>,
        even_or_odd: Parity,
        offset: usize,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        self.config().q_11_11_10.enable(region, offset + 1)?;

        let (evn_val, odd_val) = value.map(get_even_and_odd_bits).unzip();

        let [evn_11a, evn_11b, evn_10] =
            evn_val.map(|v| u32_in_be_limbs(v, [11, 11, 10])).transpose_array();

        let [odd_11a, odd_11b, odd_10] =
            odd_val.map(|v| u32_in_be_limbs(v, [11, 11, 10])).transpose_array();

        let idx = match even_or_odd {
            Parity::Evn => 0,
            Parity::Odd => 1,
        };

        self.assign_plain_and_spreaded::<11>(region, evn_11a, offset, idx)?;
        self.assign_plain_and_spreaded::<11>(region, evn_11b, offset + 1, idx)?;
        self.assign_plain_and_spreaded::<10>(region, evn_10, offset + 2, idx)?;

        self.assign_plain_and_spreaded::<11>(region, odd_11a, offset, 1 - idx)?;
        self.assign_plain_and_spreaded::<11>(region, odd_11b, offset + 1, 1 - idx)?;
        self.assign_plain_and_spreaded::<10>(region, odd_10, offset + 2, 1 - idx)?;

        let out_col = self.config().advice_cols[4];
        match even_or_odd {
            Parity::Evn => {
                region.assign_advice(|| "Evn", out_col, offset, || evn_val.map(u32_to_fe))
            }
            Parity::Odd => {
                region.assign_advice(|| "Odd", out_col, offset, || odd_val.map(u32_to_fe))
            }
        }
        .map(AssignedPlain)
    }

    /// Given a slice of at most 7 `AssignedPlain` values, it adds them
    /// modulo 2^32 and decomposes the result (named A) into (big-endian)
    /// limbs of bit sizes 10, 9, 11 and 2.
    ///
    /// This function returns the plain and spreaded forms, as well as
    /// the spreaded limbs of A.
    fn prepare_A(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 32>],
    ) -> Result<LimbsOfA<F>, Error> {
        /*
        Given assigned plain inputs S0, ..., S6 (if fewer inputs are given
        they will be completed up to length 7, padding with fixed zeros),
        let A be their sum modulo 2^32.

        We use the following table distribution.

        | T0 |  A0  |  A1   | T1 |   A2  |   A3   | A4 | A5 | A6 |
        |----|------|-------|----|-------|--------|----|----|----|
        | 10 | A.10 | ~A.10 |  9 |  A.9  |  ~A.9  |  A | S0 | S1 |
        | 11 | A.11 | ~A.11 |  2 |  A.2  |  ~A.2  | ~A | S2 | S3 | <- q_10_9_11_2
        |  0 |   0  |   0   |  3 | carry | ~carry | S4 | S5 | S6 |

        Apart from the lookups, the following identities are checked via a
        custom gate with selector q_10_9_11_2:

            A = 2^22 *  A.10 + 2^13 *  A.9 + 2^2 *  A.11 +  A.2
           ~A = 4^22 * ~A.10 + 4^13 * ~A.9 + 4^2 * ~A.11 + ~A.2

        and the following is checked with a custom gate with selector
        q_add_mod_2_32:

            S0 + S1 + S2 + S3 + S4 + S5 + S6 = A + carry * 2^32

        Note that A is implicitly being range-checked in [0, 2^32) via
        the lookup, and the carry is range-checked in [0, 8). This makes
        the gate complete and sound (the range on the carry does not need
        to be tight as long as it prevents overflows in the native field).
        */

        let zero = AssignedPlain::<F, 32>::fixed(layouter, &self.native_gadget, 0)?;

        layouter.assign_region(
            || "decompose A in 10-9-11-2",
            |mut region| {
                self.config().q_10_9_11_2.enable(&mut region, 1)?;

                let a_plain = self.assign_add_mod_2_32(&mut region, summands, &zero)?;
                let a_sprdd_val =
                    a_plain.0.value().copied().map(fe_to_u32).map(spread).map(u64_to_fe);
                let a_sprdd = region
                    .assign_advice(|| "~A", self.config().advice_cols[4], 1, || a_sprdd_val)
                    .map(AssignedSpreaded)?;

                let [val_10, val_09, val_11, val_02] = (a_plain.0.value().copied())
                    .map(|a| u32_in_be_limbs(fe_to_u32(a), [10, 9, 11, 2]))
                    .transpose_array();

                let limb_10 = self.assign_plain_and_spreaded(&mut region, val_10, 0, 0)?;
                let limb_09 = self.assign_plain_and_spreaded(&mut region, val_09, 0, 1)?;
                let limb_11 = self.assign_plain_and_spreaded(&mut region, val_11, 1, 0)?;
                let limb_02 = self.assign_plain_and_spreaded(&mut region, val_02, 1, 1)?;
                let _zeros =
                    self.assign_plain_and_spreaded::<0>(&mut region, Value::known(0), 2, 0)?;

                Ok(LimbsOfA {
                    combined: AssignedPlainSpreaded {
                        plain: a_plain,
                        spreaded: a_sprdd,
                    },
                    spreaded_limb_10: limb_10.spreaded,
                    spreaded_limb_09: limb_09.spreaded,
                    spreaded_limb_11: limb_11.spreaded,
                    spreaded_limb_02: limb_02.spreaded,
                })
            },
        )
    }

    /// Given a slice of at most 7 `AssignedPlain` values, it adds them
    /// modulo 2^32 and decomposes the result (named E) into (big-endian)
    /// limbs of bit sizes 7, 12, 2, 5 and 6.
    ///
    /// This function returns the plain and spreaded forms, as well as
    /// the spreaded limbs of E.
    fn prepare_E(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 32>],
    ) -> Result<LimbsOfE<F>, Error> {
        /*
        Given assigned plain inputs S0, ..., S6 (if fewer inputs are given
        they will be completed up to length 7, padding with fixed zeros),
        let E be their sum modulo 2^32.

        | T0 |  A0  |   A1  | T1 |   A2  |   A3   | A4 | A5 | A6 |
        |----|------|-------|----|-------|--------|----|----|----|
        |  7 | E.07 | ~E.07 | 12 |  E.12 |  ~E.12 |  E | S0 | S1 |
        |  2 | E.02 | ~E.02 |  5 |  E.5  |  ~E.5  | ~E | S2 | S3 | <- q_7_12_2_5_6
        |  6 | E.06 | ~E.06 |  3 | carry | ~carry | S4 | S5 | S6 |

        Apart from the lookups, the following identities are checked via a
        custom gate with selector q_7_12_2_5_6:

            E = 2^25 *  E.07 + 2^13 *  E.12 + 2^11 *  E.02 + 2^6 *  E.05 +  E.06
           ~E = 4^25 * ~E.07 + 4^13 * ~E.12 + 4^11 * ~E.02 + 4^6 * ~E.05 + ~E.06

        and the following is checked with a custom gate with selector
        q_add_mod_2_32:

            S0 + S1 + S2 + S3 + S4 + S5 + S6 = E + carry * 2^32

        Note that E is implicitly being range-checked in [0, 2^32) via
        the lookup, and the carry is range-checked in [0, 8). This makes
        the gate complete and sound (the range on the carry does not need
        to be tight as long as it prevents overflows in the native field).
        */

        let zero = AssignedPlain::<F, 32>::fixed(layouter, &self.native_gadget, 0)?;

        layouter.assign_region(
            || "decompose E in 7-12-2-5-6",
            |mut region| {
                self.config().q_7_12_2_5_6.enable(&mut region, 1)?;

                let e_plain = self.assign_add_mod_2_32(&mut region, summands, &zero)?;
                let e_sprdd_val =
                    (e_plain.0.value().copied()).map(fe_to_u32).map(spread).map(u64_to_fe);
                let e_sprdd = region
                    .assign_advice(|| "~E", self.config().advice_cols[4], 1, || e_sprdd_val)
                    .map(AssignedSpreaded)?;

                let [val_07, val_12, val_02, val_05, val_06] = (e_plain.0.value().copied())
                    .map(|e| u32_in_be_limbs(fe_to_u32(e), [7, 12, 2, 5, 6]))
                    .transpose_array();

                let limb_07 = self.assign_plain_and_spreaded(&mut region, val_07, 0, 0)?;
                let limb_12 = self.assign_plain_and_spreaded(&mut region, val_12, 0, 1)?;
                let limb_02 = self.assign_plain_and_spreaded(&mut region, val_02, 1, 0)?;
                let limb_05 = self.assign_plain_and_spreaded(&mut region, val_05, 1, 1)?;
                let limb_06 = self.assign_plain_and_spreaded(&mut region, val_06, 2, 0)?;

                Ok(LimbsOfE {
                    combined: AssignedPlainSpreaded {
                        plain: e_plain,
                        spreaded: e_sprdd,
                    },
                    spreaded_limb_07: limb_07.spreaded,
                    spreaded_limb_12: limb_12.spreaded,
                    spreaded_limb_02: limb_02.spreaded,
                    spreaded_limb_05: limb_05.spreaded,
                    spreaded_limb_06: limb_06.spreaded,
                })
            },
        )
    }

    /// Given a slice of at most 7 `AssignedPlain` values, this function adds
    /// them modulo 2^32 and decomposes the result (named W_i) into (big-endian)
    /// limbs of bit sizes 12, 1, 1, 1, 7, 3, 4 and 3.
    fn prepare_message_word(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 32>],
    ) -> Result<AssignedMessageWord<F>, Error> {
        /*
        Given assigned plain inputs S0, ..., S6 (if fewer inputs are given
        they will be completed up to length 7, padding with fixed zeros),
        and computes W.i as their sum modulo 2^32.

        We use the following table distribution.

        | T0 |  A0  |   A1  | T1 |   A2  |   A3   |  A4 | A5 | A6 |  A7  |
        |----|------|-------|----|-------|--------|-----|----|----|------|
        | 12 | W.12 | ~W.12 |  7 |  W.07 | ~W.07  | W.i | S0 | S1 | W.1a |
        |  3 | W.3a | ~W.3a |  4 |  W.04 | ~W.04  |     | S2 | S3 | W.1b | <- q_12_1x3_7_3_4_3
        |  3 | W.3b | ~W.3b |  3 | carry | ~carry |  S4 | S5 | S6 | W.1c |

        Apart from the lookups, the following identities are checked via a
        custom gate with selector q_12_1x3_7_3_4_3:

          W.i =   2^20 * W.12 + 2^19 * W.1a + 2^18 * W.1b + 2^17 * W.1c
                + 2^10 * W.07 + 2^7 * W.3a + 2^3 * W.04 + W.3b

          W.1a * (W.1a - 1) = 0
          W.1b * (W.1b - 1) = 0
          W.1c * (W.1c - 1) = 0

        and the following is checked with a custom gate with selector
        q_add_mod_2_32:

          S0 + S1 + S2 + S3 + S4 + S5 + S6 = W.i + carry * 2^32

        Note that W.i is implicitly being range-checked in [0, 2^32) via
        the lookup, and the carry is range-checked in [0, 8). This makes
        the gate complete and sound (the range on the carry does not need
        to be tight as long as it prevents overflows in the native field).
        */

        let zero = AssignedPlain::<F, 32>::fixed(layouter, &self.native_gadget, 0)?;

        layouter.assign_region(
            || "prepare message word",
            |mut region| {
                self.config().q_12_1x3_7_3_4_3.enable(&mut region, 1)?;

                let w_i_plain = self.assign_add_mod_2_32(&mut region, summands, &zero)?;

                let [val_12, val_1a, val_1b, val_1c, val_07, val_3a, val_04, val_3b] =
                    (w_i_plain.0.value().copied())
                        .map(|w| u32_in_be_limbs(fe_to_u32(w), [12, 1, 1, 1, 7, 3, 4, 3]))
                        .transpose_array();
                let limb_12 = self.assign_plain_and_spreaded(&mut region, val_12, 0, 0)?;
                let limb_07 = self.assign_plain_and_spreaded(&mut region, val_07, 0, 1)?;
                let limb_3a = self.assign_plain_and_spreaded(&mut region, val_3a, 1, 0)?;
                let limb_04 = self.assign_plain_and_spreaded(&mut region, val_04, 1, 1)?;
                let limb_3b = self.assign_plain_and_spreaded(&mut region, val_3b, 2, 0)?;

                // The spreaded forms of 1-bit values W.1a, W.1b and W.1c equal themselves.
                let col = self.config().advice_cols[7];
                let limb_1a = region.assign_advice(|| "W.1a", col, 0, || val_1a.map(u32_to_fe))?;
                let limb_1b = region.assign_advice(|| "W.1b", col, 1, || val_1b.map(u32_to_fe))?;
                let limb_1c = region.assign_advice(|| "W.1c", col, 2, || val_1c.map(u32_to_fe))?;

                Ok(AssignedMessageWord {
                    combined_plain: w_i_plain,
                    spreaded_w_12: limb_12.spreaded,
                    spreaded_w_1a: AssignedSpreaded(limb_1a),
                    spreaded_w_1b: AssignedSpreaded(limb_1b),
                    spreaded_w_1c: AssignedSpreaded(limb_1c),
                    spreaded_w_07: limb_07.spreaded,
                    spreaded_w_3a: limb_3a.spreaded,
                    spreaded_w_04: limb_04.spreaded,
                    spreaded_w_3b: limb_3b.spreaded,
                })
            },
        )
    }

    /// Given a plain u32 value, supposedly in the range [0, 2^L), assigns it
    /// in plain and spreaded form, returning an `AssignedPlainSpreaded<F, L>`.
    ///
    /// The assigned values are guaranteed to be well-formed and consistent
    /// via a lookup check at the specified offset.
    ///
    /// Note that we have two parallel lookup arguments. The caller must
    /// choose which of the two is used via the `lookup_idx`.
    /// If `lookup_idx = 0`, the lookup on columns (T0, A0, A1) will be used.
    /// If `lookup_idx = 1`, the lookup on columns (T1, A2, A3) will be used.
    ///
    /// # Unsatisfiable Circuit
    ///
    /// If the given value is not in the range [0, 2^L).
    fn assign_plain_and_spreaded<const L: usize>(
        &self,
        region: &mut Region<'_, F>,
        plain_val: Value<u32>,
        offset: usize,
        lookup_idx: usize,
    ) -> Result<AssignedPlainSpreaded<F, L>, Error> {
        self.config().q_lookup.enable(region, offset)?;

        let nbits_col = self.config().fixed_cols[lookup_idx]; // 0 or 1
        let plain_col = self.config().advice_cols[2 * lookup_idx]; // 0 or 2
        let sprdd_col = self.config().advice_cols[2 * lookup_idx + 1]; // 1 or 3

        let nbits_val = Value::known(F::from(L as u64));
        let sprdd_val = plain_val.map(spread).map(u64_to_fe);
        let plain_val = plain_val.map(u32_to_fe);

        region.assign_fixed(|| "nbits", nbits_col, offset, || nbits_val)?;
        let plain = region.assign_advice(|| "plain", plain_col, offset, || plain_val)?;
        let spreaded = region.assign_advice(|| "sprdd", sprdd_col, offset, || sprdd_val)?;

        Ok(AssignedPlainSpreaded {
            plain: AssignedPlain(plain),
            spreaded: AssignedSpreaded(spreaded),
        })
    }

    /// Given a slice of at most 7 `AssignedPlain` values, this function adds
    /// them modulo 2^32.
    ///
    /// The `zero` argument is supposed to contain a fixed assigned plain
    /// containing value 0, this is not enforced in this function, it is the
    /// responsibility of the caller to do so.
    ///
    /// # Panics
    ///
    /// If the more than 7 summands are provided.
    fn assign_add_mod_2_32(
        &self,
        region: &mut Region<'_, F>,
        summands: &[AssignedPlain<F, 32>],
        zero: &AssignedPlain<F, 32>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We distribute values in the PLONK table as follows.

        | T1 |   A2  |   A3   |     A4    | A5 | A6 |
        |----|-------|--------|-----------|----|----|
        |    |       |        | sum_plain | S0 | S1 |
        |    |       |        |           | S2 | S3 | <- q_add_mod_2_32
        |  3 | carry | ~carry |     S4    | S5 | S6 |

        We enforce S0 + S1 + S2 + S3 + S4 + S5 + S6 = sum_plain + carry * 2^32.
        */

        assert!(summands.len() <= 7);

        self.config().q_add_mod_2_32.enable(region, 1)?;
        let adv_cols = self.config().advice_cols;

        let mut summands = summands.to_vec();
        summands.resize(7, zero.clone());

        let (carry_val, sum_val): (Value<u32>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u64).sum())
                .map(|s: u64| s.div_rem(&(1 << 32)))
                .map(|(carry, r)| (carry as u32, u64_to_fe(r)))
                .unzip();

        summands[0].0.copy_advice(|| "S0", region, adv_cols[5], 0)?;
        summands[1].0.copy_advice(|| "S1", region, adv_cols[6], 0)?;
        summands[2].0.copy_advice(|| "S2", region, adv_cols[5], 1)?;
        summands[3].0.copy_advice(|| "S3", region, adv_cols[6], 1)?;
        summands[4].0.copy_advice(|| "S4", region, adv_cols[4], 2)?;
        summands[5].0.copy_advice(|| "S5", region, adv_cols[5], 2)?;
        summands[6].0.copy_advice(|| "S6", region, adv_cols[6], 2)?;
        let _carry: AssignedPlainSpreaded<F, 3> =
            self.assign_plain_and_spreaded(region, carry_val, 2, 1)?;
        region.assign_advice(|| "sum", adv_cols[4], 0, || sum_val).map(AssignedPlain)
    }
}

impl<F: PrimeField> CompressionState<F> {
    /// Adds pair-wise (modulo 2^32) the fields of two compression states.
    pub fn add(
        &self,
        sha256_chip: &Sha256Chip<F>,
        layouter: &mut impl Layouter<F>,
        other: &Self,
    ) -> Result<Self, Error> {
        let a = sha256_chip.prepare_A(layouter, &[self.a.plain(), other.a.plain()])?;
        let b = sha256_chip.prepare_A(layouter, &[self.b.plain.clone(), other.b.plain.clone()])?;
        let c = sha256_chip.prepare_A(layouter, &[self.c.plain.clone(), other.c.plain.clone()])?;
        let d = sha256_chip.prepare_A(layouter, &[self.d.clone(), other.d.clone()])?;
        // NB: d can be optimized and do it in a single row without `prepare_A`.

        let e = sha256_chip.prepare_E(layouter, &[self.e.plain(), other.e.plain()])?;
        let f = sha256_chip.prepare_E(layouter, &[self.f.plain.clone(), other.f.plain.clone()])?;
        let g = sha256_chip.prepare_E(layouter, &[self.g.plain.clone(), other.g.plain.clone()])?;
        let h = sha256_chip.prepare_E(layouter, &[self.h.clone(), other.h.clone()])?;
        // NB: h can be optimized and do it in a single row without `prepare_E`.

        Ok(Self {
            a,
            b: b.combined,
            c: c.combined,
            d: d.combined.plain,
            e,
            f: f.combined,
            g: g.combined,
            h: h.combined.plain,
        })
    }
}

#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::Instance;

#[cfg(any(test, feature = "testing"))]
use crate::{field::decomposition::chip::P2RDecompositionConfig, testing_utils::FromScratch};

#[cfg(any(test, feature = "testing"))]
impl<F: PrimeField> FromScratch<F> for Sha256Chip<F> {
    type Config = (Sha256Config, P2RDecompositionConfig);

    fn new_from_scratch(config: &Self::Config) -> Self {
        Self {
            config: config.0.clone(),
            native_gadget: NativeGadget::new_from_scratch(&config.1),
        }
    }

    fn configure_from_scratch(
        meta: &mut ConstraintSystem<F>,
        instance_columns: &[Column<Instance>; 2],
    ) -> Self::Config {
        use std::cmp::max;

        use crate::field::{
            decomposition::pow2range::Pow2RangeChip,
            native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
        };

        let advice_columns = (0..max(NB_ARITH_COLS, NB_SHA256_ADVICE_COLS))
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let fixed_columns = (0..max(NB_ARITH_FIXED_COLS, NB_SHA256_FIXED_COLS))
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();

        let native_config = NativeChip::configure(
            meta,
            &(
                advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                fixed_columns[..NB_ARITH_FIXED_COLS].try_into().unwrap(),
                *instance_columns,
            ),
        );

        let pow2range_config = Pow2RangeChip::configure(meta, &advice_columns[1..=4]);
        let core_decomposition_config =
            P2RDecompositionChip::configure(meta, &(native_config, pow2range_config));

        let sha256_config = Sha256Chip::configure(
            meta,
            &(
                advice_columns[..NB_SHA256_ADVICE_COLS].try_into().unwrap(),
                fixed_columns[..NB_SHA256_FIXED_COLS].try_into().unwrap(),
            ),
        );

        (sha256_config, core_decomposition_config)
    }

    fn load_from_scratch(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.native_gadget.load_from_scratch(layouter)?;
        self.load(layouter)
    }
}
