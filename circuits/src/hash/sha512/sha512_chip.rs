//! SHA-512 Chip

// A: |-----------|-----|------|--------------|
//        25         5     6         28

//  13-12-5-6-13-13-2

// $Prepare(A)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |   A4   |  A5  |  A6  |
// |----|----------|-----------|----|----------|-----------|--------|------|------|
// | 13 |   A.13a  |  ~A.13a   | 12 |   A.12   |   ~A.12   |   A    |  S0  |  S1  |
// | 05 |   A.05   |  ~A.05    | 06 |   A.06   |   ~A.06   |   ~A   |  S2  |  S3  |
// | 13 |   A.13b  |  ~A.13b   | 13 |   A.13c  |   ~A.13c  |   S4   |  S5  |  S6  |
// | 02 |   A.02   |  ~A.02    | 03 |   carry  |   ~carry  |        |      |      |

// E: |----------|----------|-----|-----------|
//        23          23       4       14

//  13-10-13-10-4-13-1

// $Prepare(E)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |   A4   |  A5  |  A6  |
// |----|----------|-----------|----|----------|-----------|--------|------|------|
// | 13 |   E.13a  |  ~E.13a   | 10 |   E.10a  |   ~E.10a  |   E    |  S0  |  S1  |
// | 13 |   E.13b  |  ~E.13b   | 10 |   E.10b  |   ~E.10b  |   ~E   |  S2  |  S3  |
// | 04 |   E.04   |  ~E.04    | 13 |   E.13c  |   ~E.13c  |   S4   |  S5  |  S6  |
// | 01 |   E.01   |  ~E.01    | 03 |   carry  |   ~carry  |        |      |      |

// message-word:

// |----------------------------------------|-|-----------|-|
//                     56                    1      6      1

// |-----|----------------------------|---------|-----------|
//    3                42                 13         6

// |-----|----------------------------|-----|-|-|---------|-|
//    3                42                11  1 1    5      1

// 3-13-13-13-3-11-1-1-5-1

// $Prepare_Word$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |    A4   |  A5  |  A6  |  A.7  |
// |----|----------|-----------|----|----------|-----------|---------|------|------|-------|
// | 03 |   W.03a  |  ~W.03a   | 13 |   W.13a  |  ~W.13a   |  W.i    |  S0  |  S1  | W.01a |
// | 13 |   W.13b  |  ~W.13b   | 13 |   W.13c  |  ~W.13c   |         |  S2  |  S3  | W.01b |
// | 03 |   W.03b  |  ~W.03b   | 11 |   W.11   |  ~W.11    |   S4    |  S5  |  S6  | W.01c |
// | 05 |   W.05   |  ~W.05    | 03 |   carry  |  ~carry   |         |      |      |       |

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
    hash::sha512::{
        types::{
            AssignedMessageWord, AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded, LimbsOfA,
            LimbsOfE,
        },
        utils::{
            expr_pow2_ip, expr_pow4_ip, gen_spread_table, get_even_and_odd_bits, negate_spreaded,
            spread, spreaded_Sigma_0, spreaded_Sigma_1, spreaded_maj, spreaded_sigma_0,
            spreaded_sigma_1, u64_in_be_limbs, MASK_EVN_128,
        },
    },
    instructions::{assignments::AssignmentInstructions, DecompositionInstructions},
    types::{AssignedByte, AssignedNative},
    utils::{
        util::{fe_to_u128, fe_to_u64, u128_to_fe, u64_to_fe},
        ComposableChip,
    },
};

/// Number of advice columns used by the identities of the SHA512 chip.
pub const NB_SHA512_ADVICE_COLS: usize = 8;

/// Number of fixed columns used by the identities of the SHA512 chip.
pub const NB_SHA512_FIXED_COLS: usize = 2;

const ROUND_CONSTANTS: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

const IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// Tag for the even and odd 13-13-13-13-12 decompositions.
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

/// Configuration of Sha512Chip.
#[derive(Clone, Debug)]
pub struct Sha512Config {
    advice_cols: [Column<Advice>; NB_SHA512_ADVICE_COLS],
    fixed_cols: [Column<Fixed>; NB_SHA512_FIXED_COLS],

    q_lookup: Selector,
    table: SpreadTable,

    q_maj: Selector,
    q_half_ch: Selector,
    q_Sigma_0: Selector,
    q_Sigma_1: Selector,
    q_sigma_0: Selector,
    q_sigma_1: Selector,

    q_13_13_13_13_12: Selector,
    q_13_12_5_6_13_13_2: Selector,
    q_13_10_13_10_4_13_1: Selector,
    q_3_3x13_3_11_1_1_5_1: Selector,
    q_add_mod_2_64: Selector,
}

/// Chip for SHA512.
#[derive(Clone, Debug)]
pub struct Sha512Chip<F: PrimeField> {
    config: Sha512Config,
    pub(super) native_gadget: NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>,
}

impl<F: PrimeField> Chip<F> for Sha512Chip<F> {
    type Config = Sha512Config;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> ComposableChip<F> for Sha512Chip<F> {
    type SharedResources = (
        [Column<Advice>; NB_SHA512_ADVICE_COLS],
        [Column<Fixed>; NB_SHA512_FIXED_COLS],
    );

    type InstructionDeps = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    fn new(config: &Sha512Config, native_gadget: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: native_gadget.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> Sha512Config {
        let advice_cols = shared_res.0;
        let fixed_cols = shared_res.1;

        for (i, column) in advice_cols.iter().enumerate() {
            // A0 and A2 are not involved in the copy-constraint.
            if i != 0 && i != 2 {
                meta.enable_equality(*column);
            }
        }

        let q_lookup = meta.selector();
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

        let q_13_13_13_13_12 = meta.selector();
        let q_13_12_5_6_13_13_2 = meta.selector();
        let q_13_10_13_10_4_13_1 = meta.selector();
        let q_3_3x13_3_11_1_1_5_1 = meta.selector();
        let q_add_mod_2_64 = meta.selector();

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
            let s_odd_13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_odd_13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_odd_13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_13d = meta.query_advice(advice_cols[1], Rotation(2));
            let s_odd_12 = meta.query_advice(advice_cols[1], Rotation(3));
            let s_evn_13a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_evn_13b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_evn_13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s_evn_13d = meta.query_advice(advice_cols[3], Rotation(2));
            let s_evn_12 = meta.query_advice(advice_cols[3], Rotation(3));

            let s_evn = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_evn_13a, &s_evn_13b, &s_evn_13c, &s_evn_13d, &s_evn_12],
            );
            let s_odd = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_odd_13a, &s_odd_13b, &s_odd_13c, &s_odd_13d, &s_odd_12],
            );

            let id = (sA + sB + sC) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_maj, vec![("Maj", id)])
        });

        meta.create_gate("half Ch(E, F, G)", |meta| {
            // See function `ch` for a description of the following layout.
            let sX = meta.query_advice(advice_cols[5], Rotation(-1));
            let sY = meta.query_advice(advice_cols[6], Rotation(-1));
            let s_odd_13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_odd_13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_odd_13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_13d = meta.query_advice(advice_cols[1], Rotation(2));
            let s_odd_12 = meta.query_advice(advice_cols[1], Rotation(3));
            let s_evn_13a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_evn_13b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_evn_13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s_evn_13d = meta.query_advice(advice_cols[3], Rotation(2));
            let s_evn_12 = meta.query_advice(advice_cols[3], Rotation(3));
            let summand_1 = meta.query_advice(advice_cols[4], Rotation(0));
            let summand_2 = meta.query_advice(advice_cols[5], Rotation(0));
            let sum = meta.query_advice(advice_cols[6], Rotation(0));

            let s_evn = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_evn_13a, &s_evn_13b, &s_evn_13c, &s_evn_13d, &s_evn_12],
            );
            let s_odd = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_odd_13a, &s_odd_13b, &s_odd_13c, &s_odd_13d, &s_odd_12],
            );

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
            let s13a = meta.query_advice(advice_cols[5], Rotation(-1));
            let s12 = meta.query_advice(advice_cols[6], Rotation(-1));
            let s05 = meta.query_advice(advice_cols[5], Rotation(0));
            let s06 = meta.query_advice(advice_cols[6], Rotation(0));
            let s13b = meta.query_advice(advice_cols[5], Rotation(1));
            let s13c = meta.query_advice(advice_cols[6], Rotation(1));
            let s02 = meta.query_advice(advice_cols[5], Rotation(2));
            let s_evn_13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_13d = meta.query_advice(advice_cols[1], Rotation(2));
            let s_evn_12 = meta.query_advice(advice_cols[1], Rotation(3));
            let s_odd_13a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_13b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s_odd_13d = meta.query_advice(advice_cols[3], Rotation(2));
            let s_odd_12 = meta.query_advice(advice_cols[3], Rotation(3));

            let s_1st_rot = expr_pow4_ip(
                [51, 38, 36, 23, 11, 6, 0],
                [&s13b, &s13c, &s02, &s13a, &s12, &s05, &s06],
            );
            let s_2nd_rot = expr_pow4_ip(
                [58, 45, 32, 30, 17, 5, 0],
                [&s06, &s13b, &s13c, &s02, &s13a, &s12, &s05],
            );
            let s_3rd_rot = expr_pow4_ip(
                [59, 53, 40, 27, 25, 12, 0],
                [&s05, &s06, &s13b, &s13c, &s02, &s13a, &s12],
            );

            let s_evn = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_evn_13a, &s_evn_13b, &s_evn_13c, &s_evn_13d, &s_evn_12],
            );
            let s_odd = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_odd_13a, &s_odd_13b, &s_odd_13c, &s_odd_13d, &s_odd_12],
            );

            let id = (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_Sigma_0, vec![("Sigma_0", id)])
        });

        meta.create_gate("Σ₁(E)", |meta| {
            // See function `Sigma_1` for a description of the following layout.
            let s13a = meta.query_advice(advice_cols[5], Rotation(-1));
            let s10a = meta.query_advice(advice_cols[6], Rotation(-1));
            let s13b = meta.query_advice(advice_cols[5], Rotation(0));
            let s10b = meta.query_advice(advice_cols[6], Rotation(0));
            let s04 = meta.query_advice(advice_cols[5], Rotation(1));
            let s13c = meta.query_advice(advice_cols[6], Rotation(1));
            let s01 = meta.query_advice(advice_cols[5], Rotation(2));
            let s_evn_13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_13d = meta.query_advice(advice_cols[1], Rotation(2));
            let s_evn_12 = meta.query_advice(advice_cols[1], Rotation(3));
            let s_odd_13a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_13b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s_odd_13d = meta.query_advice(advice_cols[3], Rotation(2));
            let s_odd_12 = meta.query_advice(advice_cols[3], Rotation(3));

            let s_1st_rot = expr_pow4_ip(
                [51, 50, 37, 27, 14, 4, 0],
                [&s13c, &s01, &s13a, &s10a, &s13b, &s10b, &s04],
            );
            let s_2nd_rot = expr_pow4_ip(
                [60, 47, 46, 33, 23, 10, 0],
                [&s04, &s13c, &s01, &s13a, &s10a, &s13b, &s10b],
            );
            let s_3rd_rot = expr_pow4_ip(
                [51, 41, 37, 24, 23, 10, 0],
                [&s13b, &s10b, &s04, &s13c, &s01, &s13a, &s10a],
            );

            let s_evn = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_evn_13a, &s_evn_13b, &s_evn_13c, &s_evn_13d, &s_evn_12],
            );
            let s_odd = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_odd_13a, &s_odd_13b, &s_odd_13c, &s_odd_13d, &s_odd_12],
            );

            let id = (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_Sigma_1, vec![("Sigma_1", id)])
        });

        meta.create_gate("σ₀(W)", |meta| {
            // See function `sigma_0` for a description of the following layout.
            let s03a = meta.query_advice(advice_cols[5], Rotation(-1));
            let s13a = meta.query_advice(advice_cols[6], Rotation(-1));
            let s13b = meta.query_advice(advice_cols[5], Rotation(0));
            let s13c = meta.query_advice(advice_cols[6], Rotation(0));
            let s03b = meta.query_advice(advice_cols[5], Rotation(1));
            let s11 = meta.query_advice(advice_cols[6], Rotation(1));
            let s01a = meta.query_advice(advice_cols[5], Rotation(2));
            let s01b = meta.query_advice(advice_cols[6], Rotation(2));
            let s05 = meta.query_advice(advice_cols[5], Rotation(3));
            let s01c = meta.query_advice(advice_cols[6], Rotation(3));
            let s_evn_13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_13d = meta.query_advice(advice_cols[1], Rotation(2));
            let s_evn_12 = meta.query_advice(advice_cols[1], Rotation(3));
            let s_odd_13a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_13b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s_odd_13d = meta.query_advice(advice_cols[3], Rotation(2));
            let s_odd_12 = meta.query_advice(advice_cols[3], Rotation(3));

            let s_1st_shift = expr_pow4_ip(
                [54, 41, 28, 15, 12, 1, 0],
                [&s03a, &s13a, &s13b, &s13c, &s03b, &s11, &s01a],
            );
            let s_2nd_rot = expr_pow4_ip(
                [63, 60, 47, 34, 21, 18, 7, 6, 5, 0],
                [
                    &s01c, &s03a, &s13a, &s13b, &s13c, &s03b, &s11, &s01a, &s01b, &s05,
                ],
            );
            let s_3rd_rot = expr_pow4_ip(
                [63, 62, 57, 56, 53, 40, 27, 14, 11, 0],
                [
                    &s01a, &s01b, &s05, &s01c, &s03a, &s13a, &s13b, &s13c, &s03b, &s11,
                ],
            );

            let s_evn = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_evn_13a, &s_evn_13b, &s_evn_13c, &s_evn_13d, &s_evn_12],
            );
            let s_odd = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_odd_13a, &s_odd_13b, &s_odd_13c, &s_odd_13d, &s_odd_12],
            );

            let id = (s_1st_shift + s_2nd_rot + s_3rd_rot) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_sigma_0, vec![("sigma_0", id)])
        });

        meta.create_gate("σ₁(W)", |meta| {
            // See function `sigma_1` for a description of the following layout.
            let s03a = meta.query_advice(advice_cols[5], Rotation(-1));
            let s13a = meta.query_advice(advice_cols[6], Rotation(-1));
            let s13b = meta.query_advice(advice_cols[5], Rotation(0));
            let s13c = meta.query_advice(advice_cols[6], Rotation(0));
            let s03b = meta.query_advice(advice_cols[5], Rotation(1));
            let s11 = meta.query_advice(advice_cols[6], Rotation(1));
            let s01a = meta.query_advice(advice_cols[5], Rotation(2));
            let s01b = meta.query_advice(advice_cols[6], Rotation(2));
            let s05 = meta.query_advice(advice_cols[5], Rotation(3));
            let s01c = meta.query_advice(advice_cols[6], Rotation(3));
            let s_evn_13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_13d = meta.query_advice(advice_cols[1], Rotation(2));
            let s_evn_12 = meta.query_advice(advice_cols[1], Rotation(3));
            let s_odd_13a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_13b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s_odd_13d = meta.query_advice(advice_cols[3], Rotation(2));
            let s_odd_12 = meta.query_advice(advice_cols[3], Rotation(3));

            let s_1st_shift = expr_pow4_ip(
                [55, 42, 29, 16, 13, 2, 1, 0],
                [&s03a, &s13a, &s13b, &s13c, &s03b, &s11, &s01a, &s01b],
            );
            let s_2nd_rot = expr_pow4_ip(
                [53, 52, 51, 46, 45, 42, 29, 16, 3, 0],
                [
                    &s11, &s01a, &s01b, &s05, &s01c, &s03a, &s13a, &s13b, &s13c, &s03b,
                ],
            );
            let s_3rd_rot = expr_pow4_ip(
                [51, 38, 25, 22, 11, 10, 9, 4, 3, 0],
                [
                    &s13a, &s13b, &s13c, &s03b, &s11, &s01a, &s01b, &s05, &s01c, &s03a,
                ],
            );

            let s_evn = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_evn_13a, &s_evn_13b, &s_evn_13c, &s_evn_13d, &s_evn_12],
            );
            let s_odd = expr_pow4_ip(
                [51, 38, 25, 12, 0],
                [&s_odd_13a, &s_odd_13b, &s_odd_13c, &s_odd_13d, &s_odd_12],
            );

            let id = (s_1st_shift + s_2nd_rot + s_3rd_rot) - (s_evn + Expression::from(2) * s_odd);

            Constraints::with_selector(q_sigma_1, vec![("sigma_1", id)])
        });

        meta.create_gate("13-13-13-13-12 decomposition", |meta| {
            // See function `assign_sprdd_13_13_13_13_12` for a description of the following
            // layout.
            let p13a = meta.query_advice(advice_cols[0], Rotation(-1));
            let p13b = meta.query_advice(advice_cols[0], Rotation(0));
            let p13c = meta.query_advice(advice_cols[0], Rotation(1));
            let p13d = meta.query_advice(advice_cols[0], Rotation(2));
            let p12 = meta.query_advice(advice_cols[0], Rotation(3));
            let output = meta.query_advice(advice_cols[4], Rotation(-1));

            let id = expr_pow2_ip([51, 38, 25, 12, 0], [&p13a, &p13b, &p13c, &p13d, &p12]) - output;

            Constraints::with_selector(q_13_13_13_13_12, vec![("13-13-13-13-12 decomposition", id)])
        });

        meta.create_gate("13-12-5-6-13-13-2 decomposition", |meta| {
            // See function `prepare_A` for a description of the following layout.
            let p13a = meta.query_advice(advice_cols[0], Rotation(-1));
            let p12 = meta.query_advice(advice_cols[2], Rotation(-1));
            let p05 = meta.query_advice(advice_cols[0], Rotation(0));
            let p06 = meta.query_advice(advice_cols[2], Rotation(0));
            let p13b = meta.query_advice(advice_cols[0], Rotation(1));
            let p13c = meta.query_advice(advice_cols[2], Rotation(1));
            let p02 = meta.query_advice(advice_cols[0], Rotation(2));
            let s13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s12 = meta.query_advice(advice_cols[3], Rotation(-1));
            let s05 = meta.query_advice(advice_cols[1], Rotation(0));
            let s06 = meta.query_advice(advice_cols[3], Rotation(0));
            let s13b = meta.query_advice(advice_cols[1], Rotation(1));
            let s13c = meta.query_advice(advice_cols[3], Rotation(1));
            let s02 = meta.query_advice(advice_cols[1], Rotation(2));
            let plain = meta.query_advice(advice_cols[4], Rotation(-1));
            let sprdd = meta.query_advice(advice_cols[4], Rotation(0));

            let plain_id = expr_pow2_ip(
                [51, 39, 34, 28, 15, 2, 0],
                [&p13a, &p12, &p05, &p06, &p13b, &p13c, &p02],
            ) - plain;
            let sprdd_id = expr_pow4_ip(
                [51, 39, 34, 28, 15, 2, 0],
                [&s13a, &s12, &s05, &s06, &s13b, &s13c, &s02],
            ) - sprdd;

            Constraints::with_selector(
                q_13_12_5_6_13_13_2,
                vec![
                    ("13_12_5_6_13_13_2 decomposition plain", plain_id),
                    ("13_12_5_6_13_13_2 decomposition sprdd", sprdd_id),
                ],
            )
        });

        meta.create_gate("13-10-13-10-4-13-1 decomposition", |meta| {
            // See function `prepare_A` for a description of the following layout.
            let p13a = meta.query_advice(advice_cols[0], Rotation(-1));
            let p10a = meta.query_advice(advice_cols[2], Rotation(-1));
            let p13b = meta.query_advice(advice_cols[0], Rotation(0));
            let p10b = meta.query_advice(advice_cols[2], Rotation(0));
            let p04 = meta.query_advice(advice_cols[0], Rotation(1));
            let p13c = meta.query_advice(advice_cols[2], Rotation(1));
            let p01 = meta.query_advice(advice_cols[0], Rotation(2));
            let s13a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s10a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s13b = meta.query_advice(advice_cols[1], Rotation(0));
            let s10b = meta.query_advice(advice_cols[3], Rotation(0));
            let s04 = meta.query_advice(advice_cols[3], Rotation(1));
            let s13c = meta.query_advice(advice_cols[1], Rotation(1));
            let s01 = meta.query_advice(advice_cols[1], Rotation(2));
            let plain = meta.query_advice(advice_cols[4], Rotation(-1));
            let sprdd = meta.query_advice(advice_cols[4], Rotation(0));

            let plain_id = expr_pow2_ip(
                [51, 41, 28, 18, 14, 1, 0],
                [&p13a, &p10a, &p13b, &p10b, &p04, &p13c, &p01],
            ) - plain;
            let sprdd_id = expr_pow4_ip(
                [51, 41, 28, 18, 14, 1, 0],
                [&s13a, &s10a, &s13b, &s10b, &s04, &s13c, &s01],
            ) - sprdd;

            Constraints::with_selector(
                q_13_10_13_10_4_13_1,
                vec![
                    ("13_10_13_10_4_13_1 decomposition plain", plain_id),
                    ("13_10_13_10_4_13_1 decomposition sprdd", sprdd_id),
                ],
            )
        });

        meta.create_gate("3-3x13-3-11-1-1-5-1 decomposition", |meta| {
            // See function `prepare_message_word` for a description of the following
            // layout.
            let w03a = meta.query_advice(advice_cols[0], Rotation(-1));
            let w13a = meta.query_advice(advice_cols[2], Rotation(-1));
            let w13b = meta.query_advice(advice_cols[0], Rotation(0));
            let w13c = meta.query_advice(advice_cols[2], Rotation(0));
            let w03b = meta.query_advice(advice_cols[0], Rotation(1));
            let w11 = meta.query_advice(advice_cols[2], Rotation(1));
            let w01a = meta.query_advice(advice_cols[7], Rotation(-1));
            let w01b = meta.query_advice(advice_cols[7], Rotation(0));
            let w05 = meta.query_advice(advice_cols[0], Rotation(2));
            let w01c = meta.query_advice(advice_cols[7], Rotation(1));
            let plain = meta.query_advice(advice_cols[4], Rotation(-1));

            let plain_id = expr_pow2_ip(
                [61, 48, 35, 22, 19, 8, 7, 6, 1, 0],
                [
                    &w03a, &w13a, &w13b, &w13c, &w03b, &w11, &w01a, &w01b, &w05, &w01c,
                ],
            ) - plain;

            // 1-bit check for W.01a, W.01b and W.01c
            let w_01a_check = w01a.clone() * (w01a - Expression::from(1));
            let w_01b_check = w01b.clone() * (w01b - Expression::from(1));
            let w_01c_check = w01c.clone() * (w01c - Expression::from(1));

            Constraints::with_selector(
                q_3_3x13_3_11_1_1_5_1,
                vec![
                    ("12_1x3_7_3_4_3 decomposition ", plain_id),
                    ("W.1a 1-bit check", w_01a_check),
                    ("W.1b 1-bit check", w_01b_check),
                    ("W.1c 1-bit check", w_01c_check),
                ],
            )
        });

        meta.create_gate("add mod 2^64", |meta| {
            // See function `assign_add_mod_2_64` for a description of the following layout.
            let s0 = meta.query_advice(advice_cols[5], Rotation(-1));
            let s1 = meta.query_advice(advice_cols[6], Rotation(-1));
            let s2 = meta.query_advice(advice_cols[5], Rotation(0));
            let s3 = meta.query_advice(advice_cols[6], Rotation(0));
            let s4 = meta.query_advice(advice_cols[4], Rotation(1));
            let s5 = meta.query_advice(advice_cols[5], Rotation(1));
            let s6 = meta.query_advice(advice_cols[6], Rotation(1));

            let carry = meta.query_advice(advice_cols[2], Rotation(2));
            let result = meta.query_advice(advice_cols[4], Rotation(-1));

            let summands = [s0, s1, s2, s3, s4, s5, s6];
            let lhs = summands.into_iter().reduce(|acc, x| acc + x).unwrap();
            let rhs = result + carry * Expression::Constant(u128_to_fe(1u128 << 64));

            Constraints::with_selector(q_add_mod_2_64, vec![("add_mod_2_64", lhs - rhs)])
        });

        Sha512Config {
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
            q_13_13_13_13_12,
            q_13_12_5_6_13_13_2,
            q_13_10_13_10_4_13_1,
            q_3_3x13_3_11_1_1_5_1,
            q_add_mod_2_64,
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

impl<F: PrimeField> Sha512Chip<F> {
    /// Pads the input byte array to be a multiple of 128 bytes (1024 bits).
    fn pad(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<Vec<AssignedByte<F>>, Error> {
        let l = 8 * bytes.len();
        let k = 1024 - (l + 129) % 1024;

        let mut padded = bytes.to_vec();
        padded.push(self.native_gadget.assign_fixed(layouter, 128u8)?); // k is always 7 mod 8
        padded.extend(vec![self.native_gadget.assign_fixed(layouter, 0u8)?; k / 8]);
        for byte in u128::to_be_bytes(l as u128) {
            padded.push(self.native_gadget.assign_fixed(layouter, byte)?);
        }

        Ok(padded)
    }

    /// Given a byte array of exactly 128 bytes, this function converts it into
    /// a block of 16 `AssignedPlain` values, each (64 bits) value
    /// representing 8 bytes in big-endian.
    ///
    /// # Panics
    ///
    /// If it does not receive exactly 128 bytes.
    pub(super) fn block_from_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<[AssignedPlain<F, 64>; 16], Error> {
        assert_eq!(bytes.len(), 128);

        Ok(bytes
            .chunks(8)
            .map(|word_bytes| {
                self.native_gadget
                    .assigned_from_be_bytes(layouter, word_bytes)
                    .map(AssignedPlain)
            })
            .collect::<Result<Vec<_>, Error>>()?
            .try_into()
            .unwrap())
    }

    /// Computes Maj(A, B, C).
    fn maj(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_a: &AssignedSpreaded<F, 64>,
        sprdd_b: &AssignedSpreaded<F, 64>,
        sprdd_c: &AssignedSpreaded<F, 64>,
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        We need to compute:
            Maj(A, B, C) = (A ∧ B) ⊕ (A ∧ C) ⊕ (B ∧ C)

        Note that the "majority" function (bit-wise most commont value) between A, B, C
        is encoded in the odd bits of (~A + ~B + ~C). This is because, for every bit
        position i, iff at least two out of three are 1, the sum A_i + B_i + C_i will
        overflow, leaving a carry bit of 1 (the result of majority for that bit).

        Maj which can be encoded by

        1) applying the plain-spreaded lookup on 13-13-13-13-12 limbs of Evn and Odd:
             Evn: (Evn.13a, Evn.13b, Evn.13c, Evn.13d, Evn.12)
             Odd: (Odd.13a, Odd.13b, Odd.13c, Odd.13d, Odd.12)

        2) asserting the 13-13-13-13-12 decomposition identity for Odd:
              2^51 * Odd.13a + 2^38 * Odd.13b + 2^25 * Odd.13c + 2^12 * Odd.13d + Odd.12
            = Odd

        3) asserting the major identity regarding the spreaded values:
              (4^51 * ~Evn.13a + 4^38 * ~Evn.13b + 4^25 * ~Evn.13c + 4^12 * ~Evn.13d + ~Evn.12)
          2 * (4^51 * ~Odd.13a + 4^38 * ~Odd.13b + 4^25 * ~Odd.13c + 4^12 * ~Odd.13d + ~Odd.12)
             = ~A + ~B + ~C

        The output is Odd.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |   A5  |  A6   |
        |----|----------|-----------|----|----------|-----------|------|-------|-------|
        | 13 |  Odd.13a | ~Odd.13a  | 13 |  Evn.13a | ~Evn.13a  | Odd  |  ~A   |  ~B   |
        | 13 |  Odd.13b | ~Odd.13b  | 13 |  Evn.13b | ~Evn.13b  |      |  ~C   |       | <- q_maj
        | 13 |  Odd.13c | ~Odd.13c  | 13 |  Evn.13c | ~Evn.13c  |      |       |       |
        | 13 |  Odd.13d | ~Odd.13d  | 13 |  Evn.13d | ~Evn.13d  |      |       |       |
        | 12 |  Odd.12  | ~Odd.12   | 12 |  Evn.12  | ~Evn.12   |      |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Maj(A, B, C)",
            |mut region| {
                self.config().q_maj.enable(&mut region, 1)?;

                (sprdd_a.0).copy_advice(|| "~A", &mut region, adv_cols[5], 0)?;
                (sprdd_b.0).copy_advice(|| "~B", &mut region, adv_cols[6], 0)?;
                (sprdd_c.0).copy_advice(|| "~C", &mut region, adv_cols[5], 1)?;

                let val_of_sprdd_forms: Value<[u128; 3]> = Value::from_iter([
                    sprdd_a.0.value().copied().map(fe_to_u128),
                    sprdd_b.0.value().copied().map(fe_to_u128),
                    sprdd_c.0.value().copied().map(fe_to_u128),
                ])
                .map(|sprdd_forms: Vec<u128>| sprdd_forms.try_into().unwrap());

                self.assign_sprdd_13_13_13_13_12(
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
        sprdd_E: &AssignedSpreaded<F, 64>,
        sprdd_F: &AssignedSpreaded<F, 64>,
        sprdd_G: &AssignedSpreaded<F, 64>,
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        We need to compute:
            Ch(E, F, G) = (E ∧ F) ⊕ (¬E ∧ G)

        which can be achieved by

        1) applying the plain-spreaded lookup on 13-13-13-13-12 limbs of Evn and Odd,
           for both (~E + ~F) and (~(¬E) + ~G):
             Evn_EF: (Evn_EF.13a, Evn_EF.13b, Evn_EF.13c, Evn_EF.13d, Evn_EF.12)
             Odd_EF: (Odd_EF.13a, Odd_EF.13b, Odd_EF.13c, Odd_EF.13d, Odd_EF.12)

             Evn_nEG: (Evn_nEG.13a, Evn_nEG.13b, Evn_nEG.13c, Evn_nEG.13d, Evn_nEG.12)
             Odd_nEG: (Odd_nEG.13a, Odd_nEG.13b, Odd_nEG.13c, Odd_nEG.13d, Odd_nEG.12)

        2) asserting the 13-13-13-13-12 decomposition identity for Odd_EF and Odd_nEG:
              2^51 * Odd_EF.13a + 2^38 * Odd_EF.13b + 2^25 * Odd_EF.13c + 2^12 * Odd_EF.13d + Odd_EF.12
            = Odd_EF

              2^51 * Odd_nEG.13a + 2^38 * Odd_nEG.13b + 2^25 * Odd_nEG.13c + 2^12 * Odd_nEG.13d + Odd_nEG.12
            = Odd_nEG

        3) asserting the spreaded addition identity for (~E + ~F) and (~(¬E) + ~G):
              (4^51 * ~Evn_EF.13a + 4^38 * ~Evn_EF.13b + 4^25 * ~Evn_EF.13c + 4^12 * ~Evn_EF.13d + ~Evn_EF.12)
          2 * (4^51 * ~Odd_EF.13a + 4^38 * ~Odd_EF.13b + 4^25 * ~Odd_EF.13c + 4^12 * ~Odd_EF.13d + ~Odd_EF.12)
             = ~E + ~F

              (4^51 * ~Evn_nEG.13a + 4^38 * ~Evn_nEG.13b + 4^25 * ~Evn_nEG.13c + 4^12 * ~Evn_nEG.13d + ~Evn_nEG.12)
          2 * (4^51 * ~Odd_nEG.13a + 4^38 * ~Odd_nEG.13b + 4^25 * ~Odd_nEG.13c + 4^12 * ~Odd_nEG.13d + ~Odd_nEG.12)
             = ~(¬E) + ~G

        4) asserting the following two addition identities:
                     Ret = Odd_EF + Odd_nEG
            MASK_EVN_128 = ~E + ~(¬E)

        The output is Ret.

        We distribute these values in the PLONK table as follows.

        | T0 |      A0      |       A1      | T1 |       A2     |       A3      |     A4  |    A5   |      A6     |
        |----|--------------|---------------|----|--------------|---------------|---------|---------|-------------|
        | 13 |  Odd_EF.13a  |  ~Odd_EF.13a  | 13 |  Evn_EF.13a  |  ~Evn_EF.13a  | Odd_EF  |    ~E   |     ~F      |
        | 13 |  Odd_EF.13b  |  ~Odd_EF.13b  | 13 |  Evn_EF.13b  |  ~Evn_EF.13b  | Odd_EF  | Odd_nEG |     Ret     | <- q_ch
        | 13 |  Odd_EF.13c  |  ~Odd_EF.13c  | 13 |  Evn_EF.13c  |  ~Evn_EF.13c  |         |         |             |
        | 13 |  Odd_EF.13d  |  ~Odd_EF.13d  | 13 |  Evn_EF.13d  |  ~Evn_EF.13d  |         |         |             |
        | 12 |  Odd_EF.12   |  ~Odd_EF.12   | 12 |  Evn_EF.12   |  ~Evn_EF.12   |         |         |             |
        | 13 |  Odd_nEF.13a |  ~Odd_nEF.13a | 13 |  Evn_nEF.13a |  ~Evn_nEF.13a | Odd_nEG |  ~(¬E)  |     ~G      |
        | 13 |  Odd_nEF.13b |  ~Odd_nEF.13b | 13 |  Evn_nEF.13b |  ~Evn_nEF.13b |   ~E    |  ~(¬E)  |MASK_EVN_128 | <- q_ch
        | 13 |  Odd_nEF.13c |  ~Odd_nEF.13c | 13 |  Evn_nEF.13c |  ~Evn_nEF.13c |         |         |             |
        | 13 |  Odd_nEF.13d |  ~Odd_nEF.13d | 13 |  Evn_nEF.13d |  ~Evn_nEF.13d |         |         |             |
        | 12 |  Odd_nEF.12  |  ~Odd_nEF.12  | 12 |  Evn_nEF.12  |  ~Evn_nEF.12  |         |         |             |
        */

        let adv_cols = self.config().advice_cols;

        let sprdd_E_val = sprdd_E.0.value().copied().map(fe_to_u128);
        let sprdd_F_val = sprdd_F.0.value().copied().map(fe_to_u128);
        let sprdd_G_val = sprdd_G.0.value().copied().map(fe_to_u128);
        let sprdd_nE_val = sprdd_E_val.map(negate_spreaded);

        let EpF_val = sprdd_E_val + sprdd_F_val;
        let nEpG_val = sprdd_nE_val + sprdd_G_val;
        let sprdd_nE_val: Value<F> = sprdd_nE_val.map(u128_to_fe);

        let mask_evn_128: AssignedNative<F> =
            (self.native_gadget).assign_fixed(layouter, u128_to_fe(MASK_EVN_128))?;

        layouter.assign_region(
            || "Ch(E, F, G)",
            |mut region| {
                self.config().q_half_ch.enable(&mut region, 1)?;
                self.config().q_half_ch.enable(&mut region, 6)?;

                (sprdd_E.0).copy_advice(|| "~E", &mut region, adv_cols[5], 0)?;
                (sprdd_E.0).copy_advice(|| "~E", &mut region, adv_cols[4], 6)?;

                (sprdd_F.0).copy_advice(|| "~F", &mut region, adv_cols[6], 0)?;
                (sprdd_G.0).copy_advice(|| "~G", &mut region, adv_cols[6], 5)?;

                let sprdd_nE = region.assign_advice(|| "~(¬E)", adv_cols[5], 5, || sprdd_nE_val)?;
                sprdd_nE.copy_advice(|| "~(¬E)", &mut region, adv_cols[5], 6)?;

                mask_evn_128.copy_advice(|| "MASK_EVN_128", &mut region, adv_cols[6], 6)?;

                let odd_EF =
                    self.assign_sprdd_13_13_13_13_12(&mut region, EpF_val, Parity::Odd, 0)?;
                (odd_EF.0).copy_advice(|| "Odd_EF", &mut region, adv_cols[4], 1)?;

                let odd_nEG =
                    self.assign_sprdd_13_13_13_13_12(&mut region, nEpG_val, Parity::Odd, 5)?;
                (odd_nEG.0).copy_advice(|| "Odd_nEG", &mut region, adv_cols[5], 1)?;

                let ret_val = odd_EF.0.value().copied() + odd_nEG.0.value().copied();
                region
                    .assign_advice(|| "Ret", adv_cols[6], 1, || ret_val)
                    .map(AssignedPlain::<F, 64>)
            },
        )
    }

    /// Computes Σ₀(A).
    fn Sigma_0(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &LimbsOfA<F>,
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        Given
                    A:  ( A.13a || A.12 || A.05 || A.06 || A.13b || A.13c || A.02 )

        We need to compute:
            A >>> 28 :  ( A.13b || A.13c || A.02  || A.13a || A.12  || A.05  || A.06 )
          ⊕ A >>> 34 :  ( A.06  || A.13b || A.13c || A.02  || A.13a || A.12  || A.05 )
          ⊕ A >>> 39 :  ( A.05  || A.06  || A.13b || A.13c || A.02  || A.13a || A.12 )

        which can be achieved by

        1) applying the plain-spreaded lookup on 13-13-13-13-12 limbs of Evn and Odd:
             Evn: (Evn.13a, Evn.13b, Evn.13c, Evn.13d, Evn.12)
             Odd: (Odd.13a, Odd.13b, Odd.13c, Odd.13d, Odd.12)

        2) asserting the 13-13-13-13-12 decomposition identity for Evn:
              2^51 * Evn.13a + 2^38 * Evn.13b + 2^25 * Evn.13c + 2^12 * Evn.13d + Evn.12
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^51 * ~Evn.13a + 4^38 * ~Evn.13b + 4^25 * ~Evn.13c + 4^12 * ~Evn.13d + ~Evn.12) +
          2 * (4^51 * ~Odd.13a + 4^38 * ~Odd.13b + 4^25 * ~Odd.13c + 4^12 * ~Odd.13d + ~Odd.12)
             = 4^51 * ~A.13b + 4^38 * ~A.13c + 4^36 * ~A.02  + 4^23 * ~A.13a + 4^11 * ~A.12  + 4^6  * ~A.05  + ~A.06
             + 4^58 * ~A.06  + 4^45 * ~A.13b + 4^32 * ~A.13c + 4^30 * ~A.02  + 4^17 * ~A.13a + 4^5  * ~A.12  + ~A.05
             + 4^59 * ~A.05  + 4^53 * ~A.06  + 4^40 * ~A.13b + 4^27 * ~A.13c + 4^25 * ~A.02  + 4^12 * ~A.13a + ~A.12

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |   A6   |
        |----|----------|-----------|----|----------|-----------|------|----------|--------|
        | 13 |  Evn.13a | ~Evn.13a  | 13 |  Odd.13a | ~Odd.13a  | Evn  |  ~A.13a  | ~A.12  |
        | 13 |  Evn.13b | ~Evn.13b  | 13 |  Odd.13b | ~Odd.13b  |      |  ~A.05   | ~A.06  | <- q_Sigma_0
        | 13 |  Evn.13c | ~Evn.13c  | 13 |  Odd.13c | ~Odd.13c  |      |  ~A.13b  | ~A.13c |
        | 13 |  Evn.13d | ~Evn.13d  | 13 |  Odd.13d | ~Odd.13d  |      |  ~A.02   |        |
        | 12 |  Evn.12  | ~Evn.12   | 12 |  Odd.12  | ~Odd.12   |      |          |        |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₀(A)",
            |mut region| {
                self.config().q_Sigma_0.enable(&mut region, 1)?;

                // Copy and assign the input.
                (a.spreaded_limb_13a.0).copy_advice(|| "~A.13a", &mut region, adv_cols[5], 0)?;
                (a.spreaded_limb_12.0).copy_advice(|| "~A.12", &mut region, adv_cols[6], 0)?;
                (a.spreaded_limb_05.0).copy_advice(|| "~A.05", &mut region, adv_cols[5], 1)?;
                (a.spreaded_limb_06.0).copy_advice(|| "~A.06", &mut region, adv_cols[6], 1)?;
                (a.spreaded_limb_13b.0).copy_advice(|| "~A.13b", &mut region, adv_cols[5], 2)?;
                (a.spreaded_limb_13c.0).copy_advice(|| "~A.13c", &mut region, adv_cols[6], 2)?;
                (a.spreaded_limb_02.0).copy_advice(|| "~A.02", &mut region, adv_cols[5], 3)?;

                // Compute the spreaded Σ₀(A) off-circuit, assign the 13-13-13-13-12 limbs
                // of its even and odd bits into the circuit, enable the q_13_13_13_13_12
                // selector for the even part and q_lookup selector for the
                // related rows, return the assigned 64 even bits.
                let val_of_sprdd_limbs: Value<[u128; 7]> = Value::from_iter([
                    a.spreaded_limb_13a.0.value().copied().map(fe_to_u128),
                    a.spreaded_limb_12.0.value().copied().map(fe_to_u128),
                    a.spreaded_limb_05.0.value().copied().map(fe_to_u128),
                    a.spreaded_limb_06.0.value().copied().map(fe_to_u128),
                    a.spreaded_limb_13b.0.value().copied().map(fe_to_u128),
                    a.spreaded_limb_13c.0.value().copied().map(fe_to_u128),
                    a.spreaded_limb_02.0.value().copied().map(fe_to_u128),
                ])
                .map(|limbs: Vec<u128>| limbs.try_into().unwrap());

                self.assign_sprdd_13_13_13_13_12(
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
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        Given
                    E:  ( E.13a || E.10a || E.13b || E.10b || E.04 || E.13c || E.01 )

        We need to compute:
            E >>> 14 :  ( E.13c || E.01  || E.13a || E.10a || E.13b || E.10b || E.04  )
          ⊕ E >>> 18 :  ( E.04  || E.13c || E.01  || E.13a || E.10a || E.13b || E.10b )
          ⊕ E >>> 41 :  ( E.13b || E.10b || E.04  || E.13c || E.01  || E.13a || E.10a )

        which can be achieved by

        1) applying the plain-spreaded lookup on 13-13-13-13-12 limbs of Evn and Odd:
             Evn: (Evn.13a, Evn.13b, Evn.13c, Evn.13d, Evn.12)
             Odd: (Odd.13a, Odd.13b, Odd.13c, Odd.13d, Odd.12)

        2) asserting the 13-13-13-13-12 decomposition identity for Evn:
              2^51 * Evn.13a + 2^38 * Evn.13b + 2^25 * Evn.13c + 2^12 * Evn.13d + Evn.12
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^51 * ~Evn.13a + 4^38 * ~Evn.13b + 4^25 * ~Evn.13c + 4^12 * ~Evn.13d + ~Evn.12) +
          2 * (4^51 * ~Odd.13a + 4^38 * ~Odd.13b + 4^25 * ~Odd.13c + 4^12 * ~Odd.13d + ~Odd.12)
             = 4^51 * ~E.13c + 4^50 * ~E.01  + 4^37 * ~E.13a + 4^27 * ~E.10a + 4^14 * ~E.13b + 4^4  * ~E.10b  + ~E.04
             + 4^60 * ~E.04  + 4^47 * ~E.13c + 4^46 * ~E.01  + 4^33 * ~E.13a + 4^23 * ~E.10a + 4^10 * ~E.13b  + ~E.10b
             + 4^51 * ~E.13b + 4^41 * ~E.10b + 4^37 * ~E.04  + 4^24 * ~E.13c + 4^23 * ~E.01  + 4^10 * ~E.13a  + ~E.10a

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |   A6   |
        |----|----------|-----------|----|----------|-----------|------|----------|--------|
        | 13 |  Evn.13a | ~Evn.13a  | 13 |  Odd.13a | ~Odd.13a  | Evn  |  ~E.13a  | ~E.10a |
        | 13 |  Evn.13b | ~Evn.13b  | 13 |  Odd.13b | ~Odd.13b  |      |  ~E.13b  | ~E.10b | <- q_Sigma_1
        | 13 |  Evn.13c | ~Evn.13c  | 13 |  Odd.13c | ~Odd.13c  |      |  ~E.04   | ~E.13c |
        | 13 |  Evn.13d | ~Evn.13d  | 13 |  Odd.13d | ~Odd.13d  |      |  ~E.01   |        |
        | 12 |  Evn.12  | ~Evn.12   | 12 |  Odd.12  | ~Odd.12   |      |          |        |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₁(E)",
            |mut region| {
                self.config().q_Sigma_1.enable(&mut region, 1)?;

                // Copy and assign the input.
                (e.spreaded_limb_13a.0).copy_advice(|| "~E.13a", &mut region, adv_cols[5], 0)?;
                (e.spreaded_limb_10a.0).copy_advice(|| "~E.10a", &mut region, adv_cols[6], 0)?;
                (e.spreaded_limb_13b.0).copy_advice(|| "~E.13b", &mut region, adv_cols[5], 1)?;
                (e.spreaded_limb_10b.0).copy_advice(|| "~E.10b", &mut region, adv_cols[6], 1)?;
                (e.spreaded_limb_04.0).copy_advice(|| "~E.04", &mut region, adv_cols[5], 2)?;
                (e.spreaded_limb_13c.0).copy_advice(|| "~E.13c", &mut region, adv_cols[6], 2)?;
                (e.spreaded_limb_01.0).copy_advice(|| "~E.01", &mut region, adv_cols[5], 3)?;

                // Compute the spreaded Σ₁(E) off-circuit, assign the 13-13-13-13-12 limbs
                // of its even and odd bits into the circuit, enable the q_13_13_13_13_12
                // selector for the even part and q_lookup selector for the
                // related rows, return the assigned 64 even bits.
                let val_of_sprdd_limbs: Value<[u128; 7]> = Value::from_iter([
                    e.spreaded_limb_13a.0.value().copied().map(fe_to_u128),
                    e.spreaded_limb_10a.0.value().copied().map(fe_to_u128),
                    e.spreaded_limb_13b.0.value().copied().map(fe_to_u128),
                    e.spreaded_limb_10b.0.value().copied().map(fe_to_u128),
                    e.spreaded_limb_04.0.value().copied().map(fe_to_u128),
                    e.spreaded_limb_13c.0.value().copied().map(fe_to_u128),
                    e.spreaded_limb_01.0.value().copied().map(fe_to_u128),
                ])
                .map(|limbs: Vec<u128>| limbs.try_into().unwrap());

                self.assign_sprdd_13_13_13_13_12(
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
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        Given
                    W:  ( W.03a || W.13a || W.13b || W.13c || W.03b || W.11 || W.01a || W.01b || W.05 || W.01c )

        We need to compute:
            W  >>  7 :  ( W.03a || W.13a || W.13b || W.13c || W.03b || W.11  || W.01a )
          ⊕ W >>>  1 :  ( W.01c || W.03a || W.13a || W.13b || W.13c || W.03b || W.11  || W.01a || W.01b || W.05 )
          ⊕ W >>>  8 :  ( W.01a || W.01b || W.05  || W.01c || W.03a || W.13a || W.13b || W.13c || W.03b || W.11 )

        which can be achieved by

        1) applying the plain-spreaded lookup on 13-13-13-13-12 limbs of Evn and Odd:
             Evn: (Evn.13a, Evn.13b, Evn.13c, Evn.13d, Evn.12)
             Odd: (Odd.13a, Odd.13b, Odd.13c, Odd.13d, Odd.12)

        2) asserting the 13-13-13-13-12 decomposition identity for Evn:
              2^51 * Evn.13a + 2^38 * Evn.13b + 2^25 * Evn.13c + 2^12 * Evn.13d + Evn.12
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^51 * ~Evn.13a + 4^38 * ~Evn.13b + 4^25 * ~Evn.13c + 4^12 * ~Evn.13d + ~Evn.12) +
          2 * (4^51 * ~Odd.13a + 4^38 * ~Odd.13b + 4^25 * ~Odd.13c + 4^12 * ~Odd.13d + ~Odd.12)
             = 4^54 * ~W.03a + 4^41 * ~W.13a + 4^28 * ~W.13b + 4^15 * ~W.13c + 4^12 * ~W.03b + 4^1
             * ~W.11  + ~W.01a
             + 4^63 * ~W.01c + 4^60 * ~W.03a + 4^47 * ~W.13a + 4^34 * ~W.13b + 4^21 * ~W.13c + 4^18
             * ~W.03b + 4^7  * ~W.11 + 4^6  * ~W.01a + 4^5  * ~W.01b + ~W.05
             + 4^63 * ~W.05  + 4^62 * ~W.06  + 4^57 * ~W.13b + 4^56 * ~W.13c + 4^53 * ~W.02  + 4^40
             * ~W.13a + 4^27 * ~W.12 + 4^14 * ~W.12  + 4^11 * ~W.03b + ~W.11

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |   A6   |
        |----|----------|-----------|----|----------|-----------|------|----------|--------|
        | 13 |  Evn.13a | ~Evn.13a  | 13 |  Odd.13a | ~Odd.13a  | Evn  |  ~W.03a  | ~W.13a |
        | 13 |  Evn.13b | ~Evn.13b  | 13 |  Odd.13b | ~Odd.13b  |      |  ~W.13b  | ~W.13c | <- q_sigma_0
        | 13 |  Evn.13c | ~Evn.13c  | 13 |  Odd.13c | ~Odd.13c  |      |  ~W.03b  | ~W.11  |
        | 13 |  Evn.13d | ~Evn.13d  | 13 |  Odd.13d | ~Odd.13d  |      |  ~W.01a  | ~W.01b |
        | 12 |  Evn.12  | ~Evn.12   | 12 |  Odd.12  | ~Odd.12   |      |  ~W.05   | ~W.01c |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "σ₀(W)",
            |mut region| {
                self.config().q_sigma_0.enable(&mut region, 1)?;

                // Copy and assign the input.
                (w.spreaded_w_03a.0).copy_advice(|| "~W.03a", &mut region, adv_cols[5], 0)?;
                (w.spreaded_w_13a.0).copy_advice(|| "~W.13a", &mut region, adv_cols[6], 0)?;
                (w.spreaded_w_13b.0).copy_advice(|| "~W.13b", &mut region, adv_cols[5], 1)?;
                (w.spreaded_w_13c.0).copy_advice(|| "~W.13c", &mut region, adv_cols[6], 1)?;
                (w.spreaded_w_03b.0).copy_advice(|| "~W.03b", &mut region, adv_cols[5], 2)?;
                (w.spreaded_w_11.0).copy_advice(|| "~W.11", &mut region, adv_cols[6], 2)?;
                (w.spreaded_w_01a.0).copy_advice(|| "~W.01a", &mut region, adv_cols[5], 3)?;
                (w.spreaded_w_01b.0).copy_advice(|| "~W.01b", &mut region, adv_cols[6], 3)?;
                (w.spreaded_w_05.0).copy_advice(|| "~W.05", &mut region, adv_cols[5], 4)?;
                (w.spreaded_w_01c.0).copy_advice(|| "~W.01c", &mut region, adv_cols[6], 4)?;

                // Compute the spreaded σ₀(W) off-circuit, assign the 13-13-13-13-12 limbs
                // of its even and odd bits into the circuit, enable the q_13_13_13_13_12
                // selector for the even part and q_lookup selector for the
                // related rows, return the assigned 64 even bits.
                let val_of_sprdd_limbs: Value<[u128; 10]> = Value::from_iter([
                    w.spreaded_w_03a.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_13a.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_13b.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_13c.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_03b.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_11.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_01a.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_01b.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_05.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_01c.0.value().copied().map(fe_to_u128),
                ])
                .map(|limbs: Vec<u128>| limbs.try_into().unwrap());

                self.assign_sprdd_13_13_13_13_12(
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
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        Given
                    W:  ( W.03a || W.13a || W.13b || W.13c || W.03b || W.11 || W.01a || W.01b || W.05 || W.01c )

        We need to compute:
            W  >>  6 :  ( W.03a || W.13a || W.13b || W.13c || W.03b || W.11  || W.01a || W.01b )
          ⊕ W >>> 19 :  ( W.11  || W.01a || W.01b || W.05  || W.01c || W.03a || W.13a || W.13b || W.13c || W.03b )
          ⊕ W >>> 61 :  ( W.13a || W.13b || W.13c || W.03b || W.11  || W.01a || W.01b || W.05  || W.01c || W.03a )

        which can be achieved by

        1) applying the plain-spreaded lookup on 13-13-13-13-12 limbs of Evn and Odd:
             Evn: (Evn.13a, Evn.13b, Evn.13c, Evn.13d, Evn.12)
             Odd: (Odd.13a, Odd.13b, Odd.13c, Odd.13d, Odd.12)

        2) asserting the 13-13-13-13-12 decomposition identity for Evn:
              2^51 * Evn.13a + 2^38 * Evn.13b + 2^25 * Evn.13c + 2^12 * Evn.13d + Evn.12
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^51 * ~Evn.13a + 4^38 * ~Evn.13b + 4^25 * ~Evn.13c + 4^12 * ~Evn.13d + ~Evn.12) +
          2 * (4^51 * ~Odd.13a + 4^38 * ~Odd.13b + 4^25 * ~Odd.13c + 4^12 * ~Odd.13d + ~Odd.12)
             = 4^55 * ~W.03a + 4^42 * ~W.13a + 4^29 * ~W.13b + 4^16 * ~W.13c + 4^13 * ~W.03b + 4^2
             * ~W.11  + 4^1  * ~W.01a + ~W.01b
             + 4^53 * ~W.11  + 4^52 * ~W.01a + 4^51 * ~W.01b + 4^46 * ~W.05  + 4^45 * ~W.01c + 4^42
             * ~W.03a + 4^29 * ~W.13a + 4^16 * ~W.13b + 4^3 * ~W.13c + ~W.03b
             + 4^51 * ~W.13a + 4^38 * ~W.13b + 4^25 * ~W.13c + 4^22 * ~W.03b + 4^11 * ~W.11  + 4^10
             * ~W.01a + 4^9 * ~W.01b  + 4^4  * ~W.05  + 4^3 * ~W.01c + ~W.03a

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |   A6   |
        |----|----------|-----------|----|----------|-----------|------|----------|--------|
        | 13 |  Evn.13a | ~Evn.13a  | 13 |  Odd.13a | ~Odd.13a  | Evn  |  ~W.03a  | ~W.13a |
        | 13 |  Evn.13b | ~Evn.13b  | 13 |  Odd.13b | ~Odd.13b  |      |  ~W.13b  | ~W.13c | <- q_sigma_1
        | 13 |  Evn.13c | ~Evn.13c  | 13 |  Odd.13c | ~Odd.13c  |      |  ~W.03b  | ~W.11  |
        | 13 |  Evn.13d | ~Evn.13d  | 13 |  Odd.13d | ~Odd.13d  |      |  ~W.01a  | ~W.01b |
        | 12 |  Evn.12  | ~Evn.12   | 12 |  Odd.12  | ~Odd.12   |      |  ~W.05   | ~W.01c |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "σ₁(W)",
            |mut region| {
                self.config().q_sigma_1.enable(&mut region, 1)?;

                // Copy and assign the input.
                (w.spreaded_w_03a.0).copy_advice(|| "~W.03a", &mut region, adv_cols[5], 0)?;
                (w.spreaded_w_13a.0).copy_advice(|| "~W.13a", &mut region, adv_cols[6], 0)?;
                (w.spreaded_w_13b.0).copy_advice(|| "~W.13b", &mut region, adv_cols[5], 1)?;
                (w.spreaded_w_13c.0).copy_advice(|| "~W.13c", &mut region, adv_cols[6], 1)?;
                (w.spreaded_w_03b.0).copy_advice(|| "~W.03b", &mut region, adv_cols[5], 2)?;
                (w.spreaded_w_11.0).copy_advice(|| "~W.11", &mut region, adv_cols[6], 2)?;
                (w.spreaded_w_01a.0).copy_advice(|| "~W.01a", &mut region, adv_cols[5], 3)?;
                (w.spreaded_w_01b.0).copy_advice(|| "~W.01b", &mut region, adv_cols[6], 3)?;
                (w.spreaded_w_05.0).copy_advice(|| "~W.05", &mut region, adv_cols[5], 4)?;
                (w.spreaded_w_01c.0).copy_advice(|| "~W.01c", &mut region, adv_cols[6], 4)?;

                // Compute the spreaded σ₁(W) off-circuit, assign the 13-13-13-13-12 limbs
                // of its even and odd bits into the circuit, enable the q_13_13_13_13_12
                // selector for the even part and q_lookup selector for the
                // related rows, return the assigned 64 even bits.
                let val_of_sprdd_limbs: Value<[u128; 10]> = Value::from_iter([
                    w.spreaded_w_03a.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_13a.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_13b.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_13c.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_03b.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_11.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_01a.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_01b.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_05.0.value().copied().map(fe_to_u128),
                    w.spreaded_w_01c.0.value().copied().map(fe_to_u128),
                ])
                .map(|limbs: Vec<u128>| limbs.try_into().unwrap());

                self.assign_sprdd_13_13_13_13_12(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_sigma_1),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Given a u128, representing a spreaded value, this function fills a
    /// lookup table with the limbs of its even and odd parts (or vice versa)
    /// and returns the former or the latter, depending on the desired value
    /// `even_or_odd`.
    ///
    /// If `even_or_odd` = `Parity::Evn`:
    ///
    ///  | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |
    ///  |----|---------|----------|----|---------|----------|-----|
    ///  | 13 | Evn.13a | ~Evn.13a | 13 | Odd.13a | ~Odd.13a | Evn |
    ///  | 13 | Evn.13b | ~Evn.13b | 13 | Odd.13b | ~Odd.13b |     | <- q_13_13_13_13_12
    ///  | 13 | Evn.13c | ~Evn.13c | 13 | Odd.13c | ~Odd.13c |     |
    ///  | 13 | Evn.13d | ~Evn.13d | 13 | Odd.13d | ~Odd.13d |     |
    ///  | 12 | Evn.12  | ~Evn.12  | 12 | Odd.12  | ~Odd.12  |     |
    ///
    /// and returns `Evn`.
    ///
    /// If `even_or_odd` = `Parity::Odd`:
    ///
    ///  | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |
    ///  |----|---------|----------|----|---------|----------|-----|
    ///  | 13 | Odd.13a | ~Odd.13a | 13 | Evn.13a | ~Evn.13a | Odd |
    ///  | 13 | Odd.13b | ~Odd.13b | 13 | Evn.13b | ~Evn.13b |     | <- q_13_13_13_13_12
    ///  | 13 | Odd.13c | ~Odd.13c | 13 | Evn.13c | ~Evn.13c |     |
    ///  | 13 | Odd.13d | ~Odd.13d | 13 | Evn.13d | ~Evn.13d |     |
    ///  | 12 | Odd.12  | ~Odd.12  | 12 | Evn.12  | ~Evn.12  |     |
    ///
    /// and returns `Odd`.
    ///
    /// This function guarantees that the returned value is consistent with
    /// the values in the filled lookup table.
    fn assign_sprdd_13_13_13_13_12(
        &self,
        region: &mut Region<'_, F>,
        value: Value<u128>,
        even_or_odd: Parity,
        offset: usize,
    ) -> Result<AssignedPlain<F, 64>, Error> {
        self.config().q_13_13_13_13_12.enable(region, offset + 1)?;

        let (evn_val, odd_val) = value.map(get_even_and_odd_bits).unzip();

        let [evn0_13, evn1_13, evn2_13, evn3_13, evn4_12] = evn_val
            .map(|v| u64_in_be_limbs(v, [13, 13, 13, 13, 12]))
            .transpose_array();

        let [odd0_13, odd1_13, odd2_13, odd3_13, odd4_12] = odd_val
            .map(|v| u64_in_be_limbs(v, [13, 13, 13, 13, 12]))
            .transpose_array();

        let idx = match even_or_odd {
            Parity::Evn => 0,
            Parity::Odd => 1,
        };

        self.assign_plain_and_spreaded::<13>(region, evn0_13, offset, idx)?;
        self.assign_plain_and_spreaded::<13>(region, evn1_13, offset + 1, idx)?;
        self.assign_plain_and_spreaded::<13>(region, evn2_13, offset + 2, idx)?;
        self.assign_plain_and_spreaded::<13>(region, evn3_13, offset + 3, idx)?;
        self.assign_plain_and_spreaded::<12>(region, evn4_12, offset + 4, idx)?;

        self.assign_plain_and_spreaded::<13>(region, odd0_13, offset, 1 - idx)?;
        self.assign_plain_and_spreaded::<13>(region, odd1_13, offset + 1, 1 - idx)?;
        self.assign_plain_and_spreaded::<13>(region, odd2_13, offset + 2, 1 - idx)?;
        self.assign_plain_and_spreaded::<13>(region, odd3_13, offset + 3, 1 - idx)?;
        self.assign_plain_and_spreaded::<12>(region, odd4_12, offset + 4, 1 - idx)?;

        let out_col = self.config().advice_cols[4];
        match even_or_odd {
            Parity::Evn => {
                region.assign_advice(|| "Evn", out_col, offset, || evn_val.map(u64_to_fe))
            }
            Parity::Odd => {
                region.assign_advice(|| "Odd", out_col, offset, || odd_val.map(u64_to_fe))
            }
        }
        .map(AssignedPlain)
    }

    /// Given a slice of at most 7 `AssignedPlain` values, it adds them
    /// modulo 2^64 and decomposes the result (named A) into (big-endian)
    /// limbs of bit sizes 13, 12, 5, 6, 13, 13 and 2.
    ///
    /// This function returns the plain and spreaded forms, as well as
    /// the spreaded limbs of A.
    fn prepare_A(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 64>],
    ) -> Result<LimbsOfA<F>, Error> {
        /*
        Given assigned plain inputs S0, ..., S6 (if fewer inputs are given
        they will be completed up to length 7, padding with fixed zeros),
        let A be their sum modulo 2^64.

        We use the following table distribution.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |   A4   |  A5  |  A6  |
        |----|----------|-----------|----|----------|-----------|--------|------|------|
        | 13 |   A.13a  |  ~A.13a   | 12 |   A.12   |   ~A.12   |   A    |  S0  |  S1  |
        | 05 |   A.05   |  ~A.05    | 06 |   A.06   |   ~A.06   |   ~A   |  S2  |  S3  | <- q_13_12_5_6_13_13_2
        | 13 |   A.13b  |  ~A.13b   | 13 |   A.13c  |   ~A.13c  |   S4   |  S5  |  S6  |
        | 02 |   A.02   |  ~A.02    | 03 |   carry  |   ~carry  |        |      |      |

        Apart from the lookups, the following identities are checked via a
        custom gate with selector q_13_12_5_6_13_13_2:

            A = 2^51 *  A.13a + 2^39 *  A.12  + 2^34 *  A.05 + 2^28 * A.06
              + 2^15 *  A.13b + 2^2  *  A.13c + A.02
           ~A = 4^51 * ~A.13a + 4^39 * ~A.12  + 4^34 * ~A.05 + 4^28 * ~A.06
              + 4^15 * ~A.13b + 4^2  * ~A.13c + ~A.02

        and the following is checked with a custom gate with selector
        q_add_mod_2_32:

            S0 + S1 + S2 + S3 + S4 + S5 + S6 = A + carry * 2^64

        Note that A is implicitly being range-checked in [0, 2^64) via
        the lookup, and the carry is range-checked in [0, 8). This makes
        the gate complete and sound (the range on the carry does not need
        to be tight as long as it prevents overflows in the native field).
        */

        let zero = AssignedPlain::<F, 64>::fixed(layouter, &self.native_gadget, 0)?;

        layouter.assign_region(
            || "decompose A in 13-12-5-6-13-13-2 limbs",
            |mut region| {
                self.config().q_13_12_5_6_13_13_2.enable(&mut region, 1)?;

                let a_plain = self.assign_add_mod_2_64(&mut region, summands, &zero)?;
                let a_sprdd_val = (a_plain.0.value().copied())
                    .map(fe_to_u64)
                    .map(spread)
                    .map(u128_to_fe);
                let a_sprdd = region
                    .assign_advice(|| "~A", self.config().advice_cols[4], 1, || a_sprdd_val)
                    .map(AssignedSpreaded)?;

                let [val_13a, val_12, val_05, val_06, val_13b, val_13c, val_02] =
                    (a_plain.0.value().copied())
                        .map(|a| u64_in_be_limbs(fe_to_u64(a), [13, 12, 5, 6, 13, 13, 2]))
                        .transpose_array();

                let limb_13a = self.assign_plain_and_spreaded(&mut region, val_13a, 0, 0)?;
                let limb_12 = self.assign_plain_and_spreaded(&mut region, val_12, 0, 1)?;
                let limb_05 = self.assign_plain_and_spreaded(&mut region, val_05, 1, 0)?;
                let limb_06 = self.assign_plain_and_spreaded(&mut region, val_06, 1, 1)?;
                let limb_13b = self.assign_plain_and_spreaded(&mut region, val_13b, 2, 0)?;
                let limb_13c = self.assign_plain_and_spreaded(&mut region, val_13c, 2, 1)?;
                let limb_02 = self.assign_plain_and_spreaded(&mut region, val_02, 3, 0)?;

                Ok(LimbsOfA {
                    combined: AssignedPlainSpreaded {
                        plain: a_plain,
                        spreaded: a_sprdd,
                    },
                    spreaded_limb_13a: limb_13a.spreaded,
                    spreaded_limb_12: limb_12.spreaded,
                    spreaded_limb_05: limb_05.spreaded,
                    spreaded_limb_06: limb_06.spreaded,
                    spreaded_limb_13b: limb_13b.spreaded,
                    spreaded_limb_13c: limb_13c.spreaded,
                    spreaded_limb_02: limb_02.spreaded,
                })
            },
        )
    }

    /// Given a slice of at most 7 `AssignedPlain` values, it adds them
    /// modulo 2^64 and decomposes the result (named E) into (big-endian)
    /// limbs of bit sizes 13, 10, 13, 10, 4, 13 and 1.
    ///
    /// This function returns the plain and spreaded forms, as well as
    /// the spreaded limbs of E.
    fn prepare_E(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 64>],
    ) -> Result<LimbsOfE<F>, Error> {
        /*
        Given assigned plain inputs S0, ..., S6 (if fewer inputs are given
        they will be completed up to length 7, padding with fixed zeros),
        let E be their sum modulo 2^64.

        We use the following table distribution.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |   A4   |  A5  |  A6  |
        |----|----------|-----------|----|----------|-----------|--------|------|------|
        | 13 |   E.13a  |  ~E.13a   | 10 |   E.10a  |   ~E.10a  |   E    |  S0  |  S1  |
        | 13 |   E.13b  |  ~E.13b   | 10 |   E.10b  |   ~E.10b  |   ~E   |  S2  |  S3  | <- q_13_10_13_10_4_13_1
        | 04 |   E.04   |  ~E.04    | 13 |   E.13c  |   ~E.13c  |   S4   |  S5  |  S6  |
        | 01 |   E.01   |  ~E.01    | 03 |   carry  |   ~carry  |        |      |      |

        Apart from the lookups, the following identities are checked via a
        custom gate with selector q_13_10_13_10_4_13_1:

            E = 2^51 *  E.13a + 2^41 *  E.10a + 2^28  *  E.13b + 2^18 * E.10b
              + 2^14 *  E.04  + 2^1  *  E.13c + E.01
           ~E = 4^51 * ~E.13a + 4^41 * ~E.10a + 4^28  * ~E.13b + 4^18 * ~E.10b
              + 4^14 * ~E.04  + 4^1  * ~E.13c + ~E.01

        and the following is checked with a custom gate with selector
        q_add_mod_2_64:

            S0 + S1 + S2 + S3 + S4 + S5 + S6 = E + carry * 2^64

        Note that E is implicitly being range-checked in [0, 2^64) via
        the lookup, and the carry is range-checked in [0, 8). This makes
        the gate complete and sound (the range on the carry does not need
        to be tight as long as it prevents overflows in the native field).
        */

        let zero = AssignedPlain::<F, 64>::fixed(layouter, &self.native_gadget, 0)?;

        layouter.assign_region(
            || "decompose E in 13-10-13-10-4-13-1 limbs",
            |mut region| {
                self.config().q_13_10_13_10_4_13_1.enable(&mut region, 1)?;

                let e_plain = self.assign_add_mod_2_64(&mut region, summands, &zero)?;
                let e_sprdd_val = (e_plain.0.value().copied())
                    .map(fe_to_u64)
                    .map(spread)
                    .map(u128_to_fe);
                let e_sprdd = region
                    .assign_advice(|| "~E", self.config().advice_cols[4], 1, || e_sprdd_val)
                    .map(AssignedSpreaded)?;

                let [val_13a, val_10a, val_13b, val_10b, val_04, val_13c, val_01] =
                    (e_plain.0.value().copied())
                        .map(|e| u64_in_be_limbs(fe_to_u64(e), [13, 10, 13, 10, 4, 13, 1]))
                        .transpose_array();

                let limb_13a = self.assign_plain_and_spreaded(&mut region, val_13a, 0, 0)?;
                let limb_10a = self.assign_plain_and_spreaded(&mut region, val_10a, 0, 1)?;
                let limb_13b = self.assign_plain_and_spreaded(&mut region, val_13b, 1, 0)?;
                let limb_10b = self.assign_plain_and_spreaded(&mut region, val_10b, 1, 1)?;
                let limb_04 = self.assign_plain_and_spreaded(&mut region, val_04, 2, 0)?;
                let limb_13c = self.assign_plain_and_spreaded(&mut region, val_13c, 2, 1)?;
                let limb_01 = self.assign_plain_and_spreaded(&mut region, val_01, 3, 0)?;

                Ok(LimbsOfE {
                    combined: AssignedPlainSpreaded {
                        plain: e_plain,
                        spreaded: e_sprdd,
                    },
                    spreaded_limb_13a: limb_13a.spreaded,
                    spreaded_limb_10a: limb_10a.spreaded,
                    spreaded_limb_13b: limb_13b.spreaded,
                    spreaded_limb_10b: limb_10b.spreaded,
                    spreaded_limb_04: limb_04.spreaded,
                    spreaded_limb_13c: limb_13c.spreaded,
                    spreaded_limb_01: limb_01.spreaded,
                })
            },
        )
    }

    /// Given a slice of at most 7 `AssignedPlain` values, this function adds
    /// them modulo 2^64 and decomposes the result (named W_i) into (big-endian)
    /// limbs of bit sizes 3, 13, 13, 13, 3, 11, 1, 1, 5 and 1.
    fn prepare_message_word(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 64>],
    ) -> Result<AssignedMessageWord<F>, Error> {
        /*
        Given assigned plain inputs S0, ..., S6 (if fewer inputs are given
        they will be completed up to length 7, padding with fixed zeros),
        and computes W.i as their sum modulo 2^64.

        We use the following table distribution.

        | T0 |    A0    |     A1    | T1 |    A2    |     A3    |    A4   |  A5  |  A6  |  A.7  |
        |----|----------|-----------|----|----------|-----------|---------|------|------|-------|
        | 03 |   W.03a  |  ~W.03a   | 13 |   W.13a  |  ~W.13a   |  W.i    |  S0  |  S1  | W.01a |
        | 13 |   W.13b  |  ~W.13b   | 13 |   W.13c  |  ~W.13c   |         |  S2  |  S3  | W.01b | <- q_3_3x13_3_11_1_1_5_1
        | 03 |   W.03b  |  ~W.03b   | 11 |   W.11   |  ~W.11    |   S4    |  S5  |  S6  | W.01c |
        | 05 |   W.05   |  ~W.05    | 03 |   carry  |  ~carry   |         |      |      |       |

        Apart from the lookups, the following identities are checked via a
        custom gate with selector q_3_3x13_3_11_1_1_5_1:

          W.i =   2^61 * W.03a + 2^48 * W.13a + 2^35 * W.13b + 2^22 * W.13c
                + 2^19 * W.03b + 2^8  * W.11  + 2^7  * W.01a + 2^6  * W.01b + 2^1 * W.05 + W.01c

          W.01a * (W.01a - 1) = 0
          W.01b * (W.01b - 1) = 0
          W.01c * (W.01c - 1) = 0

        and the following is checked with a custom gate with selector
        q_add_mod_2_32:

          S0 + S1 + S2 + S3 + S4 + S5 + S6 = W.i + carry * 2^64

        Note that W.i is implicitly being range-checked in [0, 2^64) via
        the lookup, and the carry is range-checked in [0, 8). This makes
        the gate complete and sound (the range on the carry does not need
        to be tight as long as it prevents overflows in the native field).
        */

        let zero = AssignedPlain::<F, 64>::fixed(layouter, &self.native_gadget, 0)?;

        layouter.assign_region(
            || "prepare message word",
            |mut region| {
                self.config().q_3_3x13_3_11_1_1_5_1.enable(&mut region, 1)?;

                let w_i_plain = self.assign_add_mod_2_64(&mut region, summands, &zero)?;

                let [val_03a, val_13a, val_13b, val_13c, val_03b, val_11, val_01a, val_01b, val_05, val_01c] =
                    (w_i_plain.0.value().copied())
                        .map(|w| u64_in_be_limbs(fe_to_u64(w), [3, 13, 13, 13, 3, 11, 1, 1, 5, 1]))
                        .transpose_array();
                let limb_03a = self.assign_plain_and_spreaded(&mut region, val_03a, 0, 0)?;
                let limb_13a = self.assign_plain_and_spreaded(&mut region, val_13a, 0, 1)?;
                let limb_13b = self.assign_plain_and_spreaded(&mut region, val_13b, 1, 0)?;
                let limb_13c = self.assign_plain_and_spreaded(&mut region, val_13c, 1, 1)?;
                let limb_03b = self.assign_plain_and_spreaded(&mut region, val_03b, 2, 0)?;
                let limb_11 = self.assign_plain_and_spreaded(&mut region, val_11, 2, 1)?;
                let limb_05 = self.assign_plain_and_spreaded(&mut region, val_05, 3, 0)?;

                // The spreaded forms of 1-bit values W.01a, W.01b and W.01c equal themselves.
                let col = self.config().advice_cols[7];
                let limb_01a = region.assign_advice(|| "W.01a", col, 0, || val_01a.map(u64_to_fe))?;
                let limb_01b = region.assign_advice(|| "W.01b", col, 1, || val_01b.map(u64_to_fe))?;
                let limb_01c = region.assign_advice(|| "W.01c", col, 2, || val_01c.map(u64_to_fe))?;

                Ok(AssignedMessageWord {
                    combined_plain: w_i_plain,
                    spreaded_w_03a: limb_03a.spreaded,
                    spreaded_w_13a: limb_13a.spreaded,
                    spreaded_w_13b: limb_13b.spreaded,
                    spreaded_w_13c: limb_13c.spreaded,
                    spreaded_w_03b: limb_03b.spreaded,
                    spreaded_w_11: limb_11.spreaded,
                    spreaded_w_01a: AssignedSpreaded(limb_01a),
                    spreaded_w_01b: AssignedSpreaded(limb_01b),
                    spreaded_w_05: limb_05.spreaded,
                    spreaded_w_01c: AssignedSpreaded(limb_01c),
                })
            },
        )
    }

    /// Given a plain u64 value, supposedly in the range [0, 2^L), assigns it
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
    /// # Unsatisfiable
    ///
    /// If the given value is not in the range [0, 2^L), the circuit will become
    /// unsatisfiable.
    fn assign_plain_and_spreaded<const L: usize>(
        &self,
        region: &mut Region<'_, F>,
        plain_val: Value<u64>,
        offset: usize,
        lookup_idx: usize,
    ) -> Result<AssignedPlainSpreaded<F, L>, Error> {
        self.config().q_lookup.enable(region, offset)?;

        let nbits_col = self.config().fixed_cols[lookup_idx]; // 0 or 1
        let plain_col = self.config().advice_cols[2 * lookup_idx]; // 0 or 2
        let sprdd_col = self.config().advice_cols[2 * lookup_idx + 1]; // 1 or 3

        let nbits_val = Value::known(F::from(L as u64));
        let sprdd_val = plain_val.map(spread).map(u128_to_fe);
        let plain_val = plain_val.map(u64_to_fe);

        region.assign_fixed(|| "nbits", nbits_col, offset, || nbits_val)?;
        let plain = region.assign_advice(|| "plain", plain_col, offset, || plain_val)?;
        let spreaded = region.assign_advice(|| "sprdd", sprdd_col, offset, || sprdd_val)?;

        Ok(AssignedPlainSpreaded {
            plain: AssignedPlain(plain),
            spreaded: AssignedSpreaded(spreaded),
        })
    }

    /// Given a slice of at most 7 `AssignedPlain` values, this function adds
    /// them modulo 2^64.
    ///
    /// The `zero` argument is supposed to contain a fixed assigned plain
    /// containing value 0, this is not enforced in this function, it is the
    /// responsibility of the caller to do so.
    ///
    /// # Panics
    ///
    /// If the more than 7 summands are provided.
    fn assign_add_mod_2_64(
        &self,
        region: &mut Region<'_, F>,
        summands: &[AssignedPlain<F, 64>],
        zero: &AssignedPlain<F, 64>,
    ) -> Result<AssignedPlain<F, 64>, Error> {
        /*
        We distribute values in the PLONK table as follows.

        | T1 |   A2  |   A3   |     A4    | A5 | A6 |
        |----|-------|--------|-----------|----|----|
        |    |       |        | sum_plain | S0 | S1 |
        |    |       |        |           | S2 | S3 | <- q_add_mod_2_64
        |    |       |        |     S4    | S5 | S6 |
        |  3 | carry | ~carry |           |    |    |

        We enforce S0 + S1 + S2 + S3 + S4 + S5 + S6 = sum_plain + carry * 2^64.
        */

        assert!(summands.len() <= 7);

        self.config().q_add_mod_2_64.enable(region, 1)?;
        let adv_cols = self.config().advice_cols;

        let mut summands = summands.to_vec();
        summands.resize(7, zero.clone());

        let (carry_val, sum_val): (Value<u64>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u128).sum())
                .map(|s: u128| s.div_rem(&(1 << 64)))
                .map(|(carry, r)| (carry as u64, u128_to_fe(r)))
                .unzip();

        summands[0].0.copy_advice(|| "S0", region, adv_cols[5], 0)?;
        summands[1].0.copy_advice(|| "S1", region, adv_cols[6], 0)?;
        summands[2].0.copy_advice(|| "S2", region, adv_cols[5], 1)?;
        summands[3].0.copy_advice(|| "S3", region, adv_cols[6], 1)?;
        summands[4].0.copy_advice(|| "S4", region, adv_cols[4], 2)?;
        summands[5].0.copy_advice(|| "S5", region, adv_cols[5], 2)?;
        summands[6].0.copy_advice(|| "S6", region, adv_cols[6], 2)?;
        let _carry: AssignedPlainSpreaded<F, 3> =
            self.assign_plain_and_spreaded(region, carry_val, 3, 1)?;
        region
            .assign_advice(|| "sum", adv_cols[4], 0, || sum_val)
            .map(AssignedPlain)
    }
}
