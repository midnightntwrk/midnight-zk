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

// $\Sigma_{0}(A)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |   A6   |
// |----|----------|-----------|----|----------|-----------|------|----------|--------|
// | 13 |  Evn0.13 | ~Evn0.13  | 13 |  Odd0.13 | ~Odd0.13  | Evn  |  ~A.13a  | ~A.12  |
// | 13 |  Evn1.13 | ~Evn1.13  | 13 |  Odd1.13 | ~Odd1.13  |      |  ~A.05   | ~A.06  |
// | 13 |  Evn2.13 | ~Evn2.13  | 13 |  Odd2.13 | ~Odd2.13  |      |  ~A.13b  | ~A.13c |
// | 13 |  Evn3.13 | ~Evn3.13  | 13 |  Odd3.13 | ~Odd3.13  |      |  ~A.02   |        |
// | 12 |  Evn4.12 | ~Evn4.12  | 12 |  Odd4.12 | ~Odd4.12  |      |          |        |

//  $Maj(A, B, C)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |   A5  |  A6   |
// |----|----------|-----------|----|----------|-----------|------|-------|-------|
// | 13 |  Odd0.13 | ~Odd0.13  | 13 |  Evn0.13 | ~Evn0.13  | Odd  |  ~A   |  ~B   |
// | 13 |  Odd1.13 | ~Odd1.13  | 13 |  Evn1.13 | ~Evn1.13  |      |  ~C   |       |
// | 13 |  Odd2.13 | ~Odd2.13  | 13 |  Evn2.13 | ~Evn2.13  |      |       |       |
// | 13 |  Odd3.13 | ~Odd3.13  | 13 |  Evn3.13 | ~Evn3.13  |      |       |       |
// | 12 |  Odd4.12 | ~Odd4.12  | 12 |  Evn4.12 | ~Evn4.12  |      |       |       |

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

// $\Sigma_{1}(E)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |    A6   |
// |----|----------|-----------|----|----------|-----------|------|----------|---------|
// | 13 |  Evn0.13 | ~Evn0.13  | 13 |  Odd0.13 | ~Odd0.13  | Evn  |  ~E.13a  | ~E.10a  |
// | 13 |  Evn1.13 | ~Evn1.13  | 13 |  Odd1.13 | ~Odd1.13  |      |  ~E.13b  | ~E.10b  |
// | 13 |  Evn2.13 | ~Evn2.13  | 13 |  Odd2.13 | ~Odd2.13  |      |  ~E.04   | ~E.13c  |
// | 13 |  Evn3.13 | ~Evn3.13  | 13 |  Odd3.13 | ~Odd3.13  |      |  ~E.01   |         |
// | 12 |  Evn4.12 | ~Evn4.12  | 12 |  Odd4.12 | ~Odd4.12  |      |          |         |

// $Ch(E, F, G)$

// | T0 |      A0      |       A1      | T1 |       A2     |       A3      |     A4  |    A5   |      A6     |
// |----|--------------|---------------|----|--------------|---------------|---------|---------|-------------|
// | 13 |  Odd0_EF.13  |  ~Odd0_EF.13  | 13 |  Evn0_EF.13  |  ~Evn0_EF.13  | Odd_EF  |    ~E   |     ~F      |
// | 13 |  Odd1_EF.13  |  ~Odd1_EF.13  | 13 |  Evn1_EF.13  |  ~Evn1_EF.13  | Odd_EF  | Odd_nEG |     Ret     |
// | 13 |  Odd2_EF.13  |  ~Odd2_EF.13  | 13 |  Evn2_EF.13  |  ~Evn2_EF.13  |         |         |             |
// | 13 |  Odd3_EF.13  |  ~Odd3_EF.13  | 13 |  Evn3_EF.13  |  ~Evn3_EF.13  |         |         |             |
// | 12 |  Odd4_EF.12  |  ~Odd4_EF.12  | 12 |  Evn4_EF.12  |  ~Evn4_EF.12  |         |         |             |
// | 13 |  Odd0_nEF.13 |  ~Odd0_nEF.13 | 13 |  Evn0_nEF.13 |  ~Evn0_nEF.13 | Odd_nEG |  ~(¬E)  |     ~G      |
// | 13 |  Odd1_nEF.13 |  ~Odd2_nEF.13 | 13 |  Evn1_nEF.13 |  ~Evn1_nEF.13 |   ~E    |  ~(¬E)  |MASK_EVN_128 |
// | 13 |  Odd2_nEF.13 |  ~Odd4_nEF.13 | 13 |  Evn2_nEF.13 |  ~Evn2_nEF.13 |         |         |             |
// | 13 |  Odd3_nEF.13 |  ~Odd1_nEF.13 | 13 |  Evn3_nEF.13 |  ~Evn3_nEF.13 |         |         |             |
// | 12 |  Odd4_nEF.12 |  ~Odd3_nEF.12 | 12 |  Evn4_nEF.12 |  ~Evn4_nEF.12 |         |         |             |

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

// $\sigma_0(W)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |    A6   |
// |----|----------|-----------|----|----------|-----------|------|----------|---------|
// | 13 |  Evn0.13 | ~Evn0.13  | 13 |  Odd0.13 | ~Odd0.13  | Evn  | ~W.03a   | ~W.13a  |
// | 13 |  Evn1.13 | ~Evn1.13  | 13 |  Odd1.13 | ~Odd1.13  |      | ~W.13b   | ~W.13c  |
// | 13 |  Evn2.13 | ~Evn2.13  | 13 |  Odd2.13 | ~Odd2.13  |      | ~W.03b   | ~W.11   |
// | 13 |  Evn3.13 | ~Evn3.13  | 13 |  Odd3.13 | ~Odd3.13  |      | ~W.01a   | ~W.01b  |
// | 12 |  Evn4.12 | ~Evn4.12  | 12 |  Odd4.12 | ~Odd4.12  |      | ~W.05    | ~W.01c  |

// $\sigma_1(W)$

// | T0 |    A0    |     A1    | T1 |    A2    |     A3    |  A4  |    A5    |    A6   |
// |----|----------|-----------|----|----------|-----------|------|----------|---------|
// | 13 |  Evn0.13 | ~Evn0.13  | 13 |  Odd0.13 | ~Odd0.13  | Evn  | ~W.03a   | ~W.13a  |
// | 13 |  Evn1.13 | ~Evn1.13  | 13 |  Odd1.13 | ~Odd1.13  |      | ~W.13b   | ~W.13c  |
// | 13 |  Evn2.13 | ~Evn2.13  | 13 |  Odd2.13 | ~Odd2.13  |      | ~W.03b   | ~W.11   |
// | 13 |  Evn3.13 | ~Evn3.13  | 13 |  Odd3.13 | ~Odd3.13  |      | ~W.01a   | ~W.01b  |
// | 12 |  Evn4.12 | ~Evn4.12  | 12 |  Odd4.12 | ~Odd4.12  |      | ~W.05    | ~W.01c  |

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
        types::{AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded},
        utils::{
            expr_pow2_ip, expr_pow4_ip, gen_spread_table, get_even_and_odd_bits, negate_spreaded,
            spread, spreaded_maj, u64_in_be_limbs, MASK_EVN_128,
        },
    },
    instructions::assignments::AssignmentInstructions,
    types::AssignedNative,
    utils::{
        util::{fe_to_u128, u128_to_fe, u64_to_fe},
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
    // q_Sigma_0: Selector,
    // q_Sigma_1: Selector,
    // q_sigma_0: Selector,
    // q_sigma_1: Selector,
    q_13_13_13_13_12: Selector,
    // q_10_9_11_2: Selector,
    // q_7_12_2_5_6: Selector,
    // q_12_1x3_7_3_4_3: Selector,
    // q_add_mod_2_32: Selector,
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
        // let q_Sigma_0 = meta.selector();
        // let q_Sigma_1 = meta.selector();
        // let q_sigma_0 = meta.selector();
        // let q_sigma_1 = meta.selector();

        let q_13_13_13_13_12 = meta.selector();
        // let q_10_9_11_2 = meta.selector();
        // let q_7_12_2_5_6 = meta.selector();
        // let q_12_1x3_7_3_4_3 = meta.selector();
        // let q_add_mod_2_32 = meta.selector();

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

        Sha512Config {
            advice_cols,
            fixed_cols,
            q_lookup,
            table,
            q_maj,
            q_half_ch,
            // q_Sigma_0,
            // q_Sigma_1,
            // q_sigma_0,
            // q_sigma_1,
            q_13_13_13_13_12,
            // q_10_9_11_2,
            // q_7_12_2_5_6,
            // q_12_1x3_7_3_4_3,
            // q_add_mod_2_32,
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
}
