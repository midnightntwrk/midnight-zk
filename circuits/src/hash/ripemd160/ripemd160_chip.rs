//! Implementation in-circuit of the RIPEMD-160 hash function.

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
    hash::ripemd160::{
        types::{AssignedSpreaded, AssignedWord, State},
        utils::{
            expr_pow2_ip, expr_pow4_ip, gen_spread_table, get_even_and_odd_bits, limb_coeffs,
            limb_lengths, limb_values, negate_spreaded, spread, spreaded_sum, u32_in_be_limbs,
            MASK_EVN_64,
        },
    },
    instructions::{AssignmentInstructions, DecompositionInstructions, EqualityInstructions},
    types::AssignedByte,
    utils::{
        util::{fe_to_u32, fe_to_u64, u32_to_fe, u64_to_fe},
        ComposableChip,
    },
};

/// Number of advice columns used by the identities of the RIPEMD160 chip.
pub const NB_RIPEMD160_ADVICE_COLS: usize = 8;

/// Number of fixed columns used by the identities of the RIPEMD160 chip.
pub const NB_RIPEMD160_FIXED_COLS: usize = 7;

/// Constants K and K' (added constants per round)
pub const K: [u32; 5] = [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E];
pub const K_PRIME: [u32; 5] = [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000];

/// Initial values H0, H1, H2, H3, H4
pub const IV: [u32; 5] = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];

/// Message word selection order R (left) and R_PRIME (right)
pub const R: [[u8; 16]; 5] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8],
    [3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12],
    [1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2],
    [4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13],
];
pub const R_PRIME: [[u8; 16]; 5] = [
    [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12],
    [6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2],
    [15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13],
    [8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14],
    [12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11],
];

/// Rotation amounts S (left) and S_PRIME (right)
pub const S: [[u8; 16]; 5] = [
    [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    [7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12],
    [11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5],
    [11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12],
    [9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6],
];
pub const S_PRIME: [[u8; 16]; 5] = [
    [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6],
    [9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11],
    [9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5],
    [15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8],
    [8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11],
];

/// Tag for the even and odd 11-11-10 decompositions.
#[derive(Copy, Clone, Debug)]
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

/// Configuration for the RIPEMD160 chip.
#[derive(Clone, Debug)]
pub struct RipeMD160Config {
    advice_cols: [Column<Advice>; NB_RIPEMD160_ADVICE_COLS],
    fixed_cols: [Column<Fixed>; NB_RIPEMD160_FIXED_COLS],
    q_lookup: Selector,
    table: SpreadTable,
    q_11_11_10: Selector,
    q_spr_sum_evn: Selector,
    q_spr_sum_odd: Selector,
    q_left_rot: Selector,
    q_add: Selector,
    q_mod_add: Selector,
}

/// Chip for RIPEMD160.
#[derive(Clone, Debug)]
pub struct RipeMD160Chip<F: PrimeField> {
    config: RipeMD160Config,
    pub(super) native_gadget: NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>,
}

impl<F: PrimeField> Chip<F> for RipeMD160Chip<F> {
    type Config = RipeMD160Config;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: PrimeField> ComposableChip<F> for RipeMD160Chip<F> {
    type SharedResources = (
        [Column<Advice>; NB_RIPEMD160_ADVICE_COLS],
        [Column<Fixed>; NB_RIPEMD160_FIXED_COLS],
    );

    type InstructionDeps = NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>>;

    fn new(config: &RipeMD160Config, native_gadget: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_gadget: native_gadget.clone(),
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_res: &Self::SharedResources,
    ) -> Self::Config {
        let fixed_cols = shared_res.1;
        // The last fixed column is used for the constants of 0 which will be assigned
        // in the advice columns.
        meta.enable_constant(fixed_cols[NB_RIPEMD160_FIXED_COLS - 1]);

        // Columns A0, A1 and A2 do not need to be copy-enabled.
        // We have the convention that chips enable copy in a prefix of their shared
        // advice columns. Thus we let them be the last four columns of the given
        // shared resources.
        let advice_cols = [3, 4, 5, 6, 7, 0, 1, 2].map(|i| shared_res.0[i]);
        for column in advice_cols.iter().rev().take(5) {
            meta.enable_equality(*column);
        }

        // // Only for test!!!
        // for column in advice_cols.iter().rev() {
        //     meta.enable_equality(*column);
        // }
        let q_lookup = meta.complex_selector();
        let table = SpreadTable {
            nbits_col: meta.lookup_table_column(),
            plain_col: meta.lookup_table_column(),
            sprdd_col: meta.lookup_table_column(),
        };

        let q_11_11_10 = meta.selector();
        let q_spr_sum_evn = meta.selector();
        let q_spr_sum_odd = meta.selector();
        let q_left_rot = meta.selector();
        let q_add = meta.selector();
        let q_mod_add = meta.selector();

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

        meta.create_gate("11-11-10 decomposition", |meta| {
            // See function `assign_sprdd_sum` for a description of the following
            // layout.
            let p11a = meta.query_advice(advice_cols[0], Rotation(-1));
            let p11b = meta.query_advice(advice_cols[0], Rotation(0));
            let p_10 = meta.query_advice(advice_cols[0], Rotation(1));
            let output = meta.query_advice(advice_cols[4], Rotation(-1));

            let id = expr_pow2_ip([21, 10, 0], [&p11a, &p11b, &p_10]) - output;

            Constraints::with_selector(q_11_11_10, vec![("11-11-10 decomposition", id)])
        });

        meta.create_gate("spreaded sum with even output", |meta| {
            // See function `assign_sprdd_sum` for a description of the following
            // layout.
            let sA = meta.query_advice(advice_cols[5], Rotation(-1));
            let sB = meta.query_advice(advice_cols[6], Rotation(-1));
            let sC = meta.query_advice(advice_cols[7], Rotation(-1));
            let s_evn_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_evn_010 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_odd_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_odd_010 = meta.query_advice(advice_cols[3], Rotation(1));

            let s_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_010]);
            let s_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_010]);
            let id = (sA + sB + sC) - (s_evn + s_odd * Expression::Constant(F::from(2u64)));

            Constraints::with_selector(q_spr_sum_evn, vec![("spreaded sum even", id)])
        });

        meta.create_gate("spreaded sum with odd output", |meta| {
            // See function `assign_sprdd_sum` for a description of the following
            // layout.
            let sA = meta.query_advice(advice_cols[5], Rotation(-1));
            let sB = meta.query_advice(advice_cols[6], Rotation(-1));
            let sC = meta.query_advice(advice_cols[7], Rotation(-1));
            let s_odd_11a = meta.query_advice(advice_cols[1], Rotation(-1));
            let s_odd_11b = meta.query_advice(advice_cols[1], Rotation(0));
            let s_odd_010 = meta.query_advice(advice_cols[1], Rotation(1));
            let s_evn_11a = meta.query_advice(advice_cols[3], Rotation(-1));
            let s_evn_11b = meta.query_advice(advice_cols[3], Rotation(0));
            let s_evn_010 = meta.query_advice(advice_cols[3], Rotation(1));

            let s_evn = expr_pow4_ip([21, 10, 0], [&s_evn_11a, &s_evn_11b, &s_evn_010]);
            let s_odd = expr_pow4_ip([21, 10, 0], [&s_odd_11a, &s_odd_11b, &s_odd_010]);
            let id = (sA + sB + sC) - (s_evn + s_odd * Expression::Constant(F::from(2u64)));

            Constraints::with_selector(q_spr_sum_odd, vec![("spreaded sum odd", id)])
        });

        meta.create_gate("left rotation", |meta| {
            // See function `left_rotate` for a description of the following layout.
            let limb_a = meta.query_advice(advice_cols[0], Rotation(-1));
            let limb_b = meta.query_advice(advice_cols[2], Rotation(-1));
            let limb_c = meta.query_advice(advice_cols[0], Rotation(0));
            let limb_d = meta.query_advice(advice_cols[2], Rotation(0));
            let w = meta.query_advice(advice_cols[4], Rotation(-1));
            let rot_w = meta.query_advice(advice_cols[4], Rotation(0));

            let coef_a = meta.query_fixed(fixed_cols[2], Rotation(-1));
            let coef_b = meta.query_fixed(fixed_cols[3], Rotation(-1));
            let coef_c = meta.query_fixed(fixed_cols[2], Rotation(0));
            let coef_d = meta.query_fixed(fixed_cols[3], Rotation(0));

            let coef_a_rot = meta.query_fixed(fixed_cols[4], Rotation(-1));
            let coef_b_rot = meta.query_fixed(fixed_cols[5], Rotation(-1));
            let coef_c_rot = meta.query_fixed(fixed_cols[4], Rotation(0));
            let coef_d_rot = meta.query_fixed(fixed_cols[5], Rotation(0));

            let id_word = coef_a * limb_a.clone()
                + coef_b * limb_b.clone()
                + coef_c * limb_c.clone()
                + coef_d * limb_d.clone()
                - w;
            let id_rot = coef_a_rot * limb_a
                + coef_b_rot * limb_b
                + coef_c_rot * limb_c
                + coef_d_rot * limb_d
                - rot_w;

            Constraints::with_selector(
                q_left_rot,
                vec![
                    ("decomposition of word", id_word),
                    ("decomposition of rotated word", id_rot),
                ],
            )
        });

        meta.create_gate("addition", |meta| {
            let a = meta.query_advice(advice_cols[4], Rotation(0));
            let b = meta.query_advice(advice_cols[5], Rotation(0));
            let c = meta.query_advice(advice_cols[6], Rotation(0));

            let id = a + b - c;

            Constraints::with_selector(q_add, vec![("addition", id)])
        });

        meta.create_gate("addition mod 2^32", |meta| {
            let a = meta.query_advice(advice_cols[4], Rotation(0));
            let b = meta.query_advice(advice_cols[5], Rotation(0));
            let c = meta.query_advice(advice_cols[6], Rotation(0));
            let d = meta.query_advice(advice_cols[7], Rotation(0));

            let carry = meta.query_advice(advice_cols[0], Rotation(0));
            let res = meta.query_advice(advice_cols[3], Rotation(0));

            let id =
                a + b + c + d - res - carry.clone() * Expression::Constant(F::from(1u64 << 32));
            let mut range_three = Expression::Constant(F::from(1u64));
            for i in 0..=3 {
                range_three = range_three * (carry.clone() - Expression::Constant(F::from(i)));
            }

            Constraints::with_selector(
                q_mod_add,
                vec![
                    ("addition mod 2^32", id),
                    ("carry within three", range_three),
                ],
            )
        });

        RipeMD160Config {
            advice_cols,
            fixed_cols,
            q_lookup,
            table,
            q_11_11_10,
            q_spr_sum_evn,
            q_spr_sum_odd,
            q_left_rot,
            q_add,
            q_mod_add,
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

impl<F: PrimeField> RipeMD160Chip<F> {
    fn ripemd160(
        &self,
        layouter: &mut impl Layouter<F>,
        input_bytes: &[AssignedByte<F>],
    ) -> Result<State<F>, Error> {
        let round_consts: [AssignedWord<F>; 5] = [
            AssignedWord::fixed(layouter, &self.native_gadget, K[0])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K[1])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K[2])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K[3])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K[4])?,
        ];
        let round_consts_prime: [AssignedWord<F>; 5] = [
            AssignedWord::fixed(layouter, &self.native_gadget, K_PRIME[0])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K_PRIME[1])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K_PRIME[2])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K_PRIME[3])?,
            AssignedWord::fixed(layouter, &self.native_gadget, K_PRIME[4])?,
        ];

        let zero = AssignedWord::fixed(layouter, &self.native_gadget, 0u32)?;

        let mut state = State::fixed(layouter, &self.native_gadget, IV)?;

        let padded_bytes = self.pad(layouter, input_bytes)?;

        // Process each 64-byte block.
        for block_bytes in padded_bytes.chunks(64) {
            self.process_block(
                layouter,
                &mut state,
                block_bytes.try_into().unwrap(),
                round_consts.each_ref(),
                round_consts_prime.each_ref(),
                &zero,
            )?;
        }

        Ok(state)
    }

    /// Pads the input byte array to be a multiple of 64 bytes (512 bits), where
    /// the last 8 bytes represent the length of the original input in
    /// little-endian.
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
        for byte in u64::to_le_bytes(l as u64) {
            padded.push(self.native_gadget.assign_fixed(layouter, byte)?);
        }

        Ok(padded)
    }

    /// Given a byte array of exactly 64 bytes, this function converts it into a
    /// block of 16 `AssignedWord` values, each (32 bits) value representing 4
    /// bytes in *little-endian*.
    pub(super) fn block_from_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>; 64],
    ) -> Result<[AssignedWord<F>; 16], Error> {
        Ok(bytes
            .chunks(4)
            .map(|word_bytes| {
                self.native_gadget
                    .assigned_from_le_bytes(layouter, word_bytes)
                    .map(AssignedWord)
            })
            .collect::<Result<Vec<_>, Error>>()?
            .try_into()
            .unwrap())
    }

    fn process_block(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &mut State<F>,
        block_bytes: &[AssignedByte<F>; 64],
        round_consts: [&AssignedWord<F>; 5],
        round_consts_prime: [&AssignedWord<F>; 5],
        zero: &AssignedWord<F>,
    ) -> Result<(), Error> {
        let block_words = self.block_from_bytes(layouter, block_bytes)?;

        let mut temp_state = state.clone();
        let mut temp_state_prime = state.clone();

        for j in 0..80 {
            // for j in 0..1 {
            let word_idx = R[j / 16][j % 16] as usize;
            let word = &block_words[word_idx];
            let round_const = round_consts[j / 16];

            let word_prime_idx = R_PRIME[j / 16][j % 16] as usize;
            let word_prime = &block_words[word_prime_idx];
            let round_const_prime = round_consts_prime[j / 16];

            self.round_function(
                layouter,
                j,
                &mut temp_state,
                &mut temp_state_prime,
                word,
                word_prime,
                round_const,
                round_const_prime,
                zero,
            )?;
        }

        // Update the state.
        let State {
            h0: A,
            h1: B,
            h2: C,
            h3: D,
            h4: E,
        } = temp_state;
        print!(
            "A: {:?}, B: {:?}, C: {:?}, D: {:?}, E: {:?}\n",
            &A.0.value(),
            &B.0.value(),
            &C.0.value(),
            &D.0.value(),
            &E.0.value()
        );
        let State {
            h0: A_prime,
            h1: B_prime,
            h2: C_prime,
            h3: D_prime,
            h4: E_prime,
        } = temp_state_prime;
        print!(
            "A': {:?}, B': {:?}, C': {:?}, D': {:?}, E': {:?}\n",
            &A_prime.0.value(),
            &B_prime.0.value(),
            &C_prime.0.value(),
            &D_prime.0.value(),
            &E_prime.0.value()
        );

        let T = self.add_mod_2_32(layouter, &[&state.h1, &C, &D_prime], &zero)?;
        state.h1 = self.add_mod_2_32(layouter, &[&state.h2, &D, &E_prime], &zero)?;
        state.h2 = self.add_mod_2_32(layouter, &[&state.h3, &E, &A_prime], &zero)?;
        state.h3 = self.add_mod_2_32(layouter, &[&state.h4, &A, &B_prime], &zero)?;
        state.h4 = self.add_mod_2_32(layouter, &[&state.h0, &B, &C_prime], &zero)?;
        state.h0 = T;

        Ok(())
    }

    fn round_function(
        &self,
        layouter: &mut impl Layouter<F>,
        idx: usize,
        temp_state: &mut State<F>,
        temp_state_prime: &mut State<F>,
        word: &AssignedWord<F>,
        word_prime: &AssignedWord<F>,
        round_const: &AssignedWord<F>,
        round_const_prime: &AssignedWord<F>,
        zero: &AssignedWord<F>,
    ) -> Result<(), Error> {
        // TODO: optimize the parallelism of the two sides.
        let State {
            h0: ref mut A,
            h1: ref mut B,
            h2: ref mut C,
            h3: ref mut D,
            h4: ref mut E,
        } = temp_state;
        let State {
            h0: ref mut A_prime,
            h1: ref mut B_prime,
            h2: ref mut C_prime,
            h3: ref mut D_prime,
            h4: ref mut E_prime,
        } = temp_state_prime;

        let rot = S[idx / 16][idx % 16];
        let rot_prime = S_PRIME[idx / 16][idx % 16];

        let temp = self.f(layouter, idx, B, C, D)?;
        let temp = self.add_mod_2_32(layouter, &[A, &temp, word, round_const], zero)?;
        let temp = self.left_rotate(layouter, &temp, rot)?;
        let T = self.add_mod_2_32(layouter, &[&temp, E], zero)?;
        *A = E.clone();
        *E = D.clone();
        *D = self.left_rotate(layouter, C, 10)?;
        *C = B.clone();
        *B = T;

        let temp_prime = self.f(layouter, 79 - idx, B_prime, C_prime, D_prime)?;
        let temp_prime = self.add_mod_2_32(
            layouter,
            &[A_prime, &temp_prime, word_prime, round_const_prime],
            zero,
        )?;
        let temp_prime = self.left_rotate(layouter, &temp_prime, rot_prime)?;
        let T_prime = self.add_mod_2_32(layouter, &[&temp_prime, E_prime], zero)?;
        *A_prime = E_prime.clone();
        *E_prime = D_prime.clone();
        *D_prime = self.left_rotate(layouter, C_prime, 10)?;
        *C_prime = B_prime.clone();
        *B_prime = T_prime.clone();

        Ok(())
    }

    fn f(
        &self,
        layouter: &mut impl Layouter<F>,
        idx: usize,
        X: &AssignedWord<F>,
        Y: &AssignedWord<F>,
        Z: &AssignedWord<F>,
    ) -> Result<AssignedWord<F>, Error> {
        let [sprdd_X, sprdd_Y, sprdd_Z] = [
            self.prepare_spreaded(layouter, X)?,
            self.prepare_spreaded(layouter, Y)?,
            self.prepare_spreaded(layouter, Z)?,
        ];

        match idx {
            // f(X, Y, Z) = X ⊕ Y ⊕ Z
            0..=15 => self.f_type_one(layouter, &sprdd_X, &sprdd_Y, &sprdd_Z),
            // f(X, Y, Z) = (X ∧ Y) ∨ (¬X ∧ Z)
            16..=31 => self.f_type_two(layouter, &sprdd_X, &sprdd_Y, &sprdd_Z),
            // f(X, Y, Z) = (X ∨ ¬Y) ⊕ Z
            32..=47 => self.f_type_three(layouter, &sprdd_X, &sprdd_Y, &sprdd_Z),
            // f(X, Y, Z) = (X ∧ Z) ∨ (Y ∧ ¬Z)
            48..=63 => self.f_type_two(layouter, &sprdd_Z, &sprdd_X, &sprdd_Y),
            // f(X, Y, Z) = X ⊕ (Y ∨ ¬Z)
            64..=79 => self.f_type_three(layouter, &sprdd_Y, &sprdd_Z, &sprdd_X),
            _ => unreachable!("Function index out of range"),
        }
    }

    /// Given an assigned word X, this function prepares its spreaded form.
    fn prepare_spreaded(
        &self,
        layouter: &mut impl Layouter<F>,
        word: &AssignedWord<F>,
    ) -> Result<AssignedSpreaded<F, 32>, Error> {
        /*
        Given assigned word X, we first compute its spreaded form ~X, and then
        apply [`assign_sprdd_11_11_10`] to the value of ~X as follows:

        | T0 |    A0   |     A1   | T1 |   A2   |   A3   |  A4 | A5 | A6 | A7 |
        |----|---------|----------|----|--------|--------|-----|----|----|----|
        | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   | Evn | ~X | ~0 | ~0 |
        | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   |     |    |    |    | <- q_spr_sum_evn, q_11_11_10
        | 10 | Evn.11a | ~Evn.11a | 10 |   0    |   ~0   |     |    |    |    |

        with constraints of:

         1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
              Evn: (Evn.11a, Evn.11b, Evn.10)
              Odd: (0, 0, 0)

         2) asserting the 11-11-10 decomposition identity for Evn:
               2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
             = Evn

         3) asserting the spr_sum_evn identity:
               (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
           2 * (4^21 * ~0       + 4^10 * ~0       + ~0     )
              = ~X + ~0 + ~0

         4) asserting that:
                 Evn = X
        */
        let adv_cols = self.config().advice_cols;
        let sprdd_val = word.0.value().map(|&w| spread(fe_to_u32(w)));

        let (res, sprdd_word) = layouter.assign_region(
            || "Assign prepare_spreaded",
            |mut region| {
                self.config().q_spr_sum_evn.enable(&mut region, 1)?;

                let sprdd_word = region
                    .assign_advice(|| "sprdd_word", adv_cols[5], 0, || sprdd_val.map(u64_to_fe))
                    .map(AssignedSpreaded)?;
                region.assign_advice_from_constant(|| "sprdd_ZERO", adv_cols[6], 0, F::ZERO)?;
                region.assign_advice_from_constant(|| "sprdd_ZERO", adv_cols[7], 0, F::ZERO)?;

                let res = self.assign_sprdd_11_11_10(&mut region, sprdd_val, Parity::Evn, 0)?;

                Ok((res, sprdd_word))
            },
        )?;

        let _ = self.native_gadget.is_equal(layouter, &word.0, &res.0)?;
        Ok(sprdd_word)
    }

    /// Given two assigned spreaded ~X and ~Y, this function returns X ∧ Y
    /// the bitwise AND as an assigned word.
    fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_X: &AssignedSpreaded<F, 32>,
        sprdd_Y: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        X ∧ Y can be computed as the odd part of ~X + ~Y + ~0. We apply [`assign_sprdd_11_11_10`]
        to the value of ~X + ~Y + ~0 as follows:

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |  A5 | A6 | A7 |
        |----|---------|----------|----|---------|----------|-----|-----|----|----|
        | 11 | Odd.11a | ~Odd.11a | 11 | Evn.11a | ~Evn.11a | Odd |  ~X | ~Y | ~0 |
        | 11 | Odd.11b | ~Odd.11b | 11 | Evn.11b | ~Evn.11b |     |     |    |    | <- q_11_11_10, q_spr_sum_odd
        | 10 | Odd.10  | ~Odd.10  | 10 | Evn.10  | ~Evn.10  |     |     |    |    |

        with constraints of:

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Odd: (Odd.11a, Odd.11b, Odd.10)
             Evn: (Evn.11a, Evn.11b, Evn.10)

        2) asserting the 11-11-10 decomposition identity for Odd:
              2^21 * Odd.11a + 2^10 * Odd.11b + Odd.10
            = Odd

        3) asserting the spr_sum_odd identity:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             = ~X + ~Y + ~0

        and returns `Odd`
        */
        let adv_cols = self.config().advice_cols;
        let val_of_sprdd_forms: Value<[u64; 3]> = Value::from_iter([
            sprdd_X.0.value().copied().map(fe_to_u64),
            sprdd_Y.0.value().copied().map(fe_to_u64),
            Value::known(0u64),
        ])
        .map(|sprdd_forms: Vec<u64>| sprdd_forms.try_into().unwrap());
        let val_of_sum = val_of_sprdd_forms.map(|vals| spreaded_sum(vals));

        layouter.assign_region(
            || "Assign AND",
            |mut region| {
                self.config().q_spr_sum_odd.enable(&mut region, 1)?;

                sprdd_X.0.copy_advice(|| "sprdd_X", &mut region, adv_cols[5], 0)?;
                sprdd_Y.0.copy_advice(|| "sprdd_Y", &mut region, adv_cols[6], 0)?;
                region.assign_advice_from_constant(|| "sprdd_ZERO", adv_cols[7], 0, F::ZERO)?;

                self.assign_sprdd_11_11_10(&mut region, val_of_sum, Parity::Odd, 0)
            },
        )
    }

    /// Given two assigned spreaded ~X and ~Y, this function returns X ⊕ Y
    /// the bitwise XOR as an assigned word.
    fn xor(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_X: &AssignedSpreaded<F, 32>,
        sprdd_Y: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        X ⊕ Y can be computed as the even part of ~X + ~Y + ~0. We apply [`assign_sprdd_11_11_10`]
        to the value of ~X + ~Y + ~0 as follows:

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |  A5 | A6 | A7 |
        |----|---------|----------|----|---------|----------|-----|-----|----|----|
        | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn |  ~X | ~Y | ~0 |
        | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     |     |    |    | <- q_11_11_10, q_spr_sum_evn
        | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |     |    |    |

        with constraints of:

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Evn:
              2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
            = Evn

        3) asserting the spr_sum_evn identity:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             = ~A + ~B + ~C

        and returns `Evn`.
        */
        let adv_cols = self.config().advice_cols;
        let val_of_sprdd_forms: Value<[u64; 3]> = Value::from_iter([
            sprdd_X.0.value().copied().map(fe_to_u64),
            sprdd_Y.0.value().copied().map(fe_to_u64),
            Value::known(0u64),
        ])
        .map(|sprdd_forms: Vec<u64>| sprdd_forms.try_into().unwrap());
        let val_of_sum = val_of_sprdd_forms.map(|vals| spreaded_sum(vals));

        layouter.assign_region(
            || "Assign XOR",
            |mut region| {
                self.config().q_spr_sum_evn.enable(&mut region, 1)?;

                sprdd_X.0.copy_advice(|| "sprdd_X", &mut region, adv_cols[5], 0)?;
                sprdd_Y.0.copy_advice(|| "sprdd_Y", &mut region, adv_cols[6], 0)?;
                region.assign_advice_from_constant(|| "spreaded ZERO", adv_cols[7], 0, F::ZERO)?;

                self.assign_sprdd_11_11_10(&mut region, val_of_sum, Parity::Evn, 0)
            },
        )
    }

    /// Given three assigned spreaded ~X, ~Y, ~Z, this function computes the
    /// value of f(X, Y, Z) = X ⊕ Y ⊕ Z, defined as type one function in
    /// RIPEMD160.
    fn f_type_one(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_X: &AssignedSpreaded<F, 32>,
        sprdd_Y: &AssignedSpreaded<F, 32>,
        sprdd_Z: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        f(X, Y, Z) = X ⊕ Y ⊕ Z can be computed as the even part of ~X + ~Y + ~Z. We apply
        [`assign_sprdd_11_11_10`] to the value of ~X + ~Y + ~Z as follows:

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |  A5 | A6 | A7 |
        |----|---------|----------|----|---------|----------|-----|-----|----|----|
        | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn |  ~X | ~Y | ~Z |
        | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     |     |    |    | <- q_11_11_10, q_spr_sum_evn
        | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |     |    |    |

        with constraints of:

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

        2) asserting the 11-11-10 decomposition identity for Evn:
              2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
            = Evn

        3) asserting the spr_sum_evn identity:
              (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
          2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
             = ~X + ~Y + ~Z

        and returns `Evn`.
        */
        let adv_cols = self.config().advice_cols;
        let val_of_sprdd_forms: Value<[u64; 3]> = Value::from_iter([
            sprdd_X.0.value().copied().map(fe_to_u64),
            sprdd_Y.0.value().copied().map(fe_to_u64),
            sprdd_Z.0.value().copied().map(fe_to_u64),
        ])
        .map(|sprdd_forms: Vec<u64>| sprdd_forms.try_into().unwrap());
        let val_of_sum = val_of_sprdd_forms.map(|vals| spreaded_sum(vals));

        layouter.assign_region(
            || "Assign f_type_one",
            |mut region| {
                self.config().q_spr_sum_evn.enable(&mut region, 1)?;

                sprdd_X.0.copy_advice(|| "sprdd_X", &mut region, adv_cols[5], 0)?;
                sprdd_Y.0.copy_advice(|| "sprdd_Y", &mut region, adv_cols[6], 0)?;
                sprdd_Z.0.copy_advice(|| "sprdd_Z", &mut region, adv_cols[7], 0)?;

                self.assign_sprdd_11_11_10(&mut region, val_of_sum, Parity::Evn, 0)
            },
        )
    }

    /// Given three assigned spreaded ~X, ~Y, ~Z, this function computes the
    /// value of f(X, Y, Z) = (X ∧ Y) ∨ (¬X ∧ Z), defined as type two function
    /// in RIPEMD160.
    fn f_type_two(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_X: &AssignedSpreaded<F, 32>,
        sprdd_Y: &AssignedSpreaded<F, 32>,
        sprdd_Z: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        f(X, Y, Z) = (X ∧ Y) ∨ (¬X ∧ Z) = (X ∧ Y) ⊕ (¬X ∧ Z)
        Therefore, f(X, Y, Z) is exactly Ch(X, Y, Z) from SHA256, and we apply the same
        technique used in SHA256 chip to compute it, except that we fill A7 with ~0 constant
        to satisfy the spr_sum_odd constraint:

         | T0 |      A0     |      A1      | T1 |      A2     |      A3      |    A4   |    A5   |      A6     | A7 |
         |----|-------------|--------------|----|-------------|--------------|---------|---------|-------------|----|
         | 11 |  Odd_XY.11a |  ~Odd_XY.11a | 11 |  Evn_XY.11a |  ~Evn_XY.11a | Odd_XY  |   ~X    |      ~Y     | ~0 |
         | 11 |  Odd_XY.11b |  ~Odd_XY.11b | 11 |  Evn_XY.11b |  ~Evn_XY.11b | Odd_XY  | Odd_nXZ |     Ret     |    | <- q_spr_sum_odd, q_11_11_10, q_add
         | 10 |  Odd_XY.10  |   ~Odd_XY.10 | 10 |  Evn_XY.10  |  ~Evn_XY.10  |         |         |             |    |
         | 11 | Odd_nXZ.11a | ~Odd_nXZ.11a | 11 | Evn_nXZ.11a | ~Evn_nXZ.11a | Odd_nXZ |  ~(¬X)  |      ~Z     | ~0 |
         | 11 | Odd_nXZ.11b | ~Odd_nXZ.11b | 11 | Evn_nXZ.11b | ~Evn_nXZ.11b |   ~X    |  ~(¬X)  | MASK_EVN_64 |    | <- q_spr_sum_odd, q_11_11_10, q_add
         | 10 | Odd_nXZ.10  |  ~Odd_nXZ.10 | 10 | Evn_nXZ.10  | ~Evn_nXZ.10  |         |         |             |    |

        with constraints of:

        1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd,
           for both (~X + ~Y) and (~(¬X) + ~Z):
             Evn_XY: (Evn_XY.11a, Evn_XY.11b, Evn_XY.10)
             Odd_XY: (Odd_XY.11a, Odd_XY.11b, Odd_XY.10)
             Evn_nXZ: (Evn_nXZ.11a, Evn_nXZ.11b, Evn_nXZ.10)
             Odd_nXZ: (Odd_nXZ.11a, Odd_nXZ.11b, Odd_nXZ.10)
        2) asserting the 11-11-10 decomposition identity for Odd_XY and Odd_nXZ:
             2^21 * Odd_XY.11a + 2^10 * Odd_XY.11b + Odd_XY.10
            = Odd_XY
             2^21 * Odd_nXZ.11a + 2^10 * Odd_nXZ.11b + Odd_nXZ.10
            = Odd_nXZ

        3) asserting the sprdd_sum_odd identity for (~X + ~Y + ~0) and (~(¬X) + ~Z + ~0):
             (4^21 * ~Evn_XY.11a + 4^10 * ~Evn_XY.11b + ~Evn_XY.10) + 2 *
             (4^21 * ~Odd_XY.11a + 4^10 * ~Odd_XY.11b + ~Odd_XY.10)
            = ~X + ~Y + ~0

             (4^21 * ~Evn_nXZ.11a + 4^10 * ~Evn_nXZ.11b + ~Evn_nXZ.10) +
         2 * (4^21 * ~Odd_nXZ.11a + 4^10 * ~Odd_nXZ.11b + ~Odd_nXZ.10)
            = ~(¬X) + ~Z + ~0
        4) asserting the addition identities:
            Ret         = Odd_XY + Odd_nXZ
            MASK_EVN_64 = ~X + ~(¬X)

        The output is Ret.
        */
        let adv_cols = self.config().advice_cols;

        let sprdd_X_val = sprdd_X.0.value().copied().map(fe_to_u64);
        let sprdd_Y_val = sprdd_Y.0.value().copied().map(fe_to_u64);
        let sprdd_Z_val = sprdd_Z.0.value().copied().map(fe_to_u64);
        let sprdd_nX_val = sprdd_X_val.map(negate_spreaded);

        let XplusY_val = sprdd_X_val + sprdd_Y_val;
        let nXplusZ_val = sprdd_nX_val + sprdd_Z_val;
        let sprdd_nX_val: Value<F> = sprdd_nX_val.map(u64_to_fe);

        layouter.assign_region(
            || "Assign f_type_two",
            |mut region| {
                self.config().q_spr_sum_odd.enable(&mut region, 1)?;
                self.config().q_add.enable(&mut region, 1)?;
                self.config().q_spr_sum_odd.enable(&mut region, 4)?;
                self.config().q_add.enable(&mut region, 4)?;

                region.assign_advice_from_constant(|| "sprdd_ZERO", adv_cols[7], 0, F::ZERO)?;
                region.assign_advice_from_constant(|| "sprdd_ZERO", adv_cols[7], 3, F::ZERO)?;

                sprdd_X.0.copy_advice(|| "sprdd_X", &mut region, adv_cols[5], 0)?;
                sprdd_X.0.copy_advice(|| "sprdd_X", &mut region, adv_cols[4], 4)?;

                sprdd_Y.0.copy_advice(|| "sprdd_Y", &mut region, adv_cols[6], 0)?;
                sprdd_Z.0.copy_advice(|| "sprdd_Z", &mut region, adv_cols[6], 3)?;

                let sprdd_nX =
                    region.assign_advice(|| "sprdd_nX", adv_cols[5], 3, || sprdd_nX_val)?;
                sprdd_nX.copy_advice(|| "sprdd_nX", &mut region, adv_cols[5], 4)?;

                region.assign_advice_from_constant(
                    || "MASK_EVN_64",
                    adv_cols[6],
                    4,
                    F::from(MASK_EVN_64),
                )?;

                let odd_XY = self.assign_sprdd_11_11_10(&mut region, XplusY_val, Parity::Odd, 0)?;
                odd_XY.0.copy_advice(|| "Odd_XY", &mut region, adv_cols[4], 1)?;

                let odd_nXZ =
                    self.assign_sprdd_11_11_10(&mut region, nXplusZ_val, Parity::Odd, 3)?;
                odd_nXZ.0.copy_advice(|| "Odd_nXZ", &mut region, adv_cols[5], 1)?;

                let ret_val = odd_XY.0.value().copied() + odd_nXZ.0.value().copied();
                region.assign_advice(|| "Ret", adv_cols[6], 1, || ret_val).map(AssignedWord)
            },
        )
    }

    /// Given three assigned spreaded ~X, ~Y, ~Z, this function computes the
    /// value of f(X, Y, Z) = (X ∨ ¬Y) ⊕ Z, defined as type three function in
    /// RIPEMD160.
    fn f_type_three(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_X: &AssignedSpreaded<F, 32>,
        sprdd_Y: &AssignedSpreaded<F, 32>,
        sprdd_Z: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        f(X, Y, Z) = (X ∨ ¬Y) ⊕ Z = (X ⊕ ¬Y ⊕ Z) ⊕ (X ∧ ¬Y)
        Therefore, we first compute and witness ~nY using addition identity; then compute temp1 = X ⊕ ¬Y ⊕ Z
        using `f_type_one`, and prepare its spreaded form ~temp1; then we compute temp2 = X ∧ ¬Y
        using `and`, prepare its spreaded form ~temp2; finally, we compute f(X, Y, Z) = temp1 ⊕ temp2 using `xor`.
        */
        let adv_cols = self.config().advice_cols;
        let sprdd_Y_val = sprdd_Y.0.value().copied().map(fe_to_u64);
        let sprdd_nY_val = sprdd_Y_val.map(negate_spreaded).map(u64_to_fe);

        let sprdd_nY = layouter.assign_region(
            || "Assign sprdd_nY",
            |mut region| {
                self.config.q_add.enable(&mut region, 0)?;

                sprdd_Y.0.copy_advice(|| "sprdd_Y", &mut region, adv_cols[4], 0)?;
                region.assign_advice_from_constant(
                    || "MASK_EVN_64",
                    adv_cols[6],
                    0,
                    F::from(MASK_EVN_64),
                )?;
                region
                    .assign_advice(|| "sprdd_nY", adv_cols[5], 0, || sprdd_nY_val)
                    .map(AssignedSpreaded)
            },
        )?;

        let temp1 = self.f_type_one(layouter, sprdd_X, &sprdd_nY, sprdd_Z)?;
        let sprdd_temp1 = self.prepare_spreaded(layouter, &temp1)?;
        let temp2 = self.and(layouter, sprdd_X, &sprdd_nY)?;
        let sprdd_temp2 = self.prepare_spreaded(layouter, &temp2)?;

        self.xor(layouter, &sprdd_temp1, &sprdd_temp2)
    }

    /// Given an assigned word X and a left rotation amount `rot`, this function
    /// computes the left rotation of X by `rot` bits, returning Rot(X) as an
    /// assigned word.
    fn left_rotate(
        &self,
        layouter: &mut impl Layouter<F>,
        word: &AssignedWord<F>,
        rot: u8,
    ) -> Result<AssignedWord<F>, Error> {
        /*
         Computing the left rotation Rol(X, rot) fills the circuit layout as follows:

        |  T0 |   A0  |   A1  |  T1 |   A2  |   A3  |   A4  |   T2    |   T3    |      T4     |      T5     |
        |-----|-------|-------|-----|-------|-------|-------|---------|---------|-------------|-------------|
        | t_a |  l_a  | ~l_a  | t_b |  l_b  | ~l_b  |   X   | coeff_a | coeff_b | coeff_a_rot | coeff_a_rot | <- q_lookup
        | t_c |  l_c  | ~l_c  | t_d |  l_d  | ~l_d  | Rot(X)| coeff_c | coeff_d | coeff_a_rot | coeff_a_rot | <- q_lookup, q_left_rot

        with constraints of:

        1) applying the plain-spreaded lookup on limbs:
            (t_a, l_a, ~l_a), (t_b, l_b, ~l_b),
            (t_c, l_c, ~l_c), (t_d, l_d, ~l_d),
           to guarantee the limb values l_i are in the range [0, 2^t_i), the spreaded
           limb values ~l_i have to be filled as well although they are not used in the constraint

         2) asserting the decomposition identity of A:
               coeff_a * l_a + coeff_b * l_b + coeff_c * l_c + coeff_d * l_d
             = X

         3) asserting the decomposition identity of Rot(X):
               coeff_a_rot * l_a + coeff_b_rot * l_b + coeff_c_rot * l_c + coeff_d_rot * l_d
             = Rot(X)
        */
        let word_val = word.0.value().map(|&w| fe_to_u32(w));
        let rot_val = word_val.map(|w| w.rotate_left(rot as u32)).map(u32_to_fe);

        layouter.assign_region(
            || "Assign left rotation",
            |mut region| {
                self.config().q_lookup.enable(&mut region, 0)?;
                self.config().q_lookup.enable(&mut region, 1)?;
                self.config().q_left_rot.enable(&mut region, 1)?;

                word.0
                    .copy_advice(|| "Word", &mut region, self.config().advice_cols[4], 0)
                    .map(AssignedWord)?;
                let rotated_word = region
                    .assign_advice(
                        || "Rotated word",
                        self.config().advice_cols[4],
                        1,
                        || rot_val,
                    )
                    .map(AssignedWord)?;

                self.assign_left_rotation(&mut region, word_val, rot, 0)?;

                Ok(rotated_word)
            },
        )
    }

    /// Given a list of up to four assigned words, this function computes their
    /// addition modulo 2^32, returning the result as an assigned word.
    fn add_mod_2_32(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[&AssignedWord<F>],
        zero: &AssignedWord<F>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        Computing the mod 2^32 addition: A ⊞ B ⊞ C ⊞ D fills the circuit layout as follows:

        |  T0 |   A0  |   A1   |  T1 |   A2  |  A3  | A4 | A5 | A6 | A7 |
        |-----|-------|--------|-----|-------|------|----|----|----|----|
        |     | carry |        |     |       | res  | A  |  B |  C |  D | <- q_mod_add

        with constraints of:

        1) asserting the mod 2^32 addition identity:
               A + B + C + D = carry * 2^32 + res

        2) range check of `carry` in [0, 3] to make sure the above identity
        not wrap-around, although it is not tight when number of summands < 4:
               carry * (carry - 1) * (carry - 2) * (carry - 3) = 0
        */
        assert!(summands.len() <= 4, "At most 4 summands are supported");

        let adv_cols = self.config().advice_cols;

        let mut summands = summands.to_vec();
        summands.resize(4, zero);

        let (carry_val, res_val): (Value<u32>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u64).sum::<u64>())
                .map(|s| s.div_rem(&(1u64 << 32)))
                .map(|(carry, rem)| (carry as u32, u64_to_fe(rem)))
                .unzip();
        let carry_val: Value<F> = carry_val.map(u32_to_fe);

        layouter.assign_region(
            || "Assign add_mod_2_32",
            |mut region| {
                self.config().q_mod_add.enable(&mut region, 0)?;

                summands[0].0.copy_advice(|| "S0", &mut region, adv_cols[4], 0)?;
                summands[1].0.copy_advice(|| "S1", &mut region, adv_cols[5], 0)?;
                summands[2].0.copy_advice(|| "S2", &mut region, adv_cols[6], 0)?;
                summands[3].0.copy_advice(|| "S3", &mut region, adv_cols[7], 0)?;
                region.assign_advice(|| "carry", adv_cols[0], 0, || carry_val)?;
                region.assign_advice(|| "res", adv_cols[3], 0, || res_val).map(AssignedWord)
            },
        )
    }

    /// Given a u64 value representing a spreaded value, this function
    /// decomposes it into 11-11-10 limbs for both its even and odd bits,
    /// depending on `even_or_odd` it assigns them in the circuit, and returns
    /// the assigned word corresponding to either the even or odd part.
    fn assign_sprdd_11_11_10(
        &self,
        region: &mut Region<'_, F>,
        value: Value<u64>,
        even_or_odd: Parity,
        offset: usize,
    ) -> Result<AssignedWord<F>, Error> {
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
        .map(AssignedWord)
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
    ) -> Result<(), Error> {
        self.config().q_lookup.enable(region, offset)?;

        let nbits_col = self.config().fixed_cols[lookup_idx]; // 0 or 1
        let plain_col = self.config().advice_cols[2 * lookup_idx]; // 0 or 2
        let sprdd_col = self.config().advice_cols[2 * lookup_idx + 1]; // 1 or 3

        let nbits_val = Value::known(F::from(L as u64));
        let sprdd_val: Value<F> = plain_val.map(spread).map(u64_to_fe);
        let plain_val: Value<F> = plain_val.map(u32_to_fe);

        region.assign_fixed(|| "nbits", nbits_col, offset, || nbits_val)?;
        region.assign_advice(|| "plain", plain_col, offset, || plain_val)?;
        region.assign_advice(|| "sprdd", sprdd_col, offset, || sprdd_val)?;

        Ok(())
    }

    /// Given a u32 value representing a word and the rotation amount, computes
    /// and assigns its limb values, coefficients and rotated coefficients
    /// in the circuit.
    fn assign_left_rotation(
        // Note that the limb lengths are not known at compile time, so const generics are
        // not applicable and then we cannot use `assign_plain_and_spreaded`.
        &self,
        region: &mut Region<'_, F>,
        value: Value<u32>,
        rot: u8,
        offset: usize,
    ) -> Result<(), Error> {
        let limb_values: [Value<u32>; 4] = value.map(|v| limb_values(v, rot)).transpose_array();
        let sprdd_values: [Value<F>; 4] =
            limb_values.map(|limb| limb.map(spread)).map(|val| val.map(u64_to_fe));
        let limb_values: [Value<F>; 4] = limb_values.map(|limb| limb.map(u32_to_fe));

        let (coeffs, coeffs_rot) = limb_coeffs(rot);
        let coeffs: [Value<F>; 4] = coeffs.map(u32_to_fe).map(Value::known);
        let coeffs_rot: [Value<F>; 4] = coeffs_rot.map(u32_to_fe).map(Value::known);

        let (limb_lengths, _) = limb_lengths(rot);
        let limb_lengths: [Value<F>; 4] = limb_lengths.map(|l| F::from(l as u64)).map(Value::known);

        let adv_cols = self.config().advice_cols;
        let fixed_cols = self.config().fixed_cols;

        region.assign_fixed(|| "tag a", fixed_cols[0], offset, || limb_lengths[0])?;
        region.assign_advice(|| "limb a", adv_cols[0], offset, || limb_values[0])?;
        region.assign_advice(|| "~ limb a", adv_cols[1], offset, || sprdd_values[0])?;

        region.assign_fixed(|| "tag b", fixed_cols[1], offset, || limb_lengths[1])?;
        region.assign_advice(|| "limb b", adv_cols[2], offset, || limb_values[1])?;
        region.assign_advice(|| "~ limb b", adv_cols[3], offset, || sprdd_values[1])?;

        region.assign_fixed(|| "tag c", fixed_cols[0], offset + 1, || limb_lengths[2])?;
        region.assign_advice(|| "limb c", adv_cols[0], offset + 1, || limb_values[2])?;
        region.assign_advice(|| "~ limb c", adv_cols[1], offset + 1, || sprdd_values[2])?;

        region.assign_fixed(|| "tag d", fixed_cols[1], offset + 1, || limb_lengths[3])?;
        region.assign_advice(|| "limb d", adv_cols[2], offset + 1, || limb_values[3])?;
        region.assign_advice(|| "~ limb d", adv_cols[3], offset + 1, || sprdd_values[3])?;

        region.assign_fixed(|| "coeff a", fixed_cols[2], offset, || coeffs[0])?;
        region.assign_fixed(|| "coeff b", fixed_cols[3], offset, || coeffs[1])?;
        region.assign_fixed(|| "coeff c", fixed_cols[2], offset + 1, || coeffs[2])?;
        region.assign_fixed(|| "coeff d", fixed_cols[3], offset + 1, || coeffs[3])?;

        region.assign_fixed(|| "rot coeff a", fixed_cols[4], offset, || coeffs_rot[0])?;
        region.assign_fixed(|| "rot coeff b", fixed_cols[5], offset, || coeffs_rot[1])?;
        region.assign_fixed(
            || "rot coeff c",
            fixed_cols[4],
            offset + 1,
            || coeffs_rot[2],
        )?;
        region.assign_fixed(
            || "rot coeff d",
            fixed_cols[5],
            offset + 1,
            || coeffs_rot[3],
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::max;

    use midnight_curves::Fq as F;
    use midnight_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};

    use super::*;
    use crate::{
        field::{
            decomposition::{chip::P2RDecompositionConfig, pow2range::Pow2RangeChip},
            native::{NB_ARITH_COLS, NB_ARITH_FIXED_COLS},
            AssignedNative,
        },
        instructions::AssignmentInstructions,
        testing_utils::FromScratch,
    };

    struct TestCircuit<F: PrimeField> {
        inputs: [F; 5],
        input_bytes: Vec<u8>,
        output_words: [u32; 5],
        input_bytes_long: Vec<u8>,
        output_words_long: [u32; 5],
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
        type Config = (RipeMD160Config, P2RDecompositionConfig);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            unreachable!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice_columns = (0..max(NB_ARITH_COLS, NB_RIPEMD160_ADVICE_COLS))
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>();

            let fixed_columns = (0..max(NB_ARITH_FIXED_COLS, NB_RIPEMD160_FIXED_COLS))
                .map(|_| meta.fixed_column())
                .collect::<Vec<_>>();

            let instance_columns = [meta.instance_column(); 2];

            let native_config = NativeChip::configure(
                meta,
                &(
                    advice_columns[..NB_ARITH_COLS].try_into().unwrap(),
                    fixed_columns[..NB_ARITH_FIXED_COLS].try_into().unwrap(),
                    instance_columns,
                ),
            );

            let pow2range_config = Pow2RangeChip::configure(meta, &advice_columns[1..=4]);
            let core_decomposition_config =
                P2RDecompositionChip::configure(meta, &(native_config, pow2range_config));

            let ripemd160_config = RipeMD160Chip::configure(
                meta,
                &(
                    advice_columns[..NB_RIPEMD160_ADVICE_COLS].try_into().unwrap(),
                    fixed_columns[..NB_RIPEMD160_FIXED_COLS].try_into().unwrap(),
                ),
            );

            (ripemd160_config, core_decomposition_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let native_gadget = NativeGadget::new_from_scratch(&config.1);
            let ripemd160_chip = RipeMD160Chip::new(&config.0, &native_gadget);

            native_gadget.load_from_scratch(&mut layouter)?;
            ripemd160_chip.load(&mut layouter)?;

            let assigned_inputs: Vec<AssignedNative<F>> =
                ripemd160_chip.native_gadget.assign_many_fixed(&mut layouter, &self.inputs)?;

            let assigned_words: Vec<AssignedWord<F>> =
                assigned_inputs.into_iter().map(AssignedWord).collect();

            let assigned_sprdd_words: Vec<AssignedSpreaded<F, 32>> = assigned_words
                .iter()
                .map(|word| ripemd160_chip.prepare_spreaded(&mut layouter, word))
                .collect::<Result<Vec<_>, _>>()?;

            let [sprdd_a, sprdd_b, sprdd_c, sprdd_d, sprdd_e]: [AssignedSpreaded<F, 32>; 5] =
                assigned_sprdd_words.try_into().unwrap();

            let assigned_and = ripemd160_chip.and(&mut layouter, &sprdd_d, &sprdd_e)?;
            let expected_and = fe_to_u32(self.inputs[3]) & fe_to_u32(self.inputs[4]);
            assigned_and.0.value().assert_if_known(|res| **res == u32_to_fe(expected_and));

            let assigned_xor = ripemd160_chip.xor(&mut layouter, &sprdd_d, &sprdd_e)?;
            let expected_xor = fe_to_u32(self.inputs[3]) ^ fe_to_u32(self.inputs[4]);
            assigned_xor.0.value().assert_if_known(|res| **res == u32_to_fe(expected_xor));

            let assigned_rot = ripemd160_chip.left_rotate(&mut layouter, &assigned_words[3], 5)?;
            let expected_rot = fe_to_u32(self.inputs[3]).rotate_left(5);
            assigned_rot.0.value().assert_if_known(|res| **res == u32_to_fe(expected_rot));

            let assigned_add_mod = ripemd160_chip.add_mod_2_32(
                &mut layouter,
                &[&assigned_words[1], &assigned_words[2], &assigned_words[3]],
                &assigned_words[0], // intialized to zero in the test function
            )?;
            let expected_add_mod =
                (fe_to_u64(self.inputs[1]) + fe_to_u64(self.inputs[2]) + fe_to_u64(self.inputs[3]))
                    % (1u64 << 32);
            assigned_add_mod
                .0
                .value()
                .assert_if_known(|res| **res == u32_to_fe(expected_add_mod as u32));

            let res1 = ripemd160_chip.f_type_one(&mut layouter, &sprdd_a, &sprdd_b, &sprdd_c)?;
            let expected_res1 =
                fe_to_u32(self.inputs[0]) ^ fe_to_u32(self.inputs[1]) ^ fe_to_u32(self.inputs[2]);
            res1.0.value().assert_if_known(|res| **res == u32_to_fe(expected_res1));

            let res2 = ripemd160_chip.f_type_two(&mut layouter, &sprdd_b, &sprdd_c, &sprdd_d)?;
            let expected_res2 = (fe_to_u32(self.inputs[1]) & fe_to_u32(self.inputs[2]))
                | (!fe_to_u32(self.inputs[1]) & fe_to_u32(self.inputs[3]));
            res2.0.value().assert_if_known(|res| **res == u32_to_fe(expected_res2));

            let res3 = ripemd160_chip.f_type_three(&mut layouter, &sprdd_c, &sprdd_d, &sprdd_e)?;
            let expected_res3 = (fe_to_u32(self.inputs[2]) | !fe_to_u32(self.inputs[3]))
                ^ fe_to_u32(self.inputs[4]);
            res3.0.value().assert_if_known(|res| **res == u32_to_fe(expected_res3));

            let assigned_input_bytes: Vec<AssignedByte<F>> = self
                .input_bytes
                .iter()
                .map(|b| ripemd160_chip.native_gadget.assign_fixed(&mut layouter, *b))
                .collect::<Result<Vec<_>, _>>()?;

            let assigned_output: [F; 5] = self
                .output_words
                .iter()
                .map(|w| u32_to_fe(*w))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            let ripemd160_output =
                ripemd160_chip.ripemd160(&mut layouter, &assigned_input_bytes)?;

            let State { h0, h1, h2, h3, h4 } = ripemd160_output;
            let ripemd160_output = [h0, h1, h2, h3, h4];
            for (computed, expected) in ripemd160_output.iter().zip(assigned_output.iter()) {
                print!(
                    "Computed: {:?}, Expected: {:?}\n",
                    computed.0.value(),
                    expected
                );
                computed.0.value().assert_if_known(|res| **res == *expected);
            }

            let assigned_input_bytes_long: Vec<AssignedByte<F>> = self
                .input_bytes_long
                .iter()
                .map(|b| ripemd160_chip.native_gadget.assign_fixed(&mut layouter, *b))
                .collect::<Result<Vec<_>, _>>()?;

            let assigned_output_long: [F; 5] = self
                .output_words_long
                .iter()
                .map(|w| u32_to_fe(*w))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            let ripemd160_output_long =
                ripemd160_chip.ripemd160(&mut layouter, &assigned_input_bytes_long)?;

            let State { h0, h1, h2, h3, h4 } = ripemd160_output_long;
            let ripemd160_output_long = [h0, h1, h2, h3, h4];
            for (computed, expected) in
                ripemd160_output_long.iter().zip(assigned_output_long.iter())
            {
                print!(
                    "Computed: {:?}, Expected: {:?}\n",
                    computed.0.value(),
                    expected
                );
                computed.0.value().assert_if_known(|res| **res == *expected);
            }

            Ok(())
        }
    }

    #[test]
    fn test_circuit() {
        let circuit = TestCircuit {
            inputs: [
                F::from(0u64),
                F::from(1u64),
                F::from(42u64),
                F::from(255u64),
                F::from(1023u64),
            ],
            input_bytes: vec![97, 98, 99],
            output_words: [0xf708b28e, 0x7a985de0, 0x8e4a049b, 0x87b0c698, 0xfc0b5af1],

            input_bytes_long: vec![49; 64],
            output_words_long: [0x4d03b0b2, 0x858dc891, 0x64715c7e, 0x29436308, 0xe89b0d1c],
        };

        let prover = match MockProver::<F>::run(16, &circuit, vec![vec![]]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
