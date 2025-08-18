use ff::PrimeField;
#[cfg(any(test, feature = "testing"))]
use midnight_proofs::plonk::Instance;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use num_integer::Integer;

#[cfg(any(test, feature = "testing"))]
use crate::testing_utils::FromScratch;
use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    hash::new_sha256::{
        gates::{
            add_mod_2_32_gate, decompose_10_9_11_2_gate, decompose_12_12_8_gate,
            decompose_12_1_1_1_7_3_4_3_gate, decompose_7_12_2_5_6_gate, half_ch_gate, maj_gate,
            sigma_0_gate, sigma_1_gate, Sigma_0_gate, Sigma_1_gate,
        },
        types::{
            AssignedMessageWord, AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded,
            CompressionState, LimbsOfA, LimbsOfE,
        },
        utils::{
            gen_spread_table, get_even_and_odd_bits, negate_spreaded, spread, spreaded_Sigma_0,
            spreaded_Sigma_1, spreaded_maj, spreaded_sigma_0, spreaded_sigma_1, u32_in_be_limbs,
            u32_to_fe, u64_to_fe, MASK_EVN_64,
        },
    },
    instructions::{assignments::AssignmentInstructions, DecompositionInstructions},
    types::{AssignedByte, AssignedNative},
    utils::{
        util::{fe_to_u32, fe_to_u64},
        ComposableChip,
    },
};

const ROUND_CONSTANTS: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Number of advice columns used by the identities of the SHA256 chip.
pub const NB_SHA256_ADVICE_COLS: usize = 8;

/// Number of fixed columns used by the identities of the SHA256 chip.
pub const NB_SHA256_FIXED_COLS: usize = 2;

/// Tag for the even and odd 12-12-8 decompositions.
enum Parity {
    Evn,
    Odd,
}

/// Plain-Spreaded lookup table.
#[derive(Clone, Debug)]
struct SpreadTable {
    nbits_tab: TableColumn,
    plain_tab: TableColumn,
    sprdd_tab: TableColumn,
}

/// Configuration of Sha256Chip.
#[derive(Clone, Debug)]
pub struct Sha256Config {
    advice_cols: [Column<Advice>; NB_SHA256_ADVICE_COLS],
    fixed_cols: [Column<Fixed>; NB_SHA256_FIXED_COLS],
    q_Sigma_0: Selector,
    q_Sigma_1: Selector,
    q_maj: Selector,
    q_half_ch: Selector,
    q_12_12_8: Selector,
    q_10_9_11_2: Selector,
    q_7_12_2_5_6: Selector,
    q_12_1_1_1_7_3_4_3: Selector,
    q_sigma_0: Selector,
    q_sigma_1: Selector,
    q_add_mod_2_32: Selector,
    q_lookup: Selector,
    table: SpreadTable,
}

/// Chip for SHA256
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
        let advice_cols = shared_res.0;
        let fixed_cols = shared_res.1;
        let nbits_tab = meta.lookup_table_column();
        let plain_tab = meta.lookup_table_column();
        let sprdd_tab = meta.lookup_table_column();

        advice_cols.iter().for_each(|c| meta.enable_equality(*c));

        let q_Sigma_0 = meta.selector();
        let q_Sigma_1 = meta.selector();
        let q_maj = meta.selector();
        let q_half_ch = meta.selector();
        let q_12_12_8 = meta.selector();
        let q_10_9_11_2 = meta.selector();
        let q_7_12_2_5_6 = meta.selector();
        let q_12_1_1_1_7_3_4_3 = meta.selector();
        let q_sigma_0 = meta.selector();
        let q_sigma_1 = meta.selector();
        let q_add_mod_2_32 = meta.selector();
        let q_lookup = meta.complex_selector();

        (0..2).for_each(|idx| {
            meta.lookup("plain-spreaded lookup", |meta| {
                let q_lookup = meta.query_selector(q_lookup);

                let nbits = meta.query_fixed(fixed_cols[idx], Rotation(0));
                let plain = meta.query_advice(advice_cols[2 * idx], Rotation(0));
                let sprdd = meta.query_advice(advice_cols[2 * idx + 1], Rotation(0));

                vec![
                    (q_lookup.clone() * nbits, nbits_tab),
                    (q_lookup.clone() * plain, plain_tab),
                    (q_lookup * sprdd, sprdd_tab),
                ]
            });
        });

        meta.create_gate("Σ₀(A)", |meta| {
            let q_Sigma_0 = meta.query_selector(q_Sigma_0);

            let sprdd_a_10 = meta.query_advice(advice_cols[5], Rotation(0));
            let sprdd_a_09 = meta.query_advice(advice_cols[6], Rotation(0));
            let sprdd_a_11 = meta.query_advice(advice_cols[5], Rotation(1));
            let sprdd_a_02 = meta.query_advice(advice_cols[6], Rotation(1));
            let sprdd_evn_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_evn_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_evn_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let sprdd_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Constraints::with_selector(
                q_Sigma_0,
                Sigma_0_gate(
                    [sprdd_a_10, sprdd_a_09, sprdd_a_11, sprdd_a_02],
                    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                ),
            )
        });

        meta.create_gate("Σ₁(E)", |meta| {
            let q_Sigma_1 = meta.query_selector(q_Sigma_1);

            let sprdd_e_07 = meta.query_advice(advice_cols[5], Rotation(0));
            let sprdd_e_12 = meta.query_advice(advice_cols[6], Rotation(0));
            let sprdd_e_02 = meta.query_advice(advice_cols[5], Rotation(1));
            let sprdd_e_05 = meta.query_advice(advice_cols[6], Rotation(1));
            let sprdd_e_06 = meta.query_advice(advice_cols[5], Rotation(2));
            let sprdd_evn_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_evn_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_evn_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let sprdd_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Constraints::with_selector(
                q_Sigma_1,
                Sigma_1_gate(
                    [sprdd_e_07, sprdd_e_12, sprdd_e_02, sprdd_e_05, sprdd_e_06],
                    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                ),
            )
        });

        meta.create_gate("Maj(A, B, C)", |meta| {
            let q_maj = meta.query_selector(q_maj);

            let sprdd_a = meta.query_advice(advice_cols[5], Rotation(0));
            let sprdd_b = meta.query_advice(advice_cols[6], Rotation(0));
            let sprdd_c = meta.query_advice(advice_cols[5], Rotation(1));
            let sprdd_odd_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_odd_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_odd_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let sprdd_evn_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_evn_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_evn_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Constraints::with_selector(
                q_maj,
                maj_gate(
                    [sprdd_a, sprdd_b, sprdd_c],
                    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                ),
            )
        });

        meta.create_gate("half Ch(E, F, G)", |meta| {
            let q_half_ch = meta.query_selector(q_half_ch);

            let sprdd_x = meta.query_advice(advice_cols[5], Rotation(0));
            let sprdd_y = meta.query_advice(advice_cols[6], Rotation(0));
            let sprdd_odd_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_odd_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_odd_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let sprdd_evn_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_evn_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_evn_8 = meta.query_advice(advice_cols[3], Rotation(2));
            let summand_1 = meta.query_advice(advice_cols[4], Rotation(1));
            let summand_2 = meta.query_advice(advice_cols[5], Rotation(1));
            let sum = meta.query_advice(advice_cols[6], Rotation(1));

            Constraints::with_selector(
                q_half_ch,
                half_ch_gate(
                    [sprdd_x, sprdd_y],
                    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                    [summand_1, summand_2, sum],
                ),
            )
        });

        meta.create_gate("12-12-8 decomposition", |meta| {
            let q_12_12_8 = meta.query_selector(q_12_12_8);

            let limb_12a = meta.query_advice(advice_cols[0], Rotation(0));
            let limb_12b = meta.query_advice(advice_cols[0], Rotation(1));
            let limb_8 = meta.query_advice(advice_cols[0], Rotation(2));
            let output = meta.query_advice(advice_cols[4], Rotation(0));

            Constraints::with_selector(
                q_12_12_8,
                decompose_12_12_8_gate([limb_12a, limb_12b, limb_8], output),
            )
        });

        meta.create_gate("10-9-11-2 decomposition", |meta| {
            let q_10_9_11_2 = meta.query_selector(q_10_9_11_2);

            let limb_10 = meta.query_advice(advice_cols[0], Rotation(0));
            let limb_09 = meta.query_advice(advice_cols[2], Rotation(0));
            let limb_11 = meta.query_advice(advice_cols[0], Rotation(1));
            let limb_02 = meta.query_advice(advice_cols[2], Rotation(1));
            let sprdd_limb_10 = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_limb_09 = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_limb_11 = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_limb_02 = meta.query_advice(advice_cols[3], Rotation(1));
            let plain = meta.query_advice(advice_cols[4], Rotation(0));
            let sprdd = meta.query_advice(advice_cols[4], Rotation(1));

            Constraints::with_selector(
                q_10_9_11_2,
                decompose_10_9_11_2_gate(
                    [limb_10, limb_09, limb_11, limb_02],
                    [sprdd_limb_10, sprdd_limb_09, sprdd_limb_11, sprdd_limb_02],
                    (plain, sprdd),
                ),
            )
        });

        meta.create_gate("7-12-2-5-6 decomposition", |meta| {
            let q_7_12_2_5_6 = meta.query_selector(q_7_12_2_5_6);

            let limb_07 = meta.query_advice(advice_cols[0], Rotation(0));
            let limb_12 = meta.query_advice(advice_cols[2], Rotation(0));
            let limb_02 = meta.query_advice(advice_cols[0], Rotation(1));
            let limb_05 = meta.query_advice(advice_cols[2], Rotation(1));
            let limb_06 = meta.query_advice(advice_cols[0], Rotation(2));
            let sprdd_limb_07 = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_limb_12 = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_limb_02 = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_limb_05 = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_limb_06 = meta.query_advice(advice_cols[1], Rotation(2));
            let plain = meta.query_advice(advice_cols[4], Rotation(0));
            let sprdd = meta.query_advice(advice_cols[4], Rotation(1));

            Constraints::with_selector(
                q_7_12_2_5_6,
                decompose_7_12_2_5_6_gate(
                    [limb_07, limb_12, limb_02, limb_05, limb_06],
                    [
                        sprdd_limb_07,
                        sprdd_limb_12,
                        sprdd_limb_02,
                        sprdd_limb_05,
                        sprdd_limb_06,
                    ],
                    (plain, sprdd),
                ),
            )
        });

        meta.create_gate("add mod 2^32", |meta| {
            let q_add_mod_2_32 = meta.query_selector(q_add_mod_2_32);

            let s0 = meta.query_advice(advice_cols[5], Rotation(0));
            let s1 = meta.query_advice(advice_cols[6], Rotation(0));
            let s2 = meta.query_advice(advice_cols[5], Rotation(1));
            let s3 = meta.query_advice(advice_cols[6], Rotation(1));
            let s4 = meta.query_advice(advice_cols[4], Rotation(2));
            let s5 = meta.query_advice(advice_cols[5], Rotation(2));
            let s6 = meta.query_advice(advice_cols[6], Rotation(2));

            let carry = meta.query_advice(advice_cols[2], Rotation(2));
            let result = meta.query_advice(advice_cols[4], Rotation(0));

            Constraints::with_selector(
                q_add_mod_2_32,
                add_mod_2_32_gate(&[s0, s1, s2, s3, s4, s5, s6], carry, result),
            )
        });

        meta.create_gate("12-1-1-1-7-3-4-3 decomposition", |meta| {
            let q_12_1_1_1_7_3_4_3 = meta.query_selector(q_12_1_1_1_7_3_4_3);

            let w_12 = meta.query_advice(advice_cols[0], Rotation(0));
            let w_07 = meta.query_advice(advice_cols[2], Rotation(0));
            let w_3a = meta.query_advice(advice_cols[0], Rotation(1));
            let w_04 = meta.query_advice(advice_cols[2], Rotation(1));
            let w_3b = meta.query_advice(advice_cols[0], Rotation(2));
            let w_1a = meta.query_advice(advice_cols[7], Rotation(0));
            let w_1b = meta.query_advice(advice_cols[7], Rotation(1));
            let w_1c = meta.query_advice(advice_cols[7], Rotation(2));
            let w_plain = meta.query_advice(advice_cols[4], Rotation(0));

            Constraints::with_selector(
                q_12_1_1_1_7_3_4_3,
                decompose_12_1_1_1_7_3_4_3_gate(
                    [w_12, w_1a, w_1b, w_1c, w_07, w_3a, w_04, w_3b],
                    w_plain,
                ),
            )
        });

        meta.create_gate("σ₀(W)", |meta| {
            let q_sigma_0 = meta.query_selector(q_sigma_0);

            let sprdd_w_12 = meta.query_advice(advice_cols[5], Rotation(0));
            let sprdd_w_1a = meta.query_advice(advice_cols[6], Rotation(0));
            let sprdd_w_1b = meta.query_advice(advice_cols[4], Rotation(1));
            let sprdd_w_1c = meta.query_advice(advice_cols[5], Rotation(1));
            let sprdd_w_07 = meta.query_advice(advice_cols[6], Rotation(1));
            let sprdd_w_3a = meta.query_advice(advice_cols[4], Rotation(2));
            let sprdd_w_04 = meta.query_advice(advice_cols[5], Rotation(2));
            let sprdd_w_3b = meta.query_advice(advice_cols[6], Rotation(2));
            let sprdd_evn_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_evn_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_evn_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let sprdd_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Constraints::with_selector(
                q_sigma_0,
                sigma_0_gate(
                    [
                        sprdd_w_12, sprdd_w_1a, sprdd_w_1b, sprdd_w_1c, sprdd_w_07, sprdd_w_3a,
                        sprdd_w_04, sprdd_w_3b,
                    ],
                    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                ),
            )
        });

        meta.create_gate("σ₁(W)", |meta| {
            let q_sigma_1 = meta.query_selector(q_sigma_1);

            let sprdd_w_12 = meta.query_advice(advice_cols[5], Rotation(0));
            let sprdd_w_1a = meta.query_advice(advice_cols[6], Rotation(0));
            let sprdd_w_1b = meta.query_advice(advice_cols[4], Rotation(1));
            let sprdd_w_1c = meta.query_advice(advice_cols[5], Rotation(1));
            let sprdd_w_07 = meta.query_advice(advice_cols[6], Rotation(1));
            let sprdd_w_3a = meta.query_advice(advice_cols[4], Rotation(2));
            let sprdd_w_04 = meta.query_advice(advice_cols[5], Rotation(2));
            let sprdd_w_3b = meta.query_advice(advice_cols[6], Rotation(2));
            let sprdd_evn_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let sprdd_evn_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let sprdd_evn_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let sprdd_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let sprdd_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let sprdd_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Constraints::with_selector(
                q_sigma_1,
                sigma_1_gate(
                    [
                        sprdd_w_12, sprdd_w_1a, sprdd_w_1b, sprdd_w_1c, sprdd_w_07, sprdd_w_3a,
                        sprdd_w_04, sprdd_w_3b,
                    ],
                    [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                    [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                ),
            )
        });

        Sha256Config {
            advice_cols,
            fixed_cols,
            q_Sigma_0,
            q_Sigma_1,
            q_maj,
            q_half_ch,
            q_12_12_8,
            q_10_9_11_2,
            q_7_12_2_5_6,
            q_12_1_1_1_7_3_4_3,
            q_sigma_0,
            q_sigma_1,
            q_add_mod_2_32,
            q_lookup,
            table: SpreadTable {
                nbits_tab,
                plain_tab,
                sprdd_tab,
            },
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let SpreadTable {
            nbits_tab,
            plain_tab,
            sprdd_tab,
        } = self.config().table;

        layouter.assign_table(
            || "spread table",
            |mut table| {
                for (index, triple) in gen_spread_table::<F>().enumerate() {
                    table.assign_cell(|| "nbits", nbits_tab, index, || Value::known(triple.0))?;
                    table.assign_cell(|| "plain", plain_tab, index, || Value::known(triple.1))?;
                    table.assign_cell(|| "sprdd", sprdd_tab, index, || Value::known(triple.2))?;
                }
                Ok(())
            },
        )
    }
}

impl<F: PrimeField> Sha256Chip<F> {
    /// Computes Σ₀(A).
    fn Sigma_0(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &LimbsOfA<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We need to compute:
             A >>> 2 :  ( A.02 || A.10 || A.09 || A.11 )
          ⊕ A >>> 13 :  ( A.11 || A.02 || A.10 || A.09 )
          ⊕ A >>> 22 :  ( A.09 || A.11 || A.02 || A.10 )

        which can be achieved by

        1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Evn:
              2^20 * Evn.12a + 2^8 * Evn.12b + Evn.8
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8) +
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             = 4^30 * ~A.02 + 4^20 * ~A.10 + 4^11 * ~A.09 + ~A.11
             + 4^21 * ~A.11 + 4^19 * ~A.02 + 4^9  * ~A.10 + ~A.09
             + 4^23 * ~A.09 + 4^12 * ~A.11 + 4^10 * ~A.02 + ~A.10

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T_0 |    A_0  |    A_1   | T_1 |   A_2   |    A_3   |  A_4  |  A_5  |  A_6  |
        |-----|---------|----------|-----|---------|----------|-------|-------|-------|
        |  12 | Evn.12a | ~Evn.12a |  12 | Odd.12a | ~Odd.12a |  Evn  | ~A.10 | ~A.09 |
        |  12 | Evn.12b | ~Evn.12b |  12 | Odd.12b | ~Odd.12b |       | ~A.11 | ~A.02 |
        |   8 |   Evn.8 |   ~Evn.8 |   8 |   Odd.8 |   ~Odd.8 |       |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₀(A)",
            |mut region| {
                self.config().q_Sigma_0.enable(&mut region, 0)?;

                // Copy and assign the input.
                (a.spreaded_limb_10.0).copy_advice(|| "~A.10", &mut region, adv_cols[5], 0)?;
                (a.spreaded_limb_09.0).copy_advice(|| "~A.09", &mut region, adv_cols[6], 0)?;
                (a.spreaded_limb_11.0).copy_advice(|| "~A.11", &mut region, adv_cols[5], 1)?;
                (a.spreaded_limb_02.0).copy_advice(|| "~A.02", &mut region, adv_cols[6], 1)?;

                // Compute the spreaded Σ₀(A) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the q_12_12_8 selector
                // for the even part and q_lookup selector for the related rows, return the
                // assigned 32 even bits.
                let val_of_sprdd_limbs: Value<[u64; 4]> = Value::from_iter([
                    a.spreaded_limb_10.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_09.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_11.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_02.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                self.assign_sprdd_12_12_8(
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
        We need to compute:
             E >>> 6 :  ( E.06 || E.07 || E.12 || E.02 || E.05 )
          ⊕ E >>> 11 :  ( E.05 || E.06 || E.07 || E.12 || E.02 )
          ⊕ E >>> 25 :  ( E.12 || E.02 || E.05 || E.06 || E.07 )

        which can be achieved by

        1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Evn:
              2^20 * Evn.12a + 2^8 * Evn.12b + Evn.8
            = Evn

         3) asserting the Sigma_1 identity regarding the spreaded values:
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8) +
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             = 4^26 * ~E.06 + 4^19 * ~E.07 + 4^7  * ~E.12 + 4^5 * ~E.02 + ~E.05
             + 4^27 * ~E.05 + 4^21 * ~E.06 + 4^14 * ~E.07 + 4^2 * ~E.12 + ~E.02
             + 4^20 * ~E.12 + 4^18 * ~E.02 + 4^13 * ~E.05 + 4^7 * ~E.06 + ~E.07

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T_0 |   A_0   |    A_1   | T_1 |   A_2   |    A_3   | A_4 |  A_5  |  A_6  |
        |-----|---------|----------|-----|---------|----------|-----|-------|-------|
        |  12 | Evn.12a | ~Evn.12a |  12 | Odd.12a | ~Odd.12a | Evn | ~E.07 | ~E.12 |
        |  12 | Evn.12b | ~Evn.12b |  12 | Odd.12b | ~Odd.12b |     | ~E.02 | ~E.05 |
        |   8 |   Evn.8 |   ~Evn.8 |   8 |   Odd.8 |   ~Odd.8 |     | ~E.06 |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₁(E)",
            |mut region| {
                self.config().q_Sigma_1.enable(&mut region, 0)?;

                // Copy and assign the input.
                (e.spreaded_limb_07.0).copy_advice(|| "~E.07", &mut region, adv_cols[5], 0)?;
                (e.spreaded_limb_12.0).copy_advice(|| "~E.12", &mut region, adv_cols[6], 0)?;
                (e.spreaded_limb_02.0).copy_advice(|| "~E.02", &mut region, adv_cols[5], 1)?;
                (e.spreaded_limb_05.0).copy_advice(|| "~E.05", &mut region, adv_cols[6], 1)?;
                (e.spreaded_limb_06.0).copy_advice(|| "~E.06", &mut region, adv_cols[5], 2)?;

                // Compute the spreaded Σ₁(E) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the q_12_12_8 selector
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

                self.assign_sprdd_12_12_8(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_Sigma_1),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Computes Maj(A, B, C)
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

        which can be achieved by

        1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Odd:
              2^20 * Odd.12a + 2^8 * Odd.12b + Odd.8
            = Odd

        3) asserting the major identity regarding the spreaded values:
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8)
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             = ~A + ~B + ~C

        The output is Odd.

        We distribute these values in the PLONK table as follows.

        | T_0 |   A_0   |    A_1   | T_1 |   A_2   |    A_3   |  A_4  |  A_5  |  A_6  |
        |-----|---------|----------|-----|---------|----------|-------|-------|-------|
        |  12 | Odd.12a | ~Odd.12a |  12 | Evn.12a | ~Evn.12a |  Odd  |  ~A   |  ~B   |
        |  12 | Odd.12b | ~Odd.12b |  12 | Evn.12b | ~Evn.12b |       |  ~C   |       |
        |   8 | Odd.8   | ~Odd.8   |   8 | Evn.2   | ~Evn.8   |       |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Maj(A, B, C)",
            |mut region| {
                self.config().q_maj.enable(&mut region, 0)?;

                // Copy and assign the input.
                (sprdd_a.0).copy_advice(|| "~A", &mut region, adv_cols[5], 0)?;
                (sprdd_b.0).copy_advice(|| "~B", &mut region, adv_cols[6], 0)?;
                (sprdd_c.0).copy_advice(|| "~C", &mut region, adv_cols[5], 1)?;

                // Compute the spreaded Maj(A, B, C) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the q_12_12_8 selector
                // for the odd part and q_lookup selector for the related rows, return the
                // assigned 32 odd bits.
                let val_of_sprdd_forms: Value<[u64; 3]> = Value::from_iter([
                    sprdd_a.0.value().copied().map(fe_to_u64),
                    sprdd_b.0.value().copied().map(fe_to_u64),
                    sprdd_c.0.value().copied().map(fe_to_u64),
                ])
                .map(|sprdd_forms: Vec<u64>| sprdd_forms.try_into().unwrap());

                self.assign_sprdd_12_12_8(
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

        1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd,
           for both (~E + ~F) and (~(¬E) + ~G):
             Evn_EF: (Evn_EF.12a, Evn_EF.12b, Evn_EF.8)
             Odd_EF: (Odd_EF.12a, Odd_EF.12b, Odd_EF.8)

             Evn_nEG: (Evn_nEG.12a, Evn_nEG.12b, Evn_nEG.8)
             Odd_nEG: (Odd_nEG.12a, Odd_nEG.12b, Odd_nEG.8)

        2) asserting the 12-12-8 decomposition identity for Odd_EF and Odd_nEG:
              2^20 * Odd_EF.12a + 2^8 * Odd_EF.12b + Odd_EF.8
            = Odd_EF

              2^20 * Odd_nEG.12a + 2^8 * Odd_nEG.12b + Odd_nEG.8
            = Odd_nEG

        3) asserting the spreaded addition identity for (~E + ~F) and (~(¬E) + ~G):
              (4^20 * ~Evn_EF.12a + 4^8 * ~Evn_EF.12b + ~Evn_EF.8)
          2 * (4^20 * ~Odd_EF.12a + 4^8 * ~Odd_EF.12b + ~Odd_EF.8)
             = ~E + ~F

              (4^20 * ~Evn_nEG.12a + 4^8 * ~Evn_nEG.12b + ~Evn_nEG.8)
          2 * (4^20 * ~Odd_nEG.12a + 4^8 * ~Odd_nEG.12b + ~Odd_nEG.8)
             = ~(¬E) + ~G

        4) asserting the following two addition identities:
                    Ret = Odd_EF + Odd_nEG
            MASK_EVN_64 = ~E + ~(¬E)

        The output is Ret.

        We distribute these values in the PLONK table as follows.

        | T_0 |      A_0    |      A_1     | T_1 |      A_2    |      A_3     |   A_4   |   A_5   |     A_6     |
        |-----|-------------|--------------|-----|-------------|--------------|---------|---------|-------------|
        |  12 |  Odd_EF.12a |  ~Odd_EF.12a |  12 |  Evn_EF.12a |  ~Evn_EF.12a | Odd_EF  |   ~E    |      ~F     |
        |  12 |  Odd_EF.12b |  ~Odd_EF.12b |  12 |  Evn_EF.12b |  ~Evn_EF.12b | Odd_EF  | Odd_nEG |     Ret     |
        |   8 |  Odd_EF.8   |  ~Odd_EF.8   |   8 |  Evn_EF.8   |  ~Evn_EF.8   |         |         |             |
        |  12 | Odd_nEG.12a | ~Odd_nEG.12a |  12 | Evn_nEG.12a | ~Evn_nEG.12a | Odd_nEG |  ~(¬E)  |      ~G     |
        |  12 | Odd_nEG.12b | ~Odd_nEG.12b |  12 | Evn_nEG.12b | ~Evn_nEG.12b |   ~E    |  ~(¬E)  | MASK_EVN_64 |
        |   8 | Odd_nEG.8   | ~Odd_nEG.8   |   8 | Evn_nEG.2   | ~Evn_nEG.8   |         |         |             |
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
            (self.native_gadget).assign_fixed(layouter, F::from(MASK_EVN_64))?;

        layouter.assign_region(
            || "Ch(E, F, G)",
            |mut region| {
                self.config().q_half_ch.enable(&mut region, 0)?;
                self.config().q_half_ch.enable(&mut region, 3)?;

                (sprdd_E.0).copy_advice(|| "~E", &mut region, adv_cols[5], 0)?;
                (sprdd_E.0).copy_advice(|| "~E", &mut region, adv_cols[4], 4)?;

                (sprdd_F.0).copy_advice(|| "~F", &mut region, adv_cols[6], 0)?;
                (sprdd_G.0).copy_advice(|| "~G", &mut region, adv_cols[6], 3)?;

                let sprdd_nE = region.assign_advice(|| "~(¬E)", adv_cols[5], 3, || sprdd_nE_val)?;
                sprdd_nE.copy_advice(|| "~(¬E)", &mut region, adv_cols[5], 4)?;

                mask_evn_64.copy_advice(|| "MASK_EVN_64", &mut region, adv_cols[6], 4)?;

                let odd_EF = self.assign_sprdd_12_12_8(&mut region, EpF_val, Parity::Odd, 0)?;
                (odd_EF.0).copy_advice(|| "Odd_EF", &mut region, adv_cols[4], 1)?;

                let odd_nEG = self.assign_sprdd_12_12_8(&mut region, nEpG_val, Parity::Odd, 3)?;
                (odd_nEG.0).copy_advice(|| "Odd_nEG", &mut region, adv_cols[5], 1)?;

                let ret_val = odd_EF.0.value().copied() + odd_nEG.0.value().copied();
                region
                    .assign_advice(|| "Ret", adv_cols[6], 1, || ret_val)
                    .map(AssignedPlain::<F, 32>)
            },
        )
    }

    /// Given a slice of at most 7 `AssignedPlain` values, it adds them
    /// modulo 2^32 and decomposes the result (named A) into (bit-endian)
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

        | T_0 |  A_0 |  A_1  | T_1 |  A_2  |   A_3  | A_4 | A_5 | A_6 |
        |-----|------|-------|-----|-------|--------|-----|-----|-----|
        |  10 | A.10 | ~A.10 |  9  |  A.9  |  ~A.9  |   A |  S0 |  S1 |
        |  11 | A.11 | ~A.11 |  2  |  A.2  |  ~A.2  |  ~A |  S2 |  S3 |
        |   0 |   0  |   0   |  3  | carry | ~carry |  S4 |  S5 |  S6 |

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
                self.config().q_10_9_11_2.enable(&mut region, 0)?;

                let a_plain = self.assign_add_mod_2_32(&mut region, summands, &zero)?;
                let a_sprdd_val = (a_plain.0.value().copied())
                    .map(fe_to_u32)
                    .map(spread)
                    .map(u64_to_fe);
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
    /// modulo 2^32 and decomposes the result (named E) into (bit-endian)
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

        | T_0 |  A_0 |  A_1  | T_1 |   A_2   |   A_3  | A_4 | A_5 | A_6 |
        |-----|------|-------|-----|---------|--------|-----|-----|-----|
        |   7 | E.07 | ~E.07 |  12 |   E.12  |  ~E.12 |  E  |  S0 |  S1 |
        |   2 | E.02 | ~E.02 |   5 |   E.05  |  ~E.05 | ~E  |  S2 |  S3 |
        |   6 | E.06 | ~E.06 |   3 |  carry  | ~carry |  S4 |  S5 |  S6 |

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
                self.config().q_7_12_2_5_6.enable(&mut region, 0)?;

                let e_plain = self.assign_add_mod_2_32(&mut region, &summands, &zero)?;
                let e_sprdd_val = (e_plain.0.value().copied())
                    .map(fe_to_u32)
                    .map(spread)
                    .map(u64_to_fe);
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

    /// Given a plain u32 value, supposedly in the range [0, 2^L), assigns it
    /// in plain and spreaded form, returning an `AssignedPlainSpreaded<F, L>`.
    ///
    /// The assigned values are guaranteed to be well-formed and consistent
    /// via a lookup check at the specified offset.
    ///
    /// Note that we have two parallel lookup arguments. The caller must
    /// choose which of the two is used via the `lookup_idx`.
    /// If `lookup_idx = 0`, the lookup on columns (T_0, A_0, A_1) will be used.
    /// If `lookup_idx = 1`, the lookup on columns (T_1, A_2, A_3) will be used.
    ///
    /// # Unsatisfiable
    ///
    /// If the given value is not in the range [0, 2^L), the circuit will become
    /// unsatisfiable.
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

    /// Given a u64, representing an spreaded value, this function fills a
    /// lookup table with the limbs of its even and odd parts (or vice versa)
    /// and returns the former or the latter, depending on the desired value
    /// `even_or_odd`.
    ///
    /// If `even_or_odd` = `Parity::Evn`:
    ///
    ///  | T_0 |   A_0   |    A_1   | T_1 |   A_2   |    A_3   |  A_4  |
    ///  |-----|---------|----------|-----|---------|----------|-------|
    ///  |  12 | Evn.12a | ~Evn.12a |  12 | Odd.12a | ~Odd.12a |  Evn  |
    ///  |  12 | Evn.12b | ~Evn.12b |  12 | Odd.12b | ~Odd.12b |       |
    ///  |   8 | Evn.8   | ~Evn.8   |   8 | Odd.2   | ~Odd.8   |       |
    ///
    /// and returns `Evn`.
    ///
    /// If `even_or_odd` = `Parity::Odd`:
    ///
    ///  | T_0 |   A_0   |    A_1   | T_1 |   A_2   |    A_3   |  A_4  |
    ///  |-----|---------|----------|-----|---------|----------|-------|
    ///  |  12 | Odd.12a | ~Odd.12a |  12 | Evn.12a | ~Evn.12a |  Odd  |
    ///  |  12 | Odd.12b | ~Odd.12b |  12 | Evn.12b | ~Evn.12b |       |
    ///  |   8 | Odd.8   | ~Odd.8   |   8 | Evn.2   | ~Evn.8   |       |
    ///
    /// and returns `Odd`.
    ///
    /// This function guarantees that the returned value is consistent with
    /// the values in the filled lookup table.
    fn assign_sprdd_12_12_8(
        &self,
        region: &mut Region<'_, F>,
        value: Value<u64>,
        even_or_odd: Parity,
        offset: usize,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        self.config().q_12_12_8.enable(region, offset)?;

        let (evn_val, odd_val) = value.map(get_even_and_odd_bits).unzip();

        let [evn_12a, evn_12b, evn_8] = evn_val
            .map(|v| u32_in_be_limbs(v, [12, 12, 8]))
            .transpose_array();

        let [odd_12a, odd_12b, odd_8] = odd_val
            .map(|v| u32_in_be_limbs(v, [12, 12, 8]))
            .transpose_array();

        let idx = match even_or_odd {
            Parity::Evn => 0,
            Parity::Odd => 1,
        };

        self.assign_plain_and_spreaded::<12>(region, evn_12a, offset, idx)?;
        self.assign_plain_and_spreaded::<12>(region, evn_12b, offset + 1, idx)?;
        self.assign_plain_and_spreaded::<8>(region, evn_8, offset + 2, idx)?;

        self.assign_plain_and_spreaded::<12>(region, odd_12a, offset, 1 - idx)?;
        self.assign_plain_and_spreaded::<12>(region, odd_12b, offset + 1, 1 - idx)?;
        self.assign_plain_and_spreaded::<8>(region, odd_8, offset + 2, 1 - idx)?;

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

    /// A compression round. This is called 64 times per block.
    fn compression_round(
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

    /// Message schedule per block. The output will be used in the compression
    /// rounds.
    fn message_schedule(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &[AssignedPlain<F, 32>; 16],
    ) -> Result<[AssignedPlain<F, 32>; 64], Error> {
        let message_word = self.prepare_message_word(layouter, &[block[0].clone()])?;
        let mut message_words: [AssignedMessageWord<F>; 64] =
            core::array::from_fn(|_| message_word.clone());

        // The first 16 message words are got by decomposing the block words
        // into 12-1-1-1-7-3-4-3 limbs directly.
        for word_idx in 1..16 {
            message_words[word_idx] =
                self.prepare_message_word(layouter, &[block[word_idx].clone()])?;
        }
        // The remaining 48 message words are computed using the recurrence relation
        // W.i = W.(i-16) + W.(i-7) + σ₀(W.(i-15)) + σ₁(W.(i-2))
        // and decomposing into 12-1-1-1-7-3-4-3 limbs.
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

    /// Given a slice of at most 7 `AssignedPlain` values, this function adds
    /// them modulo 2^32 and decomposes the result (named W_i) into (bit-endian)
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

        | T_0 |  A_0 |  A_1  | T_1 |  A_2  |   A_3  | A_4 | A_5 | A_6 |  A_7  |
        |-----|------|-------|-----|-------|--------|-----|-----|-----|-------|
        |  12 | W.12 | ~W.12 | 07  |  W.07 | ~W.07  | W.i |  S0 |  S1 |  W.1a |
        |  03 | W.3a | ~W.3a | 04  |  W.04 | ~W.04  |     |  S2 |  S3 |  W.1b |
        |  03 | W.3b | ~W.3b | 03  | carry | ~carry |  S4 |  S5 |  S6 |  W.1c |

        Apart from the lookups, the following identity is checked via a
        custom gate with selector q_12_1_1_1_7_3_4_3:

            W.i = 2^20 * W.12 + 2^19 * W.1a + 2^18 * W.1b + 2^17 * W.1c + 2^10 * W.07 + 2^7 * W.3a + 2^3 * W.04 + W.3b

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
                self.config().q_12_1_1_1_7_3_4_3.enable(&mut region, 0)?;

                let w_i_plain = self.assign_add_mod_2_32(&mut region, &summands, &zero)?;

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

    /// Computes σ₀(W).
    fn sigma_0(
        &self,
        layouter: &mut impl Layouter<F>,
        w: &AssignedMessageWord<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
         We need to compute:
            W  >>  3 :          ( W.12 || W.1a || W.1b || W.1c || W.07 || W.3a || W.04 )
          ⊕ W >>>  7 :  ( W.04 || W.3b || W.12 || W.1a || W.1b || W.1c || W.07 || W.3a )
          ⊕ W >>> 18 :  ( W.1c || W.07 || W.3a || W.04 || W.3b || W.12 || W.1a || W.1b )

        which can be achieved by

         1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Evn:
              2^20 * Evn.12a + 2^8 * Evn.12b + Evn.8
            = Evn

        3) asserting the sigma_0 identity regarding the spreaded values:
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8) +
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             =                4^17 * ~W.12 + 4^16 * ~W.1a + 4^15 * ~W.1b + 4^14 * ~W.1c + 4^7 * ~W.07 +  4^4 * ~W.3a + ~W.04
             + 4^28 * ~W.04 + 4^25 * ~W.3b + 4^13 * ~W.12 + 4^12 * ~W.1a + 4^11 * ~W.1b + 4^10 * ~W.1c + 4^3 * ~W.07 + ~W.3a
             + 4^31 * ~W.1c + 4^24 * ~W.07 + 4^21 * ~W.3a + 4^17 * ~W.04 + 4^14 * ~W.3b +  4^2 * ~W.12 + 4^1 * ~W.1a + ~W.1b

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T_0 |    A_0   |    A_1    | T_1 |   A_2   |    A_3   |  A_4  |   A_5  |   A_6  |
        |-----|----------|-----------|-----|---------|----------|-------|--------|--------|
        |  12 | Even.12a | ~Even.12a |  12 | Odd.12a | ~Odd.12a |  Evn  | ~W.12  | ~W.1a  |
        |  12 | Even.12b | ~Even.12b |  12 | Odd.12b | ~Odd.12b | ~W.1b | ~W.1c  | ~W.07  |
        |   8 | Even.8   | ~Even.8   |   8 | Odd.8   | ~Odd.8   | ~W.3a | ~W.04  | ~W.3b  |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "σ₀(W)",
            |mut region| {
                self.config().q_sigma_0.enable(&mut region, 0)?;

                (w.spreaded_w_12.0).copy_advice(|| "~W.12", &mut region, adv_cols[5], 0)?;
                (w.spreaded_w_1a.0).copy_advice(|| "~W.1a", &mut region, adv_cols[6], 0)?;
                (w.spreaded_w_1b.0).copy_advice(|| "~W.1b", &mut region, adv_cols[4], 1)?;
                (w.spreaded_w_1c.0).copy_advice(|| "~W.1c", &mut region, adv_cols[5], 1)?;
                (w.spreaded_w_07.0).copy_advice(|| "~W.07", &mut region, adv_cols[6], 1)?;
                (w.spreaded_w_3a.0).copy_advice(|| "~W.3a", &mut region, adv_cols[4], 2)?;
                (w.spreaded_w_04.0).copy_advice(|| "~W.04", &mut region, adv_cols[5], 2)?;
                (w.spreaded_w_3b.0).copy_advice(|| "~W.3b", &mut region, adv_cols[6], 2)?;

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

                self.assign_sprdd_12_12_8(
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
         We need to compute:
            W  >> 10 :                          ( W.12 || W.1a || W.1b || W.1c || W.07 )
          ⊕ W >>> 17 :  ( W.07 || W.3a || W.04 || W.3b || W.12 || W.1a || W.1b || W.1c )
          ⊕ W >>> 19 :  ( W.1b || W.1c || W.07 || W.3a || W.04 || W.3b || W.12 || W.1a )

        which can be achieved by

         1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Evn:
              2^20 * Evn.12a + 2^8 * Evn.12b + Evn.8
            = Evn

        3) asserting the sigma_0 identity regarding the spreaded values:
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8) +
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             =                                              4^10 * ~W.12 +  4^9 * ~W.1a +  4^8 * ~W.1b + 4^7 * ~W.1c + ~W.07
             + 4^25 * ~W.07 + 4^22 * ~W.3a + 4^18 * ~W.04 + 4^15 * ~W.3b +  4^3 * ~W.12 +  4^2 * ~W.1a + 4^1 * ~W.1b + ~W.1c
             + 4^31 * ~W.1b + 4^30 * ~W.1c + 4^23 * ~W.07 + 4^20 * ~W.3a + 4^16 * ~W.04 + 4^13 * ~W.3b + 4^1 * ~W.12 + ~W.1a

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T_0 |    A_0   |    A_1    | T_1 |   A_2   |    A_3   |  A_4  |   A_5  |   A_6  |
        |-----|----------|-----------|-----|---------|----------|-------|--------|--------|
        |  12 | Even.12a | ~Even.12a |  12 | Odd.12a | ~Odd.12a |  Evn  | ~W.12  | ~W.1a  |
        |  12 | Even.12b | ~Even.12b |  12 | Odd.12b | ~Odd.12b | ~W.1b | ~W.1c  | ~W.07  |
        |   8 | Even.8   | ~Even.8   |   8 | Odd.8   | ~Odd.8   | ~W.3a | ~W.04  | ~W.3b  |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "σ₁(W)",
            |mut region| {
                self.config().q_sigma_1.enable(&mut region, 0)?;

                (w.spreaded_w_12.0).copy_advice(|| "~W.12", &mut region, adv_cols[5], 0)?;
                (w.spreaded_w_1a.0).copy_advice(|| "~W.1a", &mut region, adv_cols[6], 0)?;
                (w.spreaded_w_1b.0).copy_advice(|| "~W.1b", &mut region, adv_cols[4], 1)?;
                (w.spreaded_w_1c.0).copy_advice(|| "~W.1c", &mut region, adv_cols[5], 1)?;
                (w.spreaded_w_07.0).copy_advice(|| "~W.07", &mut region, adv_cols[6], 1)?;
                (w.spreaded_w_3a.0).copy_advice(|| "~W.3a", &mut region, adv_cols[4], 2)?;
                (w.spreaded_w_04.0).copy_advice(|| "~W.04", &mut region, adv_cols[5], 2)?;
                (w.spreaded_w_3b.0).copy_advice(|| "~W.3b", &mut region, adv_cols[6], 2)?;

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

                self.assign_sprdd_12_12_8(
                    &mut region,
                    val_of_sprdd_limbs.map(spreaded_sigma_1),
                    Parity::Evn,
                    0,
                )
            },
        )
    }

    /// Given a slice of at most 7 `AssignedPlain` values, this function adds
    /// them modulo 2^32 and returns sum_plain:
    ///
    ///     S0 + S1 + S2 + S3 + S4 + S5 + S6 = sum_plain + carry * 2^32
    ///
    ///  | T_1 |  A_2  |   A_3  |    A_4    |  A_5 |  A_6 |
    ///  |-----|-------|--------|-----------|------|------|
    ///  |     |       |        | sum_plain |  S0  |  S1  |
    ///  |     |       |        |           |  S2  |  S3  |
    ///  | 03  | carry | ~carry |     S4    |  S5  |  S6  |
    ///
    /// The `zero` argument is supposed to contain an assigned plain containing
    /// value 0, this is not enforced in this function, it is the responsibility
    /// of the caller to do so.
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
        assert!(summands.len() <= 7);

        self.config().q_add_mod_2_32.enable(region, 0)?;
        let adv_cols = self.config().advice_cols;

        let mut summands = summands.to_vec();
        summands.resize(7, zero.clone());

        let (carry_val, sum_val): (Value<u32>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u64).sum())
                .map(|s: u64| s.div_rem(&(1 << 32)))
                .map(|(carry, r)| (carry as u32, u64_to_fe(r)))
                .unzip();

        (summands[0].0).copy_advice(|| "S0", region, adv_cols[5], 0)?;
        (summands[1].0).copy_advice(|| "S1", region, adv_cols[6], 0)?;
        (summands[2].0).copy_advice(|| "S2", region, adv_cols[5], 1)?;
        (summands[3].0).copy_advice(|| "S3", region, adv_cols[6], 1)?;
        (summands[4].0).copy_advice(|| "S4", region, adv_cols[4], 2)?;
        (summands[5].0).copy_advice(|| "S5", region, adv_cols[5], 2)?;
        (summands[6].0).copy_advice(|| "S6", region, adv_cols[6], 2)?;
        let _carry: AssignedPlainSpreaded<F, 3> =
            self.assign_plain_and_spreaded(region, carry_val, 2, 1)?;
        region
            .assign_advice(|| "sum", adv_cols[4], 0, || sum_val)
            .map(AssignedPlain)
    }

    /// Pads the input byte array to be a multiple of 64 bytes.
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
    /// block of 16 `AssignedPlain` values, each (32 bits) value
    /// representing 4 bytes in big-endian.
    ///
    /// # Panics
    ///
    /// If it does not receive exactly 64 bytes.
    fn block_from_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: &[AssignedByte<F>],
    ) -> Result<[AssignedPlain<F, 32>; 16], Error> {
        assert_eq!(bytes.len(), 64);

        let block = bytes
            .chunks(4)
            .map(|word_bytes| {
                self.native_gadget
                    .assigned_from_be_bytes(layouter, word_bytes)
                    .map(AssignedPlain)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(block.try_into().unwrap())
    }

    /// SHA256 computation.
    pub fn sha256(
        &self,
        layouter: &mut impl Layouter<F>,
        input_bytes: &[AssignedByte<F>],
    ) -> Result<[AssignedPlain<F, 32>; 8], Error> {
        let mut state = CompressionState::<F>::fixed(layouter, &self.native_gadget, &IV)?;

        for block_bytes in self.pad(layouter, input_bytes)?.chunks(64) {
            let block = self.block_from_bytes(layouter, block_bytes)?;
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
        // TODO: d can be optimized and do it in a single row without `prepare_A`.

        let e = sha256_chip.prepare_E(layouter, &[self.e.plain(), other.e.plain()])?;
        let f = sha256_chip.prepare_E(layouter, &[self.f.plain.clone(), other.f.plain.clone()])?;
        let g = sha256_chip.prepare_E(layouter, &[self.g.plain.clone(), other.g.plain.clone()])?;
        let h = sha256_chip.prepare_E(layouter, &[self.h.clone(), other.h.clone()])?;
        // TODO: h can be optimized and do it in a single row without `prepare_E`.

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
impl<F: PrimeField> FromScratch<F> for Sha256Chip<F> {
    type Config = (
        Sha256Config,
        <NativeGadget<F, P2RDecompositionChip<F>, NativeChip<F>> as FromScratch<F>>::Config,
    );

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
        let adv_cols: [Column<Advice>; NB_SHA256_ADVICE_COLS] =
            std::array::from_fn(|_| meta.advice_column());
        let fixed_cols: [Column<Fixed>; NB_SHA256_FIXED_COLS] =
            std::array::from_fn(|_| meta.fixed_column());
        // Add all advice columns to permutation
        for column in adv_cols.iter() {
            meta.enable_equality(*column);
        }

        for column in fixed_cols.iter() {
            meta.enable_constant(*column);
        }
        (
            <Sha256Chip<F> as ComposableChip<F>>::configure(meta, &(adv_cols, fixed_cols)),
            NativeGadget::configure_from_scratch(meta, instance_columns),
        )
    }

    fn load_from_scratch(layouter: &mut impl Layouter<F>, config: &Self::Config) {
        let sha256_chip = Sha256Chip::new_from_scratch(config);
        let _ = sha256_chip.load(layouter);
        NativeGadget::load_from_scratch(layouter, &config.1);
    }
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use halo2curves::pasta::pallas;
    use midnight_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use sha2::Digest;

    use super::*;
    use crate::{
        instructions::{AssertionInstructions, AssignmentInstructions},
        testing_utils::FromScratch,
        utils::util::fe_to_u32,
    };

    /// Test vector: "abc"
    #[cfg(test)]
    pub const PAD_TEST_INPUT: [u8; 3] = [0x61, 0x62, 0x63];

    #[cfg(test)]
    pub fn msg_schedule_test_input() -> [u32; 16] {
        [
            0b01100001_01100010_01100011_10000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000000000,
            0b00000000000000000000000000011000,
        ]
    }

    #[cfg(test)]
    pub const MSG_SCHEDULE_TEST_OUTPUT: [u32; 64] = [
        0b01100001011000100110001110000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000011000,
        0b01100001011000100110001110000000,
        0b00000000000011110000000000000000,
        0b01111101101010000110010000000101,
        0b01100000000000000000001111000110,
        0b00111110100111010111101101111000,
        0b00000001100000111111110000000000,
        0b00010010110111001011111111011011,
        0b11100010111000101100001110001110,
        0b11001000001000010101110000011010,
        0b10110111001101100111100110100010,
        0b11100101101111000011100100001001,
        0b00110010011001100011110001011011,
        0b10011101001000001001110101100111,
        0b11101100100001110010011011001011,
        0b01110000001000010011100010100100,
        0b11010011101101111001011100111011,
        0b10010011111101011001100101111111,
        0b00111011011010001011101001110011,
        0b10101111111101001111111111000001,
        0b11110001000010100101110001100010,
        0b00001010100010110011100110010110,
        0b01110010101011111000001100001010,
        0b10010100000010011110001100111110,
        0b00100100011001000001010100100010,
        0b10011111010001111011111110010100,
        0b11110000101001100100111101011010,
        0b00111110001001000110101001111001,
        0b00100111001100110011101110100011,
        0b00001100010001110110001111110010,
        0b10000100000010101011111100100111,
        0b01111010001010010000110101011101,
        0b00000110010111000100001111011010,
        0b11111011001111101000100111001011,
        0b11001100011101100001011111011011,
        0b10111001111001100110110000110100,
        0b10101001100110010011011001100111,
        0b10000100101110101101111011011101,
        0b11000010000101000110001010111100,
        0b00010100100001110100011100101100,
        0b10110010000011110111101010011001,
        0b11101111010101111011100111001101,
        0b11101011111001101011001000111000,
        0b10011111111000110000100101011110,
        0b01111000101111001000110101001011,
        0b10100100001111111100111100010101,
        0b01100110100010110010111111111000,
        0b11101110101010111010001011001100,
        0b00010010101100011110110111101011,
    ];

    #[test]
    fn message_schedule() {
        struct MyCircuit {}

        impl<F: PrimeField> Circuit<F> for MyCircuit {
            type Config = <Sha256Chip<F> as FromScratch<F>>::Config;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                MyCircuit {}
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let committed_instance_column = meta.instance_column();
                let instance_column = meta.instance_column();
                <Sha256Chip<F> as FromScratch<F>>::configure_from_scratch(
                    meta,
                    &[committed_instance_column, instance_column],
                )
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                <Sha256Chip<F> as FromScratch<F>>::load_from_scratch(&mut layouter, &config);
                let sha256_chip = Sha256Chip::new_from_scratch(&config);
                let native_gadget = sha256_chip.native_gadget.clone();
                // Provide input
                // Test vector: "abc"
                let inputs: [Value<F>; 16] =
                    msg_schedule_test_input().map(|x| Value::known(u32_to_fe(x)));
                let assigned_inputs: [AssignedPlain<F, 32>; 16] = native_gadget
                    .assign_many(&mut layouter, &inputs)?
                    .into_iter()
                    .map(AssignedPlain)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let message_words =
                    sha256_chip.message_schedule(&mut layouter, &assigned_inputs)?;
                for (word, test_word) in message_words.iter().zip(MSG_SCHEDULE_TEST_OUTPUT.iter()) {
                    word.0.value().copied().assert_if_known(|word| {
                        let word = fe_to_u32(*word);
                        word == *test_word
                    });
                }
                Ok(())
            }
        }

        let circuit: MyCircuit = MyCircuit {};

        let prover = match MockProver::<pallas::Base>::run(16, &circuit, vec![vec![], vec![]]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn compress() {
        struct MyCircuit {}

        impl<F: PrimeField> Circuit<F> for MyCircuit {
            type Config = <Sha256Chip<F> as FromScratch<F>>::Config;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                MyCircuit {}
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let committed_instance_column = meta.instance_column();
                let instance_column = meta.instance_column();
                <Sha256Chip<F> as FromScratch<F>>::configure_from_scratch(
                    meta,
                    &[committed_instance_column, instance_column],
                )
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                <Sha256Chip<F> as FromScratch<F>>::load_from_scratch(&mut layouter, &config);
                let sha256_chip = Sha256Chip::new_from_scratch(&config);
                let native_gadget = sha256_chip.native_gadget.clone();
                // Provide input
                // Test vector: "abc"
                let inputs: [Value<F>; 64] =
                    MSG_SCHEDULE_TEST_OUTPUT.map(|x| Value::known(u32_to_fe(x)));
                let assigned_inputs: [AssignedPlain<F, 32>; 64] = native_gadget
                    .assign_many(&mut layouter, &inputs)?
                    .into_iter()
                    .map(AssignedPlain)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let mut state = CompressionState::<F>::fixed(&mut layouter, &native_gadget, &IV)?;
                let mut compression_state = state.clone();

                for i in 0..64 {
                    compression_state = sha256_chip.compression_round(
                        &mut layouter,
                        &compression_state,
                        ROUND_CONSTANTS[i],
                        &assigned_inputs[i],
                    )?;
                }
                state = state.add(&sha256_chip, &mut layouter, &compression_state)?;

                let state = state.plain();

                let hash_output = sha2::Sha256::digest("abc");

                let expected_result: Vec<u32> = hash_output
                    .chunks(4)
                    .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
                    .collect();

                for (idx, word) in state.into_iter().enumerate() {
                    word.0.value().copied().assert_if_known(|word| {
                        let f_bytes = word
                            .to_repr()
                            .as_ref()
                            .chunks(4)
                            .map(|bytes| u32::from_le_bytes(bytes.try_into().unwrap()))
                            .collect::<Vec<_>>();
                        let (x, xs) = (f_bytes[0], &f_bytes[1..]);
                        x == expected_result[idx] && xs.iter().all(|&x| x == 0)
                    });
                }

                Ok(())
            }
        }

        let circuit = MyCircuit {};

        let prover = match MockProver::<pallas::Base>::run(16, &circuit, vec![vec![], vec![]]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn pad() {
        struct MyCircuit {}

        impl<F: PrimeField> Circuit<F> for MyCircuit {
            type Config = <Sha256Chip<F> as FromScratch<F>>::Config;
            type FloorPlanner = SimpleFloorPlanner;
            type Params = ();

            fn without_witnesses(&self) -> Self {
                MyCircuit {}
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let committed_instance_column = meta.instance_column();
                let instance_column = meta.instance_column();
                <Sha256Chip<F> as FromScratch<F>>::configure_from_scratch(
                    meta,
                    &[committed_instance_column, instance_column],
                )
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                <Sha256Chip<F> as FromScratch<F>>::load_from_scratch(&mut layouter, &config);
                let sha256_chip = Sha256Chip::new_from_scratch(&config);
                let native_gadget = sha256_chip.native_gadget.clone();

                // Provide input
                // Test vector: "abc"
                let assigned_padding_input: [AssignedByte<F>; 3] =
                    PAD_TEST_INPUT.map(|x| native_gadget.assign_fixed(&mut layouter, x).unwrap());

                let assigned_padding_output =
                    sha256_chip.pad(&mut layouter, &assigned_padding_input)?;
                let block_words =
                    sha256_chip.block_from_bytes(&mut layouter, &assigned_padding_output)?;
                // convert the assigned 32-bit words to assigned bytes in big-endian order
                let assigned_output_bytes = block_words
                    .iter()
                    .map(|word| native_gadget.assigned_to_be_bytes(&mut layouter, &word.0, Some(4)))
                    .collect::<Result<Vec<_>, Error>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                let expected_result = msg_schedule_test_input();

                // Check padding
                //    for (word, test_word) in
                // block_words.iter().zip(msg_schedule_test_input().iter()) {
                //         word.0.value().copied().assert_if_known(|word| {
                //             let word = fe_to_u32(*word);
                //             word == *test_word
                //         });
                //     }

                for (idx, word) in block_words.iter().enumerate() {
                    let _ = native_gadget.assert_equal_to_fixed(
                        &mut layouter,
                        &word.0,
                        u32_to_fe(expected_result[idx]),
                    );
                }

                Ok(())
            }
        }

        let circuit = MyCircuit {};

        let prover = match MockProver::<pallas::Base>::run(16, &circuit, vec![vec![], vec![]]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
