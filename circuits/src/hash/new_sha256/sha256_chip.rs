use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use num_integer::Integer;

use crate::{
    field::NativeChip,
    hash::new_sha256::{
        gates::{
            add_mod_2_32_gate, decompose_10_9_11_2_gate, decompose_12_12_8_gate,
            decompose_7_12_2_5_6_gate, half_ch_gate, maj_gate, Sigma_0_gate, Sigma_1_gate,
        },
        types::{
            AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded, CompressionState, LimbsOfA,
            LimbsOfE,
        },
        utils::{
            gen_spread_table, get_even_and_odd_bits, negate_spreaded, spread, spreaded_Sigma_0,
            spreaded_Sigma_1, spreaded_maj, u32_in_be_limbs, u32_to_fe, u64_to_fe, MASK_EVN_64,
        },
    },
    instructions::assignments::AssignmentInstructions,
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

const NB_SHA256_ADVICE_COLS: usize = 7;
const NB_SHA256_FIXED_COLS: usize = 2;

/// Tag for the even and odd 12-12-8 decompositions.
enum Parity {
    Evn,
    Odd,
}

/// Plain-Spreaded lookup table.
#[derive(Clone, Debug)]
pub(super) struct SpreadTable {
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
    q_add_mod_2_32: Selector,
    q_lookup: Selector,
    table: SpreadTable,
}

/// Chip for SHA256
#[derive(Clone, Debug)]
pub struct Sha256Chip<F: PrimeField> {
    config: Sha256Config,
    native_chip: NativeChip<F>,
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

    type InstructionDeps = NativeChip<F>;

    fn new(config: &Sha256Config, native_chip: &Self::InstructionDeps) -> Self {
        Self {
            config: config.clone(),
            native_chip: native_chip.clone(),
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

        let q_Sigma_0 = meta.selector();
        let q_Sigma_1 = meta.selector();
        let q_maj = meta.selector();
        let q_half_ch = meta.selector();
        let q_12_12_8 = meta.selector();
        let q_10_9_11_2 = meta.selector();
        let q_7_12_2_5_6 = meta.selector();
        let q_add_mod_2_32 = meta.selector();
        let q_lookup = meta.complex_selector();

        (0..2).into_iter().for_each(|idx| {
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

            Sigma_0_gate(
                q_Sigma_0,
                [sprdd_a_10, sprdd_a_09, sprdd_a_11, sprdd_a_02],
                [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
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

            Sigma_1_gate(
                q_Sigma_1,
                [sprdd_e_07, sprdd_e_12, sprdd_e_02, sprdd_e_05, sprdd_e_06],
                [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
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

            maj_gate(
                q_maj,
                [sprdd_a, sprdd_b, sprdd_c],
                [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
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

            half_ch_gate(
                q_half_ch,
                [sprdd_x, sprdd_y],
                [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                [summand_1, summand_2, sum],
            )
        });

        meta.create_gate("12-12-8 decomposition", |meta| {
            let q_12_12_8 = meta.query_selector(q_12_12_8);

            let limb_12a = meta.query_advice(advice_cols[0], Rotation(0));
            let limb_12b = meta.query_advice(advice_cols[0], Rotation(1));
            let limb_8 = meta.query_advice(advice_cols[0], Rotation(2));
            let output = meta.query_advice(advice_cols[4], Rotation(0));

            decompose_12_12_8_gate(q_12_12_8, [limb_12a, limb_12b, limb_8], output)
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

            decompose_10_9_11_2_gate(
                q_10_9_11_2,
                [limb_10, limb_09, limb_11, limb_02],
                [sprdd_limb_10, sprdd_limb_09, sprdd_limb_11, sprdd_limb_02],
                (plain, sprdd),
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

            decompose_7_12_2_5_6_gate(
                q_7_12_2_5_6,
                [limb_07, limb_12, limb_02, limb_05, limb_06],
                [
                    sprdd_limb_07,
                    sprdd_limb_12,
                    sprdd_limb_02,
                    sprdd_limb_05,
                    sprdd_limb_06,
                ],
                (plain, sprdd),
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

            add_mod_2_32_gate(q_add_mod_2_32, &[s0, s1, s2, s3, s4, s5, s6], carry, result)
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
    pub(super) fn Sigma_0(
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
    pub(super) fn Sigma_1(
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
    pub(super) fn maj(
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
    pub(super) fn ch(
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
            (self.native_chip).assign_fixed(layouter, F::from(MASK_EVN_64))?;

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
    /// This function also returns the spreaded version of the sum, ~A and
    /// the limbs of A.
    pub(super) fn prepare_A(
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

        let adv_cols = self.config().advice_cols;

        let zero = AssignedPlain::<F, 32>(self.native_chip.assign_fixed(layouter, F::ZERO)?);
        let mut summands = summands.to_vec();
        summands.resize(7, zero);

        let (carry_val, a_val): (Value<u32>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u64).sum())
                .map(|s: u64| s.div_rem(&(1 << 32)))
                .map(|(carry, a)| (carry as u32, u64_to_fe(a)))
                .unzip();

        let a_sprdd_val = a_val.map(fe_to_u32).map(spread).map(u64_to_fe);

        let [val_10, val_09, val_11, val_02] = a_val
            .map(|a| u32_in_be_limbs(fe_to_u32(a), [10, 9, 11, 2]))
            .transpose_array();

        layouter.assign_region(
            || "decompose A in 10-9-11-2",
            |mut region| {
                self.config().q_10_9_11_2.enable(&mut region, 0)?;
                self.config().q_add_mod_2_32.enable(&mut region, 0)?;

                let limb_10 = self.assign_plain_and_spreaded(&mut region, val_10, 0, 0)?;
                let limb_09 = self.assign_plain_and_spreaded(&mut region, val_09, 0, 1)?;
                let limb_11 = self.assign_plain_and_spreaded(&mut region, val_11, 1, 0)?;
                let limb_02 = self.assign_plain_and_spreaded(&mut region, val_02, 1, 1)?;
                let _carry: AssignedPlainSpreaded<F, 3> =
                    self.assign_plain_and_spreaded(&mut region, carry_val, 2, 1)?;

                let a_plain = region.assign_advice(|| " A", adv_cols[4], 0, || a_val)?;
                let a_sprdd = region.assign_advice(|| "~A", adv_cols[4], 1, || a_sprdd_val)?;

                (summands[0].0).copy_advice(|| "S0", &mut region, adv_cols[5], 0)?;
                (summands[1].0).copy_advice(|| "S1", &mut region, adv_cols[6], 0)?;
                (summands[2].0).copy_advice(|| "S2", &mut region, adv_cols[5], 1)?;
                (summands[3].0).copy_advice(|| "S3", &mut region, adv_cols[6], 1)?;
                (summands[4].0).copy_advice(|| "S4", &mut region, adv_cols[4], 2)?;
                (summands[5].0).copy_advice(|| "S5", &mut region, adv_cols[5], 2)?;
                (summands[6].0).copy_advice(|| "S6", &mut region, adv_cols[6], 2)?;

                Ok(LimbsOfA {
                    combined: AssignedPlainSpreaded {
                        plain: AssignedPlain(a_plain),
                        spreaded: AssignedSpreaded(a_sprdd),
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
    /// This function also returns the spreaded version of the sum, ~E and
    /// the limbs of E.
    pub(super) fn prepare_E(
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

        let adv_cols = self.config().advice_cols;

        let zero = AssignedPlain::<F, 32>(self.native_chip.assign_fixed(layouter, F::ZERO)?);
        let mut summands = summands.to_vec();
        summands.resize(7, zero);

        let (carry_val, e_val): (Value<u32>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u64).sum())
                .map(|s: u64| s.div_rem(&(1 << 32)))
                .map(|(carry, e)| (carry as u32, u64_to_fe(e)))
                .unzip();

        let e_sprdd_val = e_val.map(fe_to_u32).map(spread).map(u64_to_fe);

        let [val_07, val_12, val_02, val_05, val_06] = e_val
            .map(|e| u32_in_be_limbs(fe_to_u32(e), [7, 12, 2, 5, 6]))
            .transpose_array();

        layouter.assign_region(
            || "decompose E in 7-12-2-5-6",
            |mut region| {
                self.config().q_7_12_2_5_6.enable(&mut region, 0)?;
                self.config().q_add_mod_2_32.enable(&mut region, 0)?;

                let limb_07 = self.assign_plain_and_spreaded(&mut region, val_07, 0, 0)?;
                let limb_12 = self.assign_plain_and_spreaded(&mut region, val_12, 0, 1)?;
                let limb_02 = self.assign_plain_and_spreaded(&mut region, val_02, 1, 0)?;
                let limb_05 = self.assign_plain_and_spreaded(&mut region, val_05, 1, 1)?;
                let limb_06 = self.assign_plain_and_spreaded(&mut region, val_06, 2, 0)?;
                let _carry: AssignedPlainSpreaded<F, 3> =
                    self.assign_plain_and_spreaded(&mut region, carry_val, 2, 1)?;

                let e_plain = region.assign_advice(|| " E", adv_cols[4], 0, || e_val)?;
                let e_sprdd = region.assign_advice(|| "~E", adv_cols[4], 1, || e_sprdd_val)?;

                (summands[0].0).copy_advice(|| "S0", &mut region, adv_cols[5], 0)?;
                (summands[1].0).copy_advice(|| "S1", &mut region, adv_cols[6], 0)?;
                (summands[2].0).copy_advice(|| "S2", &mut region, adv_cols[5], 1)?;
                (summands[3].0).copy_advice(|| "S3", &mut region, adv_cols[6], 1)?;
                (summands[4].0).copy_advice(|| "S4", &mut region, adv_cols[4], 2)?;
                (summands[5].0).copy_advice(|| "S5", &mut region, adv_cols[5], 2)?;
                (summands[6].0).copy_advice(|| "S6", &mut region, adv_cols[6], 2)?;

                Ok(LimbsOfE {
                    combined: AssignedPlainSpreaded {
                        plain: AssignedPlain(e_plain),
                        spreaded: AssignedSpreaded(e_sprdd),
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
        let round_k = AssignedPlain::<F, 32>::fixed(layouter, &self.native_chip, round_k)?;

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

    /// Message schedule.
    /// TODO
    fn message_schedule(
        &self,
        _layouter: &mut impl Layouter<F>,
        _input_bytes: &[AssignedByte<F>],
    ) -> Result<Vec<[AssignedPlain<F, 32>; 64]>, Error> {
        todo!()
    }

    /// SHA256 computation.
    fn sha256(
        &self,
        layouter: &mut impl Layouter<F>,
        input_bytes: &[AssignedByte<F>],
    ) -> Result<[AssignedPlain<F, 32>; 8], Error> {
        let message_blocks = self.message_schedule(layouter, input_bytes)?;
        let mut state = CompressionState::<F>::fixed(layouter, &self.native_chip, &IV)?;

        for block in message_blocks {
            let mut compression_state = state.clone();
            for i in 0..64 {
                compression_state = self.compression_round(
                    layouter,
                    &compression_state,
                    ROUND_CONSTANTS[i],
                    &block[i],
                )?;
            }
            state = state.add(&self, layouter, &compression_state)?;
        }

        Ok(state.plain())
    }
}

impl<F: PrimeField> CompressionState<F> {
    /// Adds pair-wise (modulo 2^32) the fields of two compression states.
    fn add(
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
