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
            add_mod_2_32_gate, ch_helper_gate, decompose_10_9_11_2_gate, decompose_12_12_8_gate,
            decompose_7_12_2_5_6_gate, maj_gate, Sigma_0_gate, Sigma_1_gate,
        },
        types::{AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded, LimbsOfA, LimbsOfE},
        utils::{
            gen_spread_table, get_even_and_odd_bits, negate_spreaded, spread, spreaded_Sigma_0,
            spreaded_Sigma_1, spreaded_maj, u32_in_be_limbs, u32_to_fe, u64_to_fe, MASK_EVN_64,
        },
    },
    utils::{
        util::{fe_to_u32, fe_to_u64},
        ComposableChip,
    },
};

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
    q_12_12_8: Selector,
    q_10_9_11_2: Selector,
    q_7_12_2_5_6: Selector,
    q_add_mod_2_32: Selector,
    q_ch_helper: Selector,
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
        let q_12_12_8 = meta.selector();
        let q_10_9_11_2 = meta.selector();
        let q_7_12_2_5_6 = meta.selector();
        let q_add_mod_2_32 = meta.selector();
        let q_ch_helper = meta.selector();
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

        meta.create_gate("helper of Ch(E, F, G)", |meta| {
            let q_ch_helper = meta.query_selector(q_ch_helper);

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

            ch_helper_gate(
                q_ch_helper,
                [sprdd_x, sprdd_y],
                [sprdd_evn_12a, sprdd_evn_12b, sprdd_evn_8],
                [sprdd_odd_12a, sprdd_odd_12b, sprdd_odd_8],
                [summand_1, summand_2, sum],
            )
        });

        Sha256Config {
            advice_cols,
            fixed_cols,
            q_Sigma_0,
            q_Sigma_1,
            q_maj,
            q_12_12_8,
            q_10_9_11_2,
            q_7_12_2_5_6,
            q_add_mod_2_32,
            q_ch_helper,
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
    /// Given an array of 7 `AssignedPlain` values, it adds them modulo 2^32
    /// and decomposes the result (named A) into (bit-endian) limbs of bit
    /// sizes 10, 9, 11 and 2.
    ///
    /// This function also returns the spreaded version of the sum, ~A and
    /// the limbs of A.
    pub(super) fn prepare_A(
        &self,
        layouter: &mut impl Layouter<F>,
        summands: &[AssignedPlain<F, 32>; 7],
    ) -> Result<(AssignedPlainSpreaded<F, 32>, LimbsOfA<F>), Error> {
        /*
        Given assigned plain inputs S0, ..., S6, let A be their sum modulo 2^32.
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

        let (carry_val, a_val): (Value<u32>, Value<F>) =
            Value::<Vec<F>>::from_iter(summands.iter().map(|s| s.0.value().copied()))
                .map(|v| v.into_iter().map(fe_to_u64).sum())
                .map(|s: u64| s.div_rem(&(1 << 32)))
                .map(|(carry, a)| (carry as u32, u64_to_fe(a)))
                .unzip();

        let a_spreaded_val = a_val.map(fe_to_u32).map(spread).map(u64_to_fe);

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
                let a_sprdd = region.assign_advice(|| "~A", adv_cols[4], 1, || a_spreaded_val)?;

                (summands[0].0).copy_advice(|| "S0", &mut region, adv_cols[5], 0)?;
                (summands[1].0).copy_advice(|| "S1", &mut region, adv_cols[6], 0)?;
                (summands[2].0).copy_advice(|| "S2", &mut region, adv_cols[5], 1)?;
                (summands[3].0).copy_advice(|| "S3", &mut region, adv_cols[6], 1)?;
                (summands[4].0).copy_advice(|| "S4", &mut region, adv_cols[4], 2)?;
                (summands[5].0).copy_advice(|| "S5", &mut region, adv_cols[5], 2)?;
                (summands[6].0).copy_advice(|| "S6", &mut region, adv_cols[6], 2)?;

                Ok((
                    AssignedPlainSpreaded {
                        plain: AssignedPlain(a_plain),
                        spreaded: AssignedSpreaded(a_sprdd),
                    },
                    LimbsOfA {
                        spreaded_limb_10: limb_10.spreaded,
                        spreaded_limb_09: limb_09.spreaded,
                        spreaded_limb_11: limb_11.spreaded,
                        spreaded_limb_02: limb_02.spreaded,
                    },
                ))
            },
        )
    }

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

    /// Decomposes the given `AssignedPlain` into (bit-endian) limbs of bit
    /// sizes 7, 12, 2, 5 and 6.
    ///
    /// This function also returns the spreaded version of the given input.
    pub(super) fn decompose_in_7_12_2_5_6(
        &self,
        layouter: &mut impl Layouter<F>,
        plain: &AssignedPlain<F, 32>,
    ) -> Result<(AssignedPlainSpreaded<F, 32>, LimbsOfE<F>), Error> {
        /*
        On a plain input E, we use the following table distribution.

        | T_0 |  A_0 |  A_1  | T_1 |  A_2  |   A_3  | A_4 |
        |-----|------|-------|-----|-------|--------|-----|
        |  07 | E.07 | ~E.07 |  12 |  E.12 | ~E.12  |  E  | <- a copy of plain
        |  02 | E.02 | ~E.02 |  05 |  E.05 | ~E.05  | ~E  |
        |  06 | E.06 | ~E.06 |   0 |   0   |    0   |     |

        Apart from the lookups, the following identities are checked via a
        custom gate:
            E = 2^25 *  E.07 + 2^13 *  E.12 + 2^11 *  E.02 + 2^6 *  E.05 +  E.06
           ~E = 4^25 * ~E.07 + 4^13 * ~E.12 + 4^11 * ~E.02 + 4^6 * ~E.05 + ~E.06
        */

        let adv_cols = self.config().advice_cols;
        let plain_val = plain.0.value().copied();
        let sprdd_val = plain_val.map(fe_to_u32).map(spread).map(u64_to_fe);
        let [val_07, val_12, val_02, val_05, val_06] = plain_val
            .map(|e| u32_in_be_limbs(fe_to_u32(e), [7, 12, 2, 5, 6]))
            .transpose_array();

        layouter.assign_region(
            || "decompose E in 7-12-2-5-6",
            |mut region| {
                self.config().q_7_12_2_5_6.enable(&mut region, 0)?;

                let limb_07 = self.assign_plain_and_spreaded(&mut region, val_07, 0, 0)?;
                let limb_12 = self.assign_plain_and_spreaded(&mut region, val_12, 0, 1)?;
                let limb_02 = self.assign_plain_and_spreaded(&mut region, val_02, 1, 0)?;
                let limb_05 = self.assign_plain_and_spreaded(&mut region, val_05, 1, 1)?;
                let limb_06 = self.assign_plain_and_spreaded(&mut region, val_06, 2, 0)?;
                let _ = self.assign_plain_and_spreaded::<0>(&mut region, Value::known(0), 2, 1)?;

                plain.0.copy_advice(|| "E", &mut region, adv_cols[4], 0)?;
                let spreaded = region.assign_advice(|| "~E", adv_cols[4], 1, || sprdd_val)?;

                Ok((
                    AssignedPlainSpreaded {
                        plain: plain.clone(),
                        spreaded: AssignedSpreaded(spreaded),
                    },
                    LimbsOfE {
                        spreaded_limb_07: limb_07.spreaded,
                        spreaded_limb_12: limb_12.spreaded,
                        spreaded_limb_02: limb_02.spreaded,
                        spreaded_limb_05: limb_05.spreaded,
                        spreaded_limb_06: limb_06.spreaded,
                    },
                ))
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

    /// Computes Ch(E, F, G)
    pub(super) fn ch(
        &self,
        layouter: &mut impl Layouter<F>,
        sprdd_e: &AssignedSpreaded<F, 32>,
        sprdd_f: &AssignedSpreaded<F, 32>,
        sprdd_g: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We need to compute:
            Ch(E, F, G) = (E ∧ F) ⊕ (¬E ∧ G)

        which can be achieved by

        1) applying the plain-spreaded lookup on 12-12-8 limbs of Evn and Odd for both (~E + ~F) and (~¬E + ~G):
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Odd_0 of (~E + ~F) and for Odd_1 of (~¬E + ~G):
              2^20 * Odd.12a + 2^8 * Odd.12b + Odd.8
            = Odd_i

        3) asserting the spreaded addition identity for both (~E + ~F) and (~¬E + ~G):
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8)
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             = ~E + ~F (or ~¬E + ~G)

        4) asserting the following two addition identities:
                    Ret = Odd_0 + Odd_1
            MASK_EVN_64 =    ~E + ~¬E

        The output is Ret.

        We distribute these values in the PLONK table as follows.

        | T_0 |    A_0   |     A_1   | T_1 |    A_2  |    A_3   |  A_4  |  A_5  |    A_6     |
        |-----|----------|-----------|-----|---------|----------|-------|-------|------------|
        |  12 | Odd.12a  | ~Odd.12a  |  12 | Evn.12a | ~Evn.12a | Odd_0 |   ~E  |     ~F     |
        |  12 | Odd.12b  | ~Odd.12b  |  12 | Evn.12b | ~Evn.12b | Odd_0 |Odd_1  |    Ret     |
        |   8 |   Odd.8  |   ~Odd.8  |   8 |   Evn.8 |   ~Evn.8 |       |       |            |
        |  12 | Odd.12a  | ~Odd.12a  |  12 | Evn.12a | ~Evn.12a | Odd_1 |  ~¬E  |     ~G     |
        |  12 | Odd.12b  | ~Odd.12b  |  12 | Evn.12b | ~Evn.12b |    ~E |  ~¬E  |MASK_EVN_64 |
        |   8 |   Odd.8  |   ~Odd.8  |   8 |   Evn.2 |   ~Evn.8 |       |       |            |
        */

        let adv_cols = self.config().advice_cols;
        // ~E + ~F
        let sprdd_e_plus_sprdd_f_val = Value::zip(
            sprdd_e.0.value().copied().map(fe_to_u64),
            sprdd_f.0.value().copied().map(fe_to_u64),
        )
        .map(|(e, f)| e + f);
        // ~¬E
        let sprdd_neg_e_val = sprdd_e
            .0
            .value()
            .copied()
            .map(fe_to_u64)
            .map(negate_spreaded);
        // ~¬E + ~G
        let sprdd_neg_e_plus_sprdd_g_val =
            Value::zip(sprdd_neg_e_val, sprdd_g.0.value().copied().map(fe_to_u64))
                .map(|(neg_e, g)| neg_e + g);
        // MASK_EVN_64
        let mask_evn_64_val = Value::known(MASK_EVN_64);

        layouter.assign_region(
            || "Ch(E, F, G)",
            |mut region| {
                self.config().q_ch_helper.enable(&mut region, 0)?;
                self.config().q_ch_helper.enable(&mut region, 3)?;

                (sprdd_e.0).copy_advice(|| "~E", &mut region, adv_cols[5], 0)?;
                (sprdd_f.0).copy_advice(|| "~F", &mut region, adv_cols[6], 0)?;
                (sprdd_g.0).copy_advice(|| "~G", &mut region, adv_cols[6], 3)?;
                (sprdd_e.0).copy_advice(|| "~E", &mut region, adv_cols[4], 4)?;
                let sprdd_neg_e = region
                    .assign_advice(|| "~¬E", adv_cols[5], 3, || sprdd_neg_e_val.map(u64_to_fe))
                    .map(AssignedSpreaded::<F, 32>)?;
                sprdd_neg_e
                    .0
                    .copy_advice(|| "~¬E", &mut region, adv_cols[5], 4)?;
                let _mask_evn_64 = region
                    .assign_advice(
                        || "MASK_EVN_64",
                        adv_cols[6],
                        4,
                        || mask_evn_64_val.map(u64_to_fe),
                    )
                    .map(AssignedSpreaded::<F, 32>)?;

                let odd_0 = self.assign_sprdd_12_12_8(
                    &mut region,
                    sprdd_e_plus_sprdd_f_val,
                    Parity::Odd,
                    0,
                )?;
                odd_0
                    .0
                    .copy_advice(|| "Odd_0", &mut region, adv_cols[4], 1)?;

                let odd_1 = self.assign_sprdd_12_12_8(
                    &mut region,
                    sprdd_neg_e_plus_sprdd_g_val,
                    Parity::Odd,
                    3,
                )?;
                odd_1
                    .0
                    .copy_advice(|| "Odd_1", &mut region, adv_cols[5], 1)?;

                let ret_val = Value::zip(
                    odd_0.0.value().copied().map(fe_to_u32),
                    odd_1.0.value().copied().map(fe_to_u32),
                )
                .map(|(odd_0_val, odd_1_val)| odd_0_val + odd_1_val);

                region
                    .assign_advice(|| "Ret", adv_cols[6], 1, || ret_val.map(u32_to_fe))
                    .map(AssignedPlain::<F, 32>)
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
}
