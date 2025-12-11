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

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    hash::ripemd160::{
        types::{AssignedSpreaded, AssignedWord},
        utils::{
            expr_pow2_ip, expr_pow4_ip, gen_spread_table, get_even_and_odd_bits, spread,
            spreaded_sum, u32_in_be_limbs,
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
pub const NB_RIPEMD160_FIXED_COLS: usize = 2;

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

        // Columns A0, A1, A2 and A3 do not need to be copy-enabled.
        // We have the convention that chips enable copy in a prefix of their shared
        // advice columns. Thus we let them be the last four columns of the given
        // shared resources.
        let advice_cols = [4, 5, 6, 7, 0, 1, 2, 3].map(|i| shared_res.0[i]);
        for column in advice_cols.iter().rev().take(4) {
            meta.enable_equality(*column);
        }

        let q_lookup = meta.complex_selector();
        let table = SpreadTable {
            nbits_col: meta.lookup_table_column(),
            plain_col: meta.lookup_table_column(),
            sprdd_col: meta.lookup_table_column(),
        };

        let q_11_11_10 = meta.selector();
        let q_spr_sum_evn = meta.selector();
        let q_spr_sum_odd = meta.selector();

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

        RipeMD160Config {
            advice_cols,
            fixed_cols,
            q_lookup,
            table,
            q_11_11_10,
            q_spr_sum_evn,
            q_spr_sum_odd,
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

    /// Given an assigned word A, this function prepares its spreaded form.
    fn prepare_spreaded(
        &self,
        layouter: &mut impl Layouter<F>,
        word: &AssignedWord<F>,
    ) -> Result<AssignedSpreaded<F, 32>, Error> {
        /*
         Given assigned word A, we first compute its spreaded form ~A, and then
         apply [`assign_sprdd_sum`] to the assigned values of ~A, ~0, ~0 as follows:

        | T0 |    A0   |     A1   | T1 |   A2   |   A3   |  A4 | A5 | A6 | A7 |
        |----|---------|----------|----|--------|--------|-----|----|----|----|
        | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   | Evn | ~A | ~0 | ~0 |
        | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   |     |    |    |    | <- q_spr_add, q_11_11_10
        | 10 | Evn.11a | ~Evn.11a | 10 |   0    |   ~0   |     |    |    |    |

        with constraints of:

          1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
              Evn: (Evn.11a, Evn.11b, Evn.10)
              Odd: (Odd.11a, Odd.11b, Odd.10)

         2) asserting the 11-11-10 decomposition identity for Evn:
               2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
             = Evn

         3) asserting the spr_sum_evn identity:
               (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
           2 * (4^21 * ~0       + 4^10 * ~0       + ~0     )
              = ~A + ~0 + ~0

         4) asserting that:
                 Evn = A
         */
        let sprdd_val = word.0.value().map(|&w| spread(fe_to_u32(w))).map(u64_to_fe);

        let v: Vec<AssignedSpreaded<F, 32>> = self
            .native_gadget
            .assign_many(
                layouter,
                &[sprdd_val, Value::known(F::ZERO), Value::known(F::ZERO)],
            )?
            .into_iter()
            .map(AssignedSpreaded)
            .collect();
        let [sprdd_word, sprdd_zero_a, sprdd_zero_b]: [AssignedSpreaded<F, 32>; 3] =
            v.try_into().unwrap();

        let even = self.assign_sprdd_sum(
            layouter,
            Parity::Evn,
            &sprdd_word,
            &sprdd_zero_a,
            &sprdd_zero_b,
        )?;

        let _ = self.native_gadget.is_equal(layouter, &word.0, &even.0)?;
        Ok(sprdd_word)
    }

    /// Given three assigned spreaded ~A, ~B, ~C, this function computes the
    /// value of ~A + ~B + ~C, and fills a lookup table with the limbs of its
    /// even and odd parts (or vice versa) and returns the former or the
    /// latter, depending on the desired value `even_or_odd`.
    fn assign_sprdd_sum(
        &self,
        layouter: &mut impl Layouter<F>,
        even_or_odd: Parity,
        sprdd_a: &AssignedSpreaded<F, 32>,
        sprdd_b: &AssignedSpreaded<F, 32>,
        sprdd_c: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedWord<F>, Error> {
        /*
        1) If `even_or_odd` = `Parity::Evn`, the circuit layout is as follows:

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |  A5 | A6 | A7 |
        |----|---------|----------|----|---------|----------|-----|-----|----|----|
        | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn |  ~A | ~B | ~C |
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

        2) If `even_or_odd` = `Parity::Odd`, the circuit layout is as follows:

        | T0 |    A0   |    A1    | T1 |    A2   |    A3    |  A4 |  A5 | A6 | A7 |
        |----|---------|----------|----|---------|----------|-----|-----|----|----|
        | 11 | Odd.11a | ~Odd.11a | 11 | Evn.11a | ~Evn.11a | Odd |  ~A | ~B | ~C |
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
             = ~A + ~B + ~C

        and returns `Odd`.
        */
        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Assign spreaded sum",
            |mut region| {
                match even_or_odd {
                    Parity::Evn => self.config().q_spr_sum_evn.enable(&mut region, 1)?,
                    Parity::Odd => self.config().q_spr_sum_odd.enable(&mut region, 1)?,
                };

                sprdd_a.0.copy_advice(|| "~A", &mut region, adv_cols[5], 0)?;
                sprdd_b.0.copy_advice(|| "~B", &mut region, adv_cols[6], 0)?;
                sprdd_c.0.copy_advice(|| "~C", &mut region, adv_cols[7], 0)?;

                let val_of_sprdd_forms: Value<[u64; 3]> = Value::from_iter([
                    sprdd_a.0.value().copied().map(fe_to_u64),
                    sprdd_b.0.value().copied().map(fe_to_u64),
                    sprdd_c.0.value().copied().map(fe_to_u64),
                ])
                .map(|sprdd_forms: Vec<u64>| sprdd_forms.try_into().unwrap());

                self.assign_sprdd_11_11_10(
                    &mut region,
                    val_of_sprdd_forms.map(spreaded_sum),
                    even_or_odd,
                    0,
                )
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
}

// A ⊕ B ⊕ C
//
//     1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
//        Evn: (Evn.11a, Evn.11b, Evn.10) Odd: (Odd.11a, Odd.11b, Odd.10)
//
//     2) asserting the 11-11-10 decomposition identity for Evn: 2^21 * Evn.11a
//        + 2^10 * Evn.11b + Evn.10 = Evn
//
//     3) asserting the spreaded addition identity regarding the spreaded
//        values: (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) + 2 * (4^21 *
//        ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10) = ~A + ~B + ~C
//
//     The output is Evn.
//
//     | T0 |    A0   |     A1   | T1 |    A2   |    A3    |  A4 | A5 | A6 | A7 |
//     |----|---------|----------|----|---------|----------|-----|----|----|----|
//     | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn | ~A | ~B | ~C |
//     | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     |    |    |    | <- q_spr_add, q_11_11_10
//     | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |    |    |    |
//
//
//     A ⊕ B ⊕ 0
//
//     | T0 |    A0   |     A1   | T1 |    A2   |    A3    |  A4 | A5 | A6 | A7 |
//     |----|---------|----------|----|---------|----------|-----|----|----|----|
//     | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn | ~A | ~B | ~0 |
//     | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     |    |    |    | <- q_spr_add, q_11_11_10
//     | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |    |    |    |
//
//
//     prepare_spreaded(A): A ⊕ 0 ⊕ 0
//
//     | T0 |    A0   |     A1   | T1 |   A2   |   A3   |  A4 | A5 | A6 | A7 |
//     |----|---------|----------|----|--------|--------|-----|----|----|----|
//     | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   |  A  | ~A | ~0 | ~0 |
//     | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   |     |    |    |    | <- q_spr_add, q_11_11_10
//     | 10 | Evn.11a | ~Evn.11a | 10 |   0    |   ~0   |     |    |    |    |
//
//
//     (A ∧ B) ∨ (¬A ∧ C) = (A ∧ B) ⊕ (¬A ∧ C) = Ch(A, B, C)
//
//     1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd,
//        for both (~A + ~B) and (~(¬A) + ~C): Evn_AB: (Evn_AB.11a, Evn_AB.11b,
//        Evn_AB.10) Odd_AB: (Odd_AB.11a, Odd_AB.11b, Odd_AB.10)
//
//             Evn_nAC: (Evn_nAC.11a, Evn_nAC.11b, Evn_nAC.10)
//             Odd_nAC: (Odd_nAC.11a, Odd_nAC.11b, Odd_nAC.10)
//
//     2) asserting the 11-11-10 decomposition identity for Odd_AB and Odd_nAC:
//        2^21 * Odd_AB.11a + 2^10 * Odd_AB.11b + Odd_AB.10 = Odd_AB
//
//             2^21 * Odd_nAC.11a + 2^10 * Odd_nAC.11b + Odd_nAC.10
//         = Odd_nAC
//
//     3) asserting the spreaded addition identity for (~A + ~B) and (~(¬A) +
//        ~C): (4^21 * ~Evn_AB.11a + 4^10 * ~Evn_AB.11b + ~Evn_AB.10) + 2 *
//        (4^21 * ~Odd_AB.11a + 4^10 * ~Odd_AB.11b + ~Odd_AB.10) = ~A + ~B
//
//             (4^21 * ~Evn_nAC.11a + 4^10 * ~Evn_nAC.11b + ~Evn_nAC.10) +
//         2 * (4^21 * ~Odd_nAC.11a + 4^10 * ~Odd_nAC.11b + ~Odd_nAC.10)
//             = ~(¬A) + ~C
//
//     4) asserting the following two addition identities: Ret = Odd_AB +
//        Odd_nAC MASK_EVN_64 = ~A + ~(¬A)
//
//     The output is Ret.
//
//     | T0 |      A0     |      A1      | T1 |      A2     |      A3      |    A4   |    A5   |      A6     | A7 |
//     |----|-------------|--------------|----|-------------|--------------|---------|---------|-------------|----|
//     | 11 |  Odd_AB.11a |  ~Odd_AB.11a | 11 |  Evn_AB.11a |  ~Evn_AB.11a | Odd_AB  |   ~A    |      ~B     | ~0 |
//     | 11 |  Odd_AB.11b |  ~Odd_AB.11b | 11 |  Evn_AB.11b |  ~Evn_AB.11b | Odd_AB  | Odd_nAC |     Ret     |    | <- q_spr_add, q_11_11_10, q_add
//     | 10 |  Odd_AB.10  |   ~Odd_AB.10 | 10 |  Evn_AB.10  |  ~Evn_AB.10  |         |         |             |    |
//     | 11 | Odd_nAC.11a | ~Odd_nAC.11a | 11 | Evn_nAC.11a | ~Evn_nAC.11a | Odd_nAC |  ~(¬A)  |      ~C     | ~0 |
//     | 11 | Odd_nAC.11b | ~Odd_nAC.11b | 11 | Evn_nAC.11b | ~Evn_nAC.11b |   ~A    |  ~(¬A)  | MASK_EVN_64 |    | <- q_spr_add, q_11_11_10, q_add
//     | 10 | Odd_nAC.10  |  ~Odd_nAC.10 | 10 | Evn_nAC.10  | ~Evn_nAC.10  |         |         |             |    |
//
//
//     A ∧ B
//
//     1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
//        Evn: (Evn.11a, Evn.11b, Evn.10) Odd: (Odd.11a, Odd.11b, Odd.10)
//
//     2) asserting the 11-11-10 decomposition identity for Odd: 2^21 * Odd.11a
//        + 2^10 * Odd.11b + Odd.10 = Odd
//
//     3) asserting the spreaded addition identity regarding the spreaded
//        values: (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) + 2 * (4^21 *
//        ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10) = ~A + ~B
//
//     The output is Odd.
//
//     | T0 |    A0   |     A1   | T1 |    A2   |    A3     |  A4 | A5 | A6 | A7 |
//     |----|---------|----------|----|---------|-----------|-----|----|----|----|
//     | 11 | Odd.11a | ~Odd.11a | 11 | Evn.11a | ~Evn.11a  | Odd | ~A | ~B | ~0 |
//     | 11 | Odd.11b | ~Odd.11b | 11 | Evn.11b | ~Evn.11b  |     |    |    |    | <- q_spr_add, q_11_11_10
//     | 10 | Odd.10  | ~Odd.10  | 10 | Evn.10  | ~Evn.10   |     |    |    |    |
//
//     rotate_left(A, s)
//
//     |  T0 |  A0  |  A1   |  T1 |   A2  |   A3   |   A4  | A5 | A6 | A7 |
//     |-----|------|-------|-----|-------|--------|-------|----|----|----|
//     | T.1 |  A.1 | ~A.1  | T.3 |  A.3  |  ~A.3  |   A   |    |    |    |
//     | T.2 |  A.2 | ~A.2  | T.4 |  A.4  |  ~A.4  | Rot(A)|    |    |    | <- q_rol
//
//     A ⊞ B ⊞ C ⊞ D
//
//     |  T0 |   A0  |   A1   |  T1 |   A2  |   A3   |   A4  | A5 | A6 | A7 |
//     |-----|-------|--------|-----|-------|--------|-------|----|----|----|
//     |  2  | carry | ~carry |  0  |   0   |   ~0   |   A   |  B |  C |  D | <- q_mod_add

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
        testing_utils::FromScratch,
    };

    struct TestCircuit<F: PrimeField> {
        inputs: [F; 5],
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

            let inputs: Vec<AssignedNative<F>> =
                ripemd160_chip.native_gadget.assign_many_fixed(&mut layouter, &self.inputs)?;

            let assigned_inputs: Vec<AssignedWord<F>> =
                inputs.into_iter().map(AssignedWord).collect();

            // Iterate over inputs and apply the spread operation
            for (assigned_input, &input) in assigned_inputs.iter().zip(self.inputs.iter()) {
                let res = ripemd160_chip.prepare_spreaded(&mut layouter, assigned_input)?;
                res.0
                    .value()
                    .assert_if_known(|res| **res == u64_to_fe(spread(fe_to_u32(input))))
            }

            Ok(())
        }
    }

    #[test]
    fn test_prepare_spreaded() {
        let circuit = TestCircuit {
            inputs: [
                F::from(0u64),
                F::from(1u64),
                F::from(42u64),
                F::from(255u64),
                F::from(1023u64),
            ],
        };

        let prover = match MockProver::<F>::run(16, &circuit, vec![vec![]]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
