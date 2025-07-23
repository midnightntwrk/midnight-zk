use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use crate::{
    field::NativeChip,
    hash::new_sha256::{
        gates::{decompose_12_12_8, major, Sigma_0},
        types::{AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded, LimbsOfA},
        utils::{
            get_even_odd_bits, iter_of_table, spread, spreaded_Sigma_0, spreaded_maj,
            u32_in_be_limbs, u32_to_fe, u64_to_fe,
        },
    },
    utils::{util::fe_to_u64, ComposableChip},
};

const NB_SHA256_ADVICE_COLS: usize = 7;
const NB_SHA256_FIXED_COLS: usize = 2;

/// Tag for the even and odd 12-12-8 decompositions.
enum Parity {
    Even,
    Odd,
}

/// Plain-Spreaded lookup table.
#[derive(Clone, Debug)]
pub(super) struct SpreadedTable {
    table_tag: TableColumn,
    table_plain: TableColumn,
    table_spreaded: TableColumn,
}

/// Configuration of Sha256Chip.
#[derive(Clone, Debug)]
pub struct Sha256Config {
    advice_cols: [Column<Advice>; NB_SHA256_ADVICE_COLS],
    fixed_cols: [Column<Fixed>; NB_SHA256_FIXED_COLS],
    s_Sigma_0: Selector,
    s_12_12_8: Selector,
    s_lookup: Selector,
    s_maj: Selector,
    table: SpreadedTable,
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
        let advice_cols = shared_res.0.clone();
        let fixed_cols = shared_res.1.clone();
        let table_tag = meta.lookup_table_column();
        let table_plain = meta.lookup_table_column();
        let table_spreaded = meta.lookup_table_column();

        let s_Sigma_0 = meta.selector();
        let s_12_12_8 = meta.selector();
        let s_maj = meta.selector();
        let s_lookup = meta.complex_selector();

        (0..2).into_iter().for_each(|idx| {
            meta.lookup("plain-spreaded lookup", |meta| {
                let s_lookup = meta.query_selector(s_lookup);

                let tag = meta.query_fixed(fixed_cols[idx], Rotation(0));
                let plain = meta.query_advice(advice_cols[2 * idx], Rotation(0));
                let spreaded = meta.query_advice(advice_cols[2 * idx + 1], Rotation(0));

                vec![
                    (s_lookup.clone() * tag, table_tag),
                    (s_lookup.clone() * plain, table_plain),
                    (s_lookup * spreaded, table_spreaded),
                ]
            });
        });

        meta.create_gate("12-12-8 decomposition", |meta| {
            let s_12_12_8 = meta.query_selector(s_12_12_8);

            let limb_12a = meta.query_advice(advice_cols[0], Rotation(0));
            let limb_12b = meta.query_advice(advice_cols[0], Rotation(1));
            let limb_8 = meta.query_advice(advice_cols[0], Rotation(2));
            let output = meta.query_advice(advice_cols[4], Rotation(0));

            decompose_12_12_8(s_12_12_8, [limb_12a, limb_12b, limb_8], output)
        });

        meta.create_gate("spreaded Σ₀(A)", |meta| {
            let s_Sigma_0 = meta.query_selector(s_Sigma_0);

            let spreaded_a_10 = meta.query_advice(advice_cols[5], Rotation(0));
            let spreaded_a_9 = meta.query_advice(advice_cols[6], Rotation(0));
            let spreaded_a_11 = meta.query_advice(advice_cols[5], Rotation(1));
            let spreaded_a_2 = meta.query_advice(advice_cols[6], Rotation(1));
            let spreaded_even_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let spreaded_even_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let spreaded_even_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let spreaded_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let spreaded_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let spreaded_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Sigma_0(
                s_Sigma_0,
                [spreaded_a_10, spreaded_a_9, spreaded_a_11, spreaded_a_2],
                [spreaded_even_12a, spreaded_even_12b, spreaded_even_8],
                [spreaded_odd_12a, spreaded_odd_12b, spreaded_odd_8],
            )
        });

        meta.create_gate("spreaded Maj(A, B, C)", |meta| {
            let s_maj = meta.query_selector(s_maj);

            let spreaded_a = meta.query_advice(advice_cols[5], Rotation(0));
            let spreaded_b = meta.query_advice(advice_cols[6], Rotation(0));
            let spreaded_c = meta.query_advice(advice_cols[5], Rotation(1));

            let spreaded_even_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let spreaded_even_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let spreaded_even_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let spreaded_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let spreaded_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let spreaded_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            major(
                s_maj,
                [spreaded_a, spreaded_b, spreaded_c],
                [spreaded_even_12a, spreaded_even_12b, spreaded_even_8],
                [spreaded_odd_12a, spreaded_odd_12b, spreaded_odd_8],
            )
        });

        Sha256Config {
            advice_cols,
            fixed_cols,
            s_Sigma_0,
            s_12_12_8,
            s_maj,
            s_lookup,
            table: SpreadedTable {
                table_tag,
                table_plain,
                table_spreaded,
            },
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let SpreadedTable {
            table_tag,
            table_plain,
            table_spreaded,
        } = self.config().table;

        layouter.assign_table(
            || "spreaded table",
            |mut table| {
                // Generates the lookup table lazily as we only need it during keygen.
                let iter_of_table = iter_of_table::<F>();

                for (index, triple) in iter_of_table.into_iter().enumerate() {
                    table.assign_cell(|| "tag", table_tag, index, || Value::known(triple.0))?;
                    table.assign_cell(|| "plain", table_plain, index, || Value::known(triple.1))?;
                    table.assign_cell(
                        || "spreaded",
                        table_spreaded,
                        index,
                        || Value::known(triple.2),
                    )?;
                }
                Ok(())
            },
        )
    }
}

impl<F: PrimeField> Sha256Chip<F> {
    /// Computes Σ₀(A).
    pub(super) fn compute_Sigma_0(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &LimbsOfA<F>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We need to compute:
             A >>> 2 :       (   A.2  ||  A.10  ||   A.9  ||  A.11  )
          ⊕ A >>> 13 :    ⊕  (  A.11  ||   A.2  ||  A.10  ||   A.9  )
          ⊕ A >>> 22 :    ⊕  (   A.9  ||  A.11  ||   A.2  ||  A.10  )

        which can be achieved by
        1) applying plain-spreaded lookup on 12-12-8 limbs of Even and Odd:
            Even: (Even.12a, Even.12b, Even.8)
             Odd: ( Odd.12a,  Odd.12b,  Odd.8)
        2) asserting the 12-12-8 decomposition identity for Even:
              2^20 * Even.12a + 2^8 * Even.12b + Even.8
            = Even
        3) asserting the s_Sigma_0 identity regarding the spreaded values:
              (4^20 * ~Even.12a + 4^8 * ~Even.12b + ~Even.8) +
          2 * (4^20 *  ~Odd.12a + 4^8 *  ~Odd.12b +  ~Odd.8)
             = 4^30 *  ~A.2  +  4^20 * ~A.10  +  4^11 * ~A.9  +  ~A.11
             + 4^21 * ~A.11  +  4^19 *  ~A.2  +  4^9 * ~A.10  +   ~A.9
             + 4^23 *  ~A.9  +  4^12 * ~A.11  +  4^10 * ~A.2  +  ~A.10

        The output is Even.

        We distribute these values in the PLONK table as follows.

        | T_0 |    A_0   |    A_1    | T_1 |   A_2   |    A_3   |  A_4  |  A_5  |  A_6  |
        |-----|----------|-----------|-----|---------|----------|-------|-------|-------|
        |  12 | Even.12a | ~Even.12a |  12 | Odd.12a | ~Odd.12a | Even  | ~A.10 |  ~A.9 |
        |  12 | Even.12b | ~Even.12b |  12 | Odd.12b | ~Odd.12b |       | ~A.11 |  ~A.2 |
        |   8 |   Even.8 |   ~Even.8 |   8 |   Odd.8 |   ~Odd.8 |       |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₀(A)",
            |mut region| {
                self.config().s_Sigma_0.enable(&mut region, 0)?;

                // Copy and assign the input.
                (a.spreaded_limb_10.0).copy_advice(|| "~A.10", &mut region, adv_cols[5], 0)?;
                (a.spreaded_limb_9.0).copy_advice(|| "~A.9", &mut region, adv_cols[6], 0)?;
                (a.spreaded_limb_11.0).copy_advice(|| "~A.11", &mut region, adv_cols[5], 1)?;
                (a.spreaded_limb_2.0).copy_advice(|| "~A.2", &mut region, adv_cols[6], 1)?;

                // Compute the spreaded Σ₀(A) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the s_12_12_8 selector
                // for the even part and s_lookup selector for the related rows.
                let val_of_spreaded_limbs: Value<[u64; 4]> = Value::from_iter([
                    a.spreaded_limb_10.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_9.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_11.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_2.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                let (even_val, _odd_val) = self.assign_even_odd_12_12_8(
                    &mut region,
                    val_of_spreaded_limbs,
                    spreaded_Sigma_0,
                    Parity::Even,
                )?;

                // Return the 32 even bits as the result of Σ₀(A).
                region
                    .assign_advice(|| "Even", adv_cols[4], 0, || even_val.map(u32_to_fe))
                    .map(AssignedPlain)
            },
        )
    }

    /// Computes Maj(A, B, C)
    pub(super) fn compute_maj(
        &self,
        layouter: &mut impl Layouter<F>,
        spreaded_a: &AssignedSpreaded<F, 32>,
        spreaded_b: &AssignedSpreaded<F, 32>,
        spreaded_c: &AssignedSpreaded<F, 32>,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        /*
        We need to compute:
            Maj(A, B, C) = (A ∧ B) ⊕ (A ∧ C) ⊕ (B ∧ C)

        which can be achieved by
        1) applying plain-spreaded lookup on 12-12-8 limbs of Even and Odd:
            Even: (Even.12a, Even.12b, Even.8)
             Odd: ( Odd.12a,  Odd.12b,  Odd.8)
        2) asserting the 12-12-8 decomposition identity for Odd:
              2^20 * Odd.12a + 2^8 * Odd.12b + Odd.8
            = Odd
        3) asserting the s_maj identity regarding the spreaded values:
              (4^20 * ~Even.12a + 4^8 * ~Even.12b + ~Even.8)
          2 * (4^20 *  ~Odd.12a + 4^8 *  ~Odd.12b +  ~Odd.8)
             = ~A + ~B + ~C

        The output is Odd.

        We distribute these values in the PLONK table as follows.

        | T_0 |   A_0   |    A_1   | T_1 |    A_2   |    A_3    |  A_4  |  A_5  |  A_6  |
        |-----|---------|----------|-----|----------|-----------|-------|-------|-------|
        |  12 | Odd.12a | ~Odd.12a |  12 | Even.12a | ~Even.12a |  Odd  | ~A    | ~B    |
        |  12 | Odd.12b | ~Odd.12b |  12 | Even.12b | ~Even.12b |       | ~C    |       |
        |   8 | Odd.8   | ~Odd.8   |   8 | Even.2   | ~Even.8   |       |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Maj(A, B, C)",
            |mut region| {
                self.config().s_maj.enable(&mut region, 0)?;

                // Copy and assign the input.
                (spreaded_a.0).copy_advice(|| "~A", &mut region, adv_cols[5], 0)?;
                (spreaded_b.0).copy_advice(|| "~B", &mut region, adv_cols[6], 0)?;
                (spreaded_c.0).copy_advice(|| "~C", &mut region, adv_cols[5], 1)?;

                // Compute the spreaded Maj(A, B, C) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the s_12_12_8 selector
                // for the odd part and s_lookup selector for the related rows.
                let val_of_spreaded_forms: Value<[u64; 3]> = Value::from_iter([
                    spreaded_a.0.value().copied().map(fe_to_u64),
                    spreaded_b.0.value().copied().map(fe_to_u64),
                    spreaded_c.0.value().copied().map(fe_to_u64),
                ])
                .map(|spreaded_forms: Vec<u64>| spreaded_forms.try_into().unwrap());

                let (_even_val, odd_val) = self.assign_even_odd_12_12_8(
                    &mut region,
                    val_of_spreaded_forms,
                    spreaded_maj,
                    Parity::Odd,
                )?;

                // Return the 32 odd bits as the result of Maj(A, B, C).
                region
                    .assign_advice(|| "Odd", adv_cols[4], 0, || odd_val.map(u32_to_fe))
                    .map(AssignedPlain)
            },
        )
    }

    /// Given a plain value of bits L, assigns (tag, plain, spreaded) in the
    /// corresponding columns with the specified lookup index, and enables
    /// the lookup selector for this row.
    fn assign_spreaded_lookup<const L: usize>(
        &self,
        region: &mut Region<'_, F>,
        tag: usize,
        plain_val: Value<u32>,
        offset: usize,
        lookup_idx: usize,
    ) -> Result<AssignedPlainSpreaded<F, L>, Error> {
        self.config().s_lookup.enable(region, offset)?;

        let tag = F::from(tag as u64);
        let tag_col = self.config().fixed_cols[lookup_idx]; // 0 or 1
        let plain_col = self.config().advice_cols[2 * lookup_idx]; // 0 or 2
        let spreaded_col = self.config().advice_cols[2 * lookup_idx + 1]; // 1 or 3
        region.assign_fixed(|| "tag", tag_col, offset, || Value::known(tag))?;
        self.assign_plain_spreaded(region, plain_val, plain_col, spreaded_col, offset)
    }

    /// Assigns the plain-spreaded pair into the given columns with the
    /// specified offset.
    fn assign_plain_spreaded<const L: usize>(
        &self,
        region: &mut Region<'_, F>,
        plain_val: Value<u32>,
        plain_col: Column<Advice>,
        spreaded_col: Column<Advice>,
        offset: usize,
    ) -> Result<AssignedPlainSpreaded<F, L>, Error> {
        let plain = region
            .assign_advice(|| "plain", plain_col, offset, || plain_val.map(u32_to_fe))
            .map(AssignedPlain)?;
        let spreaded = region
            .assign_advice(
                || "spreaded",
                spreaded_col,
                offset,
                || plain_val.map(spread).map(u64_to_fe),
            )
            .map(AssignedSpreaded)?;
        Ok(AssignedPlainSpreaded { plain, spreaded })
    }

    /// Computes off-circuit the result of the operation (e.g spreaded-Σ₀),
    /// assigns the 12-12-8 limbs of its even and odd bits into the
    /// corresponding columns depending on whether the 12-12-8 decomposition
    /// is for the even or odd part, and enables the s_12_12_8 selector.
    fn assign_even_odd_12_12_8<const N: usize>(
        &self,
        region: &mut Region<'_, F>,
        val: Value<[u64; N]>,
        op: fn([u64; N]) -> u64,
        even_or_odd: Parity,
    ) -> Result<(Value<u32>, Value<u32>), Error> {
        self.config().s_12_12_8.enable(region, 0)?;

        // Compute off-circuit the result of the given operation, and derive its 32 even
        // and odd bits.
        let (even_val, odd_val) = val.map(op).map(get_even_odd_bits).unzip();
        /*
        Compute the 12-12-8 limbs of the even and odd bits, then assign to the circuit
        1) when the 12-12-8 decomposition is for the even part:

        | T_0 |    A_0   |     A_1   | T_1 |    A_2  |    A_3   |  A_4  |
        |-----|----------|-----------|-----|---------|----------|-------|
        |  12 | Even.12a | ~Even.12a |  12 | Odd.12a | ~Odd.12a | Even  |
        |  12 | Even.12b | ~Even.12b |  12 | Odd.12b | ~Odd.12b |
        |   8 | Even.8   | ~Even.8   |   8 | Odd.2   | ~Odd.8   |

        2) when the 12-12-8 decomposition is for the odd part:

        | T_0 |   A_0   |    A_1   | T_1 |    A_2   |    A_3    |  A_4  |
        |-----|---------|----------|-----|----------|-----------|-------|
        |  12 | Odd.12a | ~Odd.12a |  12 | Even.12a | ~Even.12a |  Odd  |
        |  12 | Odd.12b | ~Odd.12b |  12 | Even.12b | ~Even.12b |       |
        |   8 | Odd.8   | ~Odd.8   |   8 | Even.2   | ~Even.8   |       |
        */
        let [even_12a, even_12b, even_8] = even_val
            .map(|v| u32_in_be_limbs(v, [12, 12, 8]))
            .transpose_array();

        let [odd_12a, odd_12b, odd_8] = odd_val
            .map(|v| u32_in_be_limbs(v, [12, 12, 8]))
            .transpose_array();

        let idx = match even_or_odd {
            Parity::Even => 0usize,
            Parity::Odd => 1usize,
        };

        self.assign_spreaded_lookup::<12>(region, 12, even_12a, 0, idx)?; // 0 or 1
        self.assign_spreaded_lookup::<12>(region, 12, even_12b, 1, idx)?;
        self.assign_spreaded_lookup::<8>(region, 8, even_8, 2, idx)?;

        self.assign_spreaded_lookup::<12>(region, 12, odd_12a, 0, (idx + 1) % 2)?; // 1 or 0
        self.assign_spreaded_lookup::<12>(region, 12, odd_12b, 1, (idx + 1) % 2)?;
        self.assign_spreaded_lookup::<8>(region, 8, odd_8, 2, (idx + 1) % 2)?;

        Ok((even_val, odd_val))
    }
}
