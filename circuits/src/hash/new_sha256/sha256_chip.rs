use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use crate::{
    field::NativeChip,
    hash::new_sha256::{
        gates::{decompose_12_12_8_gate, maj_gate, Sigma_0_gate},
        types::{AssignedPlain, AssignedPlainSpreaded, AssignedSpreaded, LimbsOfA},
        utils::{
            gen_spread_table, get_even_odd_bits, spread, spreaded_Sigma_0, spreaded_maj,
            u32_in_be_limbs, u32_to_fe, u64_to_fe,
        },
    },
    utils::{util::fe_to_u64, ComposableChip},
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
    q_12_12_8: Selector,
    q_lookup: Selector,
    q_maj: Selector,
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
        let advice_cols = shared_res.0.clone();
        let fixed_cols = shared_res.1.clone();
        let nbits_tab = meta.lookup_table_column();
        let plain_tab = meta.lookup_table_column();
        let sprdd_tab = meta.lookup_table_column();

        let q_Sigma_0 = meta.selector();
        let q_12_12_8 = meta.selector();
        let q_maj = meta.selector();
        let q_lookup = meta.complex_selector();

        (0..2).into_iter().for_each(|idx| {
            meta.lookup("plain-spreaded lookup", |meta| {
                let q_lookup = meta.query_selector(q_lookup);

                let tag = meta.query_fixed(fixed_cols[idx], Rotation(0));
                let plain = meta.query_advice(advice_cols[2 * idx], Rotation(0));
                let spreaded = meta.query_advice(advice_cols[2 * idx + 1], Rotation(0));

                vec![
                    (q_lookup.clone() * tag, nbits_tab),
                    (q_lookup.clone() * plain, plain_tab),
                    (q_lookup * spreaded, sprdd_tab),
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

        meta.create_gate("Σ₀(A)", |meta| {
            let q_Sigma_0 = meta.query_selector(q_Sigma_0);

            let spreaded_a_10 = meta.query_advice(advice_cols[5], Rotation(0));
            let spreaded_a_9 = meta.query_advice(advice_cols[6], Rotation(0));
            let spreaded_a_11 = meta.query_advice(advice_cols[5], Rotation(1));
            let spreaded_a_2 = meta.query_advice(advice_cols[6], Rotation(1));
            let spreaded_evn_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let spreaded_evn_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let spreaded_evn_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let spreaded_odd_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let spreaded_odd_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let spreaded_odd_8 = meta.query_advice(advice_cols[3], Rotation(2));

            Sigma_0_gate(
                q_Sigma_0,
                [spreaded_a_10, spreaded_a_9, spreaded_a_11, spreaded_a_2],
                [spreaded_evn_12a, spreaded_evn_12b, spreaded_evn_8],
                [spreaded_odd_12a, spreaded_odd_12b, spreaded_odd_8],
            )
        });

        meta.create_gate("Maj(A, B, C)", |meta| {
            let q_maj = meta.query_selector(q_maj);

            let spreaded_a = meta.query_advice(advice_cols[5], Rotation(0));
            let spreaded_b = meta.query_advice(advice_cols[6], Rotation(0));
            let spreaded_c = meta.query_advice(advice_cols[5], Rotation(1));
            let spreaded_odd_12a = meta.query_advice(advice_cols[1], Rotation(0));
            let spreaded_odd_12b = meta.query_advice(advice_cols[1], Rotation(1));
            let spreaded_odd_8 = meta.query_advice(advice_cols[1], Rotation(2));
            let spreaded_evn_12a = meta.query_advice(advice_cols[3], Rotation(0));
            let spreaded_evn_12b = meta.query_advice(advice_cols[3], Rotation(1));
            let spreaded_evn_8 = meta.query_advice(advice_cols[3], Rotation(2));

            maj_gate(
                q_maj,
                [spreaded_a, spreaded_b, spreaded_c],
                [spreaded_evn_12a, spreaded_evn_12b, spreaded_evn_8],
                [spreaded_odd_12a, spreaded_odd_12b, spreaded_odd_8],
            )
        });

        Sha256Config {
            advice_cols,
            fixed_cols,
            q_Sigma_0,
            q_12_12_8,
            q_maj,
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
             A >>> 2 :  (   A.2  ||  A.10  ||   A.9  ||  A.11  )
          ⊕ A >>> 13 :  (  A.11  ||   A.2  ||  A.10  ||   A.9  )
          ⊕ A >>> 22 :  (   A.9  ||  A.11  ||   A.2  ||  A.10  )

        which can be achieved by

        1) applying plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
             Evn: (Evn.12a, Evn.12b, Evn.8)
             Odd: (Odd.12a, Odd.12b, Odd.8)

        2) asserting the 12-12-8 decomposition identity for Evn:
              2^20 * Evn.12a + 2^8 * Evn.12b + Evn.8
            = Evn

        3) asserting the Sigma_0 identity regarding the spreaded values:
              (4^20 * ~Evn.12a + 4^8 * ~Evn.12b + ~Evn.8) +
          2 * (4^20 * ~Odd.12a + 4^8 * ~Odd.12b + ~Odd.8)
             = 4^30 *  ~A.2  +  4^20 * ~A.10  +  4^11 * ~A.9  +  ~A.11
             + 4^21 * ~A.11  +  4^19 *  ~A.2  +  4^9 * ~A.10  +   ~A.9
             + 4^23 *  ~A.9  +  4^12 * ~A.11  +  4^10 * ~A.2  +  ~A.10

        The output is Evn.

        We distribute these values in the PLONK table as follows.

        | T_0 |    A_0  |    A_1   | T_1 |   A_2   |    A_3   |  A_4  |  A_5  |  A_6  |
        |-----|---------|----------|-----|---------|----------|-------|-------|-------|
        |  12 | Evn.12a | ~Evn.12a |  12 | Odd.12a | ~Odd.12a |  Evn  | ~A.10 |  ~A.9 |
        |  12 | Evn.12b | ~Evn.12b |  12 | Odd.12b | ~Odd.12b |       | ~A.11 |  ~A.2 |
        |   8 |   Evn.8 |   ~Evn.8 |   8 |   Odd.8 |   ~Odd.8 |       |       |       |
        */

        let adv_cols = self.config().advice_cols;

        layouter.assign_region(
            || "Σ₀(A)",
            |mut region| {
                self.config().q_Sigma_0.enable(&mut region, 0)?;

                // Copy and assign the input.
                (a.spreaded_limb_10.0).copy_advice(|| "~A.10", &mut region, adv_cols[5], 0)?;
                (a.spreaded_limb_9.0).copy_advice(|| "~A.9", &mut region, adv_cols[6], 0)?;
                (a.spreaded_limb_11.0).copy_advice(|| "~A.11", &mut region, adv_cols[5], 1)?;
                (a.spreaded_limb_2.0).copy_advice(|| "~A.2", &mut region, adv_cols[6], 1)?;

                // Compute the spreaded Σ₀(A) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the q_12_12_8 selector
                // for the even part and q_lookup selector for the related rows, return the
                // assigned 32 even bits.
                let val_of_spreaded_limbs: Value<[u64; 4]> = Value::from_iter([
                    a.spreaded_limb_10.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_9.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_11.0.value().copied().map(fe_to_u64),
                    a.spreaded_limb_2.0.value().copied().map(fe_to_u64),
                ])
                .map(|limbs: Vec<u64>| limbs.try_into().unwrap());

                self.assign_spreaded_12_12_8(
                    &mut region,
                    val_of_spreaded_limbs.map(spreaded_Sigma_0),
                    Parity::Evn,
                )
            },
        )
    }

    /// Computes Maj(A, B, C)
    pub(super) fn maj(
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

        1) applying plain-spreaded lookup on 12-12-8 limbs of Evn and Odd:
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
                (spreaded_a.0).copy_advice(|| "~A", &mut region, adv_cols[5], 0)?;
                (spreaded_b.0).copy_advice(|| "~B", &mut region, adv_cols[6], 0)?;
                (spreaded_c.0).copy_advice(|| "~C", &mut region, adv_cols[5], 1)?;

                // Compute the spreaded Maj(A, B, C) off-circuit, assign the 12-12-8 limbs
                // of its even and odd bits into the circuit, enable the q_12_12_8 selector
                // for the odd part and q_lookup selector for the related rows, return the
                // assigned 32 odd bits.
                let val_of_spreaded_forms: Value<[u64; 3]> = Value::from_iter([
                    spreaded_a.0.value().copied().map(fe_to_u64),
                    spreaded_b.0.value().copied().map(fe_to_u64),
                    spreaded_c.0.value().copied().map(fe_to_u64),
                ])
                .map(|spreaded_forms: Vec<u64>| spreaded_forms.try_into().unwrap());

                self.assign_spreaded_12_12_8(
                    &mut region,
                    val_of_spreaded_forms.map(spreaded_maj),
                    Parity::Odd,
                )
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
    /// If `lookup_idx = 0`, the lookup on columns (T_1, A_2, A_3) will be used.
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

        let tag_col = self.config().fixed_cols[lookup_idx]; // 0 or 1
        let plain_col = self.config().advice_cols[2 * lookup_idx]; // 0 or 2
        let spreaded_col = self.config().advice_cols[2 * lookup_idx + 1]; // 1 or 3

        let nbits_val = Value::known(F::from(L as u64));
        let sprdd_val = plain_val.map(spread).map(u64_to_fe);
        let plain_val = plain_val.map(u32_to_fe);

        region.assign_fixed(|| "nbits", tag_col, offset, || nbits_val)?;
        let plain = region.assign_advice(|| "plain", plain_col, offset, || plain_val)?;
        let spreaded = region.assign_advice(|| "sprdd", spreaded_col, offset, || sprdd_val)?;

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
    fn assign_spreaded_12_12_8(
        &self,
        region: &mut Region<'_, F>,
        value: Value<u64>,
        even_or_odd: Parity,
    ) -> Result<AssignedPlain<F, 32>, Error> {
        self.config().q_12_12_8.enable(region, 0)?;

        let (evn_val, odd_val) = value.map(get_even_odd_bits).unzip();

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

        self.assign_plain_and_spreaded::<12>(region, evn_12a, 0, idx)?;
        self.assign_plain_and_spreaded::<12>(region, evn_12b, 1, idx)?;
        self.assign_plain_and_spreaded::<8>(region, evn_8, 2, idx)?;

        self.assign_plain_and_spreaded::<12>(region, odd_12a, 0, 1 - idx)?;
        self.assign_plain_and_spreaded::<12>(region, odd_12b, 1, 1 - idx)?;
        self.assign_plain_and_spreaded::<8>(region, odd_8, 2, 1 - idx)?;

        let out_col = self.config().advice_cols[4];
        match even_or_odd {
            Parity::Evn => region.assign_advice(|| "Evn", out_col, 0, || evn_val.map(u32_to_fe)),
            Parity::Odd => region.assign_advice(|| "Odd", out_col, 0, || odd_val.map(u32_to_fe)),
        }
        .map(AssignedPlain)
    }
}
