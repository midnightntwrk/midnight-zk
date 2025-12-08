//! Implementation in-circuit of the RIPEMD-160 hash function.

use ff::PrimeField;
use midnight_proofs::{
    circuit::{Chip, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use crate::{
    field::{decomposition::chip::P2RDecompositionChip, NativeChip, NativeGadget},
    hash::ripemd160::utils::gen_spread_table,
    utils::ComposableChip,
};

/// Number of advice columns used by the identities of the RIPEMD160 chip.
pub const NB_RIPEMD160_ADVICE_COLS: usize = 8;

/// Number of fixed columns used by the identities of the RIPEMD160 chip.
pub const NB_RIPEMD160_FIXED_COLS: usize = 2;

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

        RipeMD160Config {
            advice_cols,
            fixed_cols,
            q_lookup,
            table,
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

/*
    A ⊕ B ⊕ C

    1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

    2) asserting the 11-11-10 decomposition identity for Evn:
            2^21 * Evn.11a + 2^10 * Evn.11b + Evn.10
        = Evn

    3) asserting the spreaded addition identity regarding the spreaded values:
            (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
        2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
            = ~A + ~B + ~C

    The output is Evn.

    | T0 |    A0   |     A1   | T1 |    A2   |    A3    |  A4 | A5 | A6 | A7 |
    |----|---------|----------|----|---------|----------|-----|----|----|----|
    | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn | ~A | ~B | ~C |
    | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     |    |    |    | <- q_spr_add, q_11_11_10
    | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |    |    |    |

*/

/*
    A ⊕ B ⊕ 0

    | T0 |    A0   |     A1   | T1 |    A2   |    A3    |  A4 | A5 | A6 | A7 |
    |----|---------|----------|----|---------|----------|-----|----|----|----|
    | 11 | Evn.11a | ~Evn.11a | 11 | Odd.11a | ~Odd.11a | Evn | ~A | ~B | ~0 |
    | 11 | Evn.11b | ~Evn.11b | 11 | Odd.11b | ~Odd.11b |     |    |    |    | <- q_spr_add, q_11_11_10
    | 10 | Evn.10  | ~Evn.10  | 10 | Odd.10  | ~Odd.10  |     |    |    |    |

*/

/*
    prepare_spreaded(A): A ⊕ 0 ⊕ 0

    | T0 |    A0   |     A1   | T1 |   A2   |   A3   |  A4 | A5 | A6 | A7 |
    |----|---------|----------|----|--------|--------|-----|----|----|----|
    | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   |  A  | ~A | ~0 | ~0 |
    | 11 | Evn.11a | ~Evn.11a | 11 |   0    |   ~0   |     |    |    |    | <- q_spr_add, q_11_11_10
    | 10 | Evn.11a | ~Evn.11a | 10 |   0    |   ~0   |     |    |    |    |

*/

/*
    (A ∧ B) ∨ (¬A ∧ C) = (A ∧ B) ⊕ (¬A ∧ C) = Ch(A, B, C)

    1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd,
        for both (~A + ~B) and (~(¬A) + ~C):
            Evn_AB: (Evn_AB.11a, Evn_AB.11b, Evn_AB.10)
            Odd_AB: (Odd_AB.11a, Odd_AB.11b, Odd_AB.10)

            Evn_nAC: (Evn_nAC.11a, Evn_nAC.11b, Evn_nAC.10)
            Odd_nAC: (Odd_nAC.11a, Odd_nAC.11b, Odd_nAC.10)

    2) asserting the 11-11-10 decomposition identity for Odd_AB and Odd_nAC:
            2^21 * Odd_AB.11a + 2^10 * Odd_AB.11b + Odd_AB.10
        = Odd_AB

            2^21 * Odd_nAC.11a + 2^10 * Odd_nAC.11b + Odd_nAC.10
        = Odd_nAC

    3) asserting the spreaded addition identity for (~A + ~B) and (~(¬A) + ~C):
            (4^21 * ~Evn_AB.11a + 4^10 * ~Evn_AB.11b + ~Evn_AB.10) +
        2 * (4^21 * ~Odd_AB.11a + 4^10 * ~Odd_AB.11b + ~Odd_AB.10)
            = ~A + ~B

            (4^21 * ~Evn_nAC.11a + 4^10 * ~Evn_nAC.11b + ~Evn_nAC.10) +
        2 * (4^21 * ~Odd_nAC.11a + 4^10 * ~Odd_nAC.11b + ~Odd_nAC.10)
            = ~(¬A) + ~C

    4) asserting the following two addition identities:
                Ret = Odd_AB + Odd_nAC
        MASK_EVN_64 = ~A + ~(¬A)

    The output is Ret.

    | T0 |      A0     |      A1      | T1 |      A2     |      A3      |    A4   |    A5   |      A6     | A7 |
    |----|-------------|--------------|----|-------------|--------------|---------|---------|-------------|----|
    | 11 |  Odd_AB.11a |  ~Odd_AB.11a | 11 |  Evn_AB.11a |  ~Evn_AB.11a | Odd_AB  |   ~A    |      ~B     | ~0 |
    | 11 |  Odd_AB.11b |  ~Odd_AB.11b | 11 |  Evn_AB.11b |  ~Evn_AB.11b | Odd_AB  | Odd_nAC |     Ret     |    | <- q_spr_add, q_11_11_10, q_add
    | 10 |  Odd_AB.10  |   ~Odd_AB.10 | 10 |  Evn_AB.10  |  ~Evn_AB.10  |         |         |             |    |
    | 11 | Odd_nAC.11a | ~Odd_nAC.11a | 11 | Evn_nAC.11a | ~Evn_nAC.11a | Odd_nAC |  ~(¬A)  |      ~C     | ~0 |
    | 11 | Odd_nAC.11b | ~Odd_nAC.11b | 11 | Evn_nAC.11b | ~Evn_nAC.11b |   ~A    |  ~(¬A)  | MASK_EVN_64 |    | <- q_spr_add, q_11_11_10, q_add
    | 10 | Odd_nAC.10  |  ~Odd_nAC.10 | 10 | Evn_nAC.10  | ~Evn_nAC.10  |         |         |             |    |

*/

/*
    A ∧ B

    1) applying the plain-spreaded lookup on 11-11-10 limbs of Evn and Odd:
             Evn: (Evn.11a, Evn.11b, Evn.10)
             Odd: (Odd.11a, Odd.11b, Odd.10)

    2) asserting the 11-11-10 decomposition identity for Odd:
            2^21 * Odd.11a + 2^10 * Odd.11b + Odd.10
        = Odd

    3) asserting the spreaded addition identity regarding the spreaded values:
            (4^21 * ~Evn.11a + 4^10 * ~Evn.11b + ~Evn.10) +
        2 * (4^21 * ~Odd.11a + 4^10 * ~Odd.11b + ~Odd.10)
            = ~A + ~B

    The output is Odd.

    | T0 |    A0   |     A1   | T1 |    A2   |    A3     |  A4 | A5 | A6 | A7 |
    |----|---------|----------|----|---------|-----------|-----|----|----|----|
    | 11 | Odd.11a | ~Odd.11a | 11 | Evn.11a | ~Evn.11a  | Odd | ~A | ~B | ~0 |
    | 11 | Odd.11b | ~Odd.11b | 11 | Evn.11b | ~Evn.11b  |     |    |    |    | <- q_spr_add, q_11_11_10
    | 10 | Odd.10  | ~Odd.10  | 10 | Evn.10  | ~Evn.10   |     |    |    |    |

*/

/*
    rotate_left(A, s)

    |  T0 |  A0  |  A1   |  T1 |   A2  |   A3   |   A4  | A5 | A6 | A7 |
    |-----|------|-------|-----|-------|--------|-------|----|----|----|
    | T.1 |  A.1 | ~A.1  | T.3 |  A.3  |  ~A.3  |   A   |    |    |    |
    | T.2 |  A.2 | ~A.2  | T.4 |  A.4  |  ~A.4  | Rot(A)|    |    |    | <- q_rol

*/

/*
    A ⊞ B ⊞ C ⊞ D

    |  T0 |   A0  |   A1   |  T1 |   A2  |   A3   |   A4  | A5 | A6 | A7 |
    |-----|-------|--------|-----|-------|--------|-------|----|----|----|
    |  2  | carry | ~carry |  0  |   0   |   ~0   |   A   |  B |  C |  D | <- q_mod_add

*/
