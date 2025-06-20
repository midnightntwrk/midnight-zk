use ff::PrimeField;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::Error,
};

use super::{
    super::{RoundWord, StateWord},
    compression_util::*,
    CompressionConfig, RoundWordDense, State,
};
use crate::hash::sha256::{table11::spread_table::PostponedSpreadVar, IV};

impl CompressionConfig {
    #[allow(clippy::many_single_char_names)]
    pub fn initialize_iv<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<State<F>, Error> {
        let a_7 = self.extras[3];

        // Decompose E into (6, 5, 14, 7)-bit chunks
        let e = self.decompose_iv_e(region, postponed)?;

        // Decompose F, G
        let f = self.decompose_iv_f(region, postponed)?;
        let g = self.decompose_iv_g(region, postponed)?;

        // Assign H
        let h = IV[7];
        let h_row = get_h_row(RoundIdx::Init);
        let assigned_h =
            self.assign_word_halves_dense_fixed(region, h_row, a_7, h_row + 1, a_7, h)?;

        // Decompose A into (2, 11, 9, 10)-bit chunks
        let a = self.decompose_iv_a(region, postponed)?;

        // Decompose B, C
        let b = self.decompose_iv_b(region, postponed)?;
        let c = self.decompose_iv_c(region, postponed)?;

        // Assign D
        let d = IV[3];
        let d_row = get_d_row(RoundIdx::Init);
        let assigned_d =
            self.assign_word_halves_dense_fixed(region, d_row, a_7, d_row + 1, a_7, d)?;

        Ok(State::new(
            StateWord::A(a),
            StateWord::B(b),
            StateWord::C(c),
            StateWord::D(assigned_d),
            StateWord::E(e),
            StateWord::F(f),
            StateWord::G(g),
            StateWord::H(assigned_h),
        ))
    }

    #[allow(clippy::many_single_char_names)]
    pub fn initialize_state<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        state: State<F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<State<F>, Error> {
        let a_7 = self.extras[3];
        let (a, b, c, d, e, f, g, h) = match_state(state);

        // Decompose E into (6, 5, 14, 7)-bit chunks
        let e = self.decompose_e(region, RoundIdx::Init, &e.dense_halves, postponed)?;

        // Decompose F, G
        let f = self.decompose_f(region, InitialRound, &f.dense_halves, postponed)?;
        let g = self.decompose_g(region, InitialRound, &g.dense_halves, postponed)?;

        // Assign H
        let h_value = h.value();
        let h_row = get_h_row(RoundIdx::Init);
        let assigned_h =
            self.assign_word_halves_dense(region, h_row, a_7, h_row + 1, a_7, h_value)?;
        region.constrain_equal(h.0.cell(), assigned_h.0.cell())?;
        region.constrain_equal(h.1.cell(), assigned_h.1.cell())?;

        // Decompose A into (2, 11, 9, 10)-bit chunks
        let a = self.decompose_a(region, RoundIdx::Init, &a.dense_halves, postponed)?;

        // Decompose B, C
        let b = self.decompose_b(region, InitialRound, &b.dense_halves, postponed)?;
        let c = self.decompose_c(region, InitialRound, &c.dense_halves, postponed)?;

        // Assign D
        let d_value = d.value();
        let d_row = get_d_row(RoundIdx::Init);
        let assigned_d =
            self.assign_word_halves_dense(region, d_row, a_7, d_row + 1, a_7, d_value)?;
        region.constrain_equal(d.0.cell(), assigned_d.0.cell())?;
        region.constrain_equal(d.1.cell(), assigned_d.1.cell())?;

        Ok(State::new(
            StateWord::A(a),
            StateWord::B(b),
            StateWord::C(c),
            StateWord::D(d),
            StateWord::E(e),
            StateWord::F(f),
            StateWord::G(g),
            StateWord::H(h),
        ))
    }

    fn decompose_iv_b<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_b_row(InitialRound);

        let b = IV[1];
        let (dense_halves, spread_halves) = self.assign_word_halves_fixed(region, row, b)?;
        self.decompose_abcd(region, row, Value::known(b), postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_b<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        round_idx: InitialRound,
        assigned_b: &RoundWordDense<F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_b_row(round_idx);

        let b_value = assigned_b.value();
        let (dense_halves, spread_halves) = self.assign_word_halves(region, row, b_value)?;
        region.constrain_equal(dense_halves.0.cell(), assigned_b.0.cell())?;
        region.constrain_equal(dense_halves.1.cell(), assigned_b.1.cell())?;
        self.decompose_abcd(region, row, b_value, postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_iv_c<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_c_row(InitialRound);

        let c = IV[2];
        let (dense_halves, spread_halves) = self.assign_word_halves_fixed(region, row, c)?;
        self.decompose_abcd(region, row, Value::known(c), postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_c<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        round_idx: InitialRound,
        assigned_c: &RoundWordDense<F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_c_row(round_idx);

        let c_value = assigned_c.value();
        let (dense_halves, spread_halves) = self.assign_word_halves(region, row, c_value)?;
        region.constrain_equal(dense_halves.0.cell(), assigned_c.0.cell())?;
        region.constrain_equal(dense_halves.1.cell(), assigned_c.1.cell())?;
        self.decompose_abcd(region, row, c_value, postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_iv_f<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_f_row(InitialRound);

        let f = IV[5];
        let (dense_halves, spread_halves) = self.assign_word_halves_fixed(region, row, f)?;
        self.decompose_efgh(region, row, Value::known(f), postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_f<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        round_idx: InitialRound,
        assigned_f: &RoundWordDense<F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_f_row(round_idx);

        let f_value = assigned_f.value();
        let (dense_halves, spread_halves) = self.assign_word_halves(region, row, f_value)?;
        region.constrain_equal(dense_halves.0.cell(), assigned_f.0.cell())?;
        region.constrain_equal(dense_halves.1.cell(), assigned_f.1.cell())?;
        self.decompose_efgh(region, row, f_value, postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_iv_g<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_g_row(InitialRound);

        let g = IV[6];
        let (dense_halves, spread_halves) = self.assign_word_halves_fixed(region, row, g)?;
        self.decompose_efgh(region, row, Value::known(g), postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }

    fn decompose_g<F: PrimeField>(
        &self,
        region: &mut Region<'_, F>,
        round_idx: InitialRound,
        assigned_g: &RoundWordDense<F>,
        postponed: &mut Vec<Box<dyn PostponedSpreadVar>>,
    ) -> Result<RoundWord<F>, Error> {
        let row = get_decompose_g_row(round_idx);

        let g_value = assigned_g.value();
        let (dense_halves, spread_halves) = self.assign_word_halves(region, row, g_value)?;
        region.constrain_equal(dense_halves.0.cell(), assigned_g.0.cell())?;
        region.constrain_equal(dense_halves.1.cell(), assigned_g.1.cell())?;
        self.decompose_efgh(region, row, g_value, postponed)?;
        Ok(RoundWord::new(dense_halves, Some(spread_halves)))
    }
}
