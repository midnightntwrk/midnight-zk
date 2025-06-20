use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::plonk::{Constraint, Constraints, Expression};

use super::super::Gate;
use crate::hash::sha256::util::MASK_EVEN_32;

pub struct CompressionGate<F: PrimeField>(PhantomData<F>);

impl<F: PrimeField> CompressionGate<F> {
    fn ones() -> Expression<F> {
        Expression::Constant(F::ONE)
    }

    // Decompose `A,B,C,D` words
    // (2, 11, 9, 10)-bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_decompose_abcd(
        s_decompose_abcd: Expression<F>,
        a: Expression<F>,
        spread_a: Expression<F>,
        b: Expression<F>,
        spread_b: Expression<F>,
        c_lo: Expression<F>,
        spread_c_lo: Expression<F>,
        c_mid: Expression<F>,
        spread_c_mid: Expression<F>,
        c_hi: Expression<F>,
        spread_c_hi: Expression<F>,
        d: Expression<F>,
        spread_d: Expression<F>,
        word_lo: Expression<F>,
        spread_word_lo: Expression<F>,
        word_hi: Expression<F>,
        spread_word_hi: Expression<F>,
    ) -> Constraints<
        F,
        (&'static str, Expression<F>),
        impl Iterator<Item = (&'static str, Expression<F>)>,
    > {
        let check_spread_and_range = Gate::two_bit_spread_and_range(a.clone(), spread_a.clone());
        let dense_check = a
            + b * F::from(1 << 2)
            + c_lo * F::from(1 << 13)
            + c_mid * F::from(1 << 16)
            + c_hi * F::from(1 << 19)
            + d * F::from(1 << 22)
            + word_lo * (-F::ONE)
            + word_hi * F::from(1 << 16) * (-F::ONE);
        let spread_check = spread_a
            + spread_b * F::from(1 << 4)
            + spread_c_lo * F::from(1 << 26)
            + spread_c_mid * F::from(1 << 32)
            + spread_c_hi * F::from(1 << 38)
            + spread_d * F::from(1 << 44)
            + spread_word_lo * (-F::ONE)
            + spread_word_hi * F::from(1 << 32) * (-F::ONE);

        Constraints::with_selector(
            s_decompose_abcd,
            check_spread_and_range
                .chain(Some(("dense_check", dense_check)))
                .chain(Some(("spread_check", spread_check))),
        )
    }

    // Decompose `E,F,G,H` words
    // (6, 5, 14, 7)-bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_decompose_efgh(
        s_decompose_efgh: Expression<F>,
        a_lo: Expression<F>,
        spread_a_lo: Expression<F>,
        a_hi: Expression<F>,
        spread_a_hi: Expression<F>,
        b_lo: Expression<F>,
        spread_b_lo: Expression<F>,
        b_hi: Expression<F>,
        spread_b_hi: Expression<F>,
        c: Expression<F>,
        spread_c: Expression<F>,
        d: Expression<F>,
        spread_d: Expression<F>,
        word_lo: Expression<F>,
        spread_word_lo: Expression<F>,
        word_hi: Expression<F>,
        spread_word_hi: Expression<F>,
    ) -> Constraints<
        F,
        (&'static str, Expression<F>),
        impl Iterator<Item = (&'static str, Expression<F>)>,
    > {
        let check_spread_and_range =
            Gate::two_bit_spread_and_range(b_lo.clone(), spread_b_lo.clone());
        let dense_check = a_lo
            + a_hi * F::from(1 << 3)
            + b_lo * F::from(1 << 6)
            + b_hi * F::from(1 << 8)
            + c * F::from(1 << 11)
            + d * F::from(1 << 25)
            + word_lo * (-F::ONE)
            + word_hi * F::from(1 << 16) * (-F::ONE);
        let spread_check = spread_a_lo
            + spread_a_hi * F::from(1 << 6)
            + spread_b_lo * F::from(1 << 12)
            + spread_b_hi * F::from(1 << 16)
            + spread_c * F::from(1 << 22)
            + spread_d * F::from(1 << 50)
            + spread_word_lo * (-F::ONE)
            + spread_word_hi * F::from(1 << 32) * (-F::ONE);

        Constraints::with_selector(
            s_decompose_efgh,
            check_spread_and_range
                .chain(Some(("dense_check", dense_check)))
                .chain(Some(("spread_check", spread_check))),
        )
    }

    // s_upper_sigma_0 on abcd words
    // (2, 11, 9, 10)-bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_upper_sigma_0(
        s_upper_sigma_0: Expression<F>,
        spread_r0_even: Expression<F>,
        spread_r0_odd: Expression<F>,
        spread_r1_even: Expression<F>,
        spread_r1_odd: Expression<F>,
        spread_a: Expression<F>,
        spread_b: Expression<F>,
        spread_c_lo: Expression<F>,
        spread_c_mid: Expression<F>,
        spread_c_hi: Expression<F>,
        spread_d: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let spread_witness = spread_r0_even
            + spread_r0_odd * F::from(2)
            + (spread_r1_even + spread_r1_odd * F::from(2)) * F::from(1 << 32);
        let xor_0 = spread_b.clone()
            + spread_c_lo.clone() * F::from(1 << 22)
            + spread_c_mid.clone() * F::from(1 << 28)
            + spread_c_hi.clone() * F::from(1 << 34)
            + spread_d.clone() * F::from(1 << 40)
            + spread_a.clone() * F::from(1 << 60);
        let xor_1 = spread_c_lo.clone()
            + spread_c_mid.clone() * F::from(1 << 6)
            + spread_c_hi.clone() * F::from(1 << 12)
            + spread_d.clone() * F::from(1 << 18)
            + spread_a.clone() * F::from(1 << 38)
            + spread_b.clone() * F::from(1 << 42);
        let xor_2 = spread_d
            + spread_a * F::from(1 << 20)
            + spread_b * F::from(1 << 24)
            + spread_c_lo * F::from(1 << 46)
            + spread_c_mid * F::from(1 << 52)
            + spread_c_hi * F::from(1 << 58);
        let xor = xor_0 + xor_1 + xor_2;
        let check = spread_witness + (xor * -F::ONE);

        Some(("s_upper_sigma_0", s_upper_sigma_0 * check))
    }

    // s_upper_sigma_1 on efgh words
    // (6, 5, 14, 7)-bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_upper_sigma_1(
        s_upper_sigma_1: Expression<F>,
        spread_r0_even: Expression<F>,
        spread_r0_odd: Expression<F>,
        spread_r1_even: Expression<F>,
        spread_r1_odd: Expression<F>,
        spread_a_lo: Expression<F>,
        spread_a_hi: Expression<F>,
        spread_b_lo: Expression<F>,
        spread_b_hi: Expression<F>,
        spread_c: Expression<F>,
        spread_d: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let spread_witness = spread_r0_even
            + spread_r0_odd * F::from(2)
            + (spread_r1_even + spread_r1_odd * F::from(2)) * F::from(1 << 32);

        let xor_0 = spread_b_lo.clone()
            + spread_b_hi.clone() * F::from(1 << 4)
            + spread_c.clone() * F::from(1 << 10)
            + spread_d.clone() * F::from(1 << 38)
            + spread_a_lo.clone() * F::from(1 << 52)
            + spread_a_hi.clone() * F::from(1 << 58);
        let xor_1 = spread_c.clone()
            + spread_d.clone() * F::from(1 << 28)
            + spread_a_lo.clone() * F::from(1 << 42)
            + spread_a_hi.clone() * F::from(1 << 48)
            + spread_b_lo.clone() * F::from(1 << 54)
            + spread_b_hi.clone() * F::from(1 << 58);
        let xor_2 = spread_d
            + spread_a_lo * F::from(1 << 14)
            + spread_a_hi * F::from(1 << 20)
            + spread_b_lo * F::from(1 << 26)
            + spread_b_hi * F::from(1 << 30)
            + spread_c * F::from(1 << 36);
        let xor = xor_0 + xor_1 + xor_2;
        let check = spread_witness + (xor * -F::ONE);

        Some(("s_upper_sigma_1", s_upper_sigma_1 * check))
    }

    // First part of choice gate on (E, F, G), E ∧ F
    #[allow(clippy::too_many_arguments)]
    pub fn s_ch(
        s_ch: Expression<F>,
        spread_p0_even: Expression<F>,
        spread_p0_odd: Expression<F>,
        spread_p1_even: Expression<F>,
        spread_p1_odd: Expression<F>,
        spread_e_lo: Expression<F>,
        spread_e_hi: Expression<F>,
        spread_f_lo: Expression<F>,
        spread_f_hi: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let lhs_lo = spread_e_lo + spread_f_lo;
        let lhs_hi = spread_e_hi + spread_f_hi;
        let lhs = lhs_lo + lhs_hi * F::from(1 << 32);

        let rhs_even = spread_p0_even + spread_p1_even * F::from(1 << 32);
        let rhs_odd = spread_p0_odd + spread_p1_odd * F::from(1 << 32);
        let rhs = rhs_even + rhs_odd * F::from(2);

        let check = lhs + rhs * -F::ONE;

        Some(("s_ch", s_ch * check))
    }

    // Second part of Choice gate on (E, F, G), ¬E ∧ G
    #[allow(clippy::too_many_arguments)]
    pub fn s_ch_neg(
        s_ch_neg: Expression<F>,
        spread_q0_even: Expression<F>,
        spread_q0_odd: Expression<F>,
        spread_q1_even: Expression<F>,
        spread_q1_odd: Expression<F>,
        spread_e_lo: Expression<F>,
        spread_e_hi: Expression<F>,
        spread_e_neg_lo: Expression<F>,
        spread_e_neg_hi: Expression<F>,
        spread_g_lo: Expression<F>,
        spread_g_hi: Expression<F>,
    ) -> Constraints<
        F,
        (&'static str, Expression<F>),
        impl Iterator<Item = (&'static str, Expression<F>)>,
    > {
        let neg_check = {
            let evens = Self::ones() * F::from(MASK_EVEN_32 as u64);
            // evens - spread_e_lo = spread_e_neg_lo
            let lo_check = spread_e_neg_lo.clone() + spread_e_lo + (evens.clone() * (-F::ONE));
            // evens - spread_e_hi = spread_e_neg_hi
            let hi_check = spread_e_neg_hi.clone() + spread_e_hi + (evens * (-F::ONE));

            std::iter::empty()
                .chain(Some(("lo_check", lo_check)))
                .chain(Some(("hi_check", hi_check)))
        };

        let lhs_lo = spread_e_neg_lo + spread_g_lo;
        let lhs_hi = spread_e_neg_hi + spread_g_hi;
        let lhs = lhs_lo + lhs_hi * F::from(1 << 32);

        let rhs_even = spread_q0_even + spread_q1_even * F::from(1 << 32);
        let rhs_odd = spread_q0_odd + spread_q1_odd * F::from(1 << 32);
        let rhs = rhs_even + rhs_odd * F::from(2);

        Constraints::with_selector(s_ch_neg, neg_check.chain(Some(("s_ch_neg", lhs - rhs))))
    }

    // Majority gate on (A, B, C)
    #[allow(clippy::too_many_arguments)]
    pub fn s_maj(
        s_maj: Expression<F>,
        spread_m_0_even: Expression<F>,
        spread_m_0_odd: Expression<F>,
        spread_m_1_even: Expression<F>,
        spread_m_1_odd: Expression<F>,
        spread_a_lo: Expression<F>,
        spread_a_hi: Expression<F>,
        spread_b_lo: Expression<F>,
        spread_b_hi: Expression<F>,
        spread_c_lo: Expression<F>,
        spread_c_hi: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let maj_even = spread_m_0_even + spread_m_1_even * F::from(1 << 32);
        let maj_odd = spread_m_0_odd + spread_m_1_odd * F::from(1 << 32);
        let maj = maj_even + maj_odd * F::from(2);

        let a = spread_a_lo + spread_a_hi * F::from(1 << 32);
        let b = spread_b_lo + spread_b_hi * F::from(1 << 32);
        let c = spread_c_lo + spread_c_hi * F::from(1 << 32);
        let sum = a + b + c;

        Some(("maj", s_maj * (sum - maj)))
    }

    // s_h_prime to get H' = H + Ch(E, F, G) + s_upper_sigma_1(E) + K + W
    #[allow(clippy::too_many_arguments)]
    pub fn s_h_prime(
        s_h_prime: Expression<F>,
        h_prime_lo: Expression<F>,
        h_prime_hi: Expression<F>,
        h_prime_carry: Expression<F>,
        carry_lsb: Expression<F>,
        carry_msbits: Expression<F>,
        sigma_e_lo: Expression<F>,
        sigma_e_hi: Expression<F>,
        ch_lo: Expression<F>,
        ch_hi: Expression<F>,
        ch_neg_lo: Expression<F>,
        ch_neg_hi: Expression<F>,
        h_lo: Expression<F>,
        h_hi: Expression<F>,
        k_lo: Expression<F>,
        k_hi: Expression<F>,
        w_lo: Expression<F>,
        w_hi: Expression<F>,
    ) -> impl Iterator<Item = (&'static str, Expression<F>)> {
        let lo = h_lo + ch_lo + ch_neg_lo + sigma_e_lo + k_lo + w_lo;
        let hi = h_hi + ch_hi + ch_neg_hi + sigma_e_hi + k_hi + w_hi;

        let sum = lo + hi * F::from(1 << 16);
        let h_prime = h_prime_lo + h_prime_hi * F::from(1 << 16);

        let h_prime_equ_check = sum - (h_prime_carry.clone() * F::from(1 << 32)) - h_prime;

        // to range check h_prime_carry \in {0, 1, 2, 3, 4}, as the range-check
        // polynomial would be of degree 6 (adding the selector), we use the
        // following constraints with max degree 5 instead:
        // 1) carry_lsb = carry & 1 is a bit
        // 2) carry_msbits = (carry - carry_lsb) >> 1 :
        // i) when carry_lsb == 1, i.e carry == 1 or 3, then carry_msbits \in {0, 1}
        // ii) when carry_lsb == 0, i.e carry == 0, 2 or 4, then carry_msbits \in {0, 1,
        // 2}
        let carry_lsb_check = Gate::range_check(carry_lsb.clone(), 0, 1);
        let carry_equ_check = carry_lsb.clone() * Gate::range_check(carry_msbits.clone(), 0, 1)
            + (carry_lsb - Expression::Constant(F::ONE)) * Gate::range_check(carry_msbits, 0, 2);
        [
            ("h_prime equality check", h_prime_equ_check),
            ("h_prime carry_msb check", carry_lsb_check),
            ("h_prime carry equality check", carry_equ_check),
        ]
        .into_iter()
        .map(move |(name, poly)| (name, s_h_prime.clone() * poly))
    }

    // s_add_halves to get new_state = old_state + {a,b,...,h}
    // It is assumed that term1, term2 are already rangechecked and therefore carry
    // is not constrained
    #[allow(clippy::too_many_arguments)]
    pub fn s_add_halves(
        s_add_halves: Expression<F>,
        new_lo: Expression<F>,
        new_hi: Expression<F>,
        new_carry: Expression<F>,
        term1_lo: Expression<F>,
        term1_hi: Expression<F>,
        term2_lo: Expression<F>,
        term2_hi: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let lo = term1_lo + term2_lo; //16 lsb
        let hi = term1_hi + term2_hi; // 16 msb
        let sum = lo + hi * F::from(1 << 16);
        let new = new_lo + new_hi * F::from(1 << 16);

        let check = sum - (new_carry * F::from(1 << 32)) - new;

        Some(("s_add_halves", s_add_halves * check))
    }

    // s_a_new to get A_new = H' + Maj(A, B, C) + s_upper_sigma_0(A)
    #[allow(clippy::too_many_arguments)]
    pub fn s_a_new(
        s_a_new: Expression<F>,
        a_new_lo: Expression<F>,
        a_new_hi: Expression<F>,
        a_new_carry: Expression<F>,
        sigma_a_lo: Expression<F>,
        sigma_a_hi: Expression<F>,
        maj_abc_lo: Expression<F>,
        maj_abc_hi: Expression<F>,
        h_prime_lo: Expression<F>,
        h_prime_hi: Expression<F>,
    ) -> impl Iterator<Item = (&'static str, Expression<F>)> {
        let lo = sigma_a_lo + maj_abc_lo + h_prime_lo;
        let hi = sigma_a_hi + maj_abc_hi + h_prime_hi;
        let sum = lo + hi * F::from(1 << 16);
        let a_new = a_new_lo + a_new_hi * F::from(1 << 16);

        let equ_check = sum - (a_new_carry.clone() * F::from(1 << 32)) - a_new;

        let carry_check = Gate::range_check(a_new_carry, 0, 2);

        [("equality_check", equ_check), ("carry_check", carry_check)]
            .into_iter()
            .map(move |(name, poly)| (name, s_a_new.clone() * poly))
    }

    // s_e_new to get E_new = H' + D
    #[allow(clippy::too_many_arguments)]
    pub fn s_e_new(
        s_e_new: Expression<F>,
        e_new_lo: Expression<F>,
        e_new_hi: Expression<F>,
        e_new_carry: Expression<F>,
        d_lo: Expression<F>,
        d_hi: Expression<F>,
        h_prime_lo: Expression<F>,
        h_prime_hi: Expression<F>,
    ) -> impl Iterator<Item = (&'static str, Expression<F>)> {
        let lo = h_prime_lo + d_lo;
        let hi = h_prime_hi + d_hi;
        let sum = lo + hi * F::from(1 << 16);
        let e_new = e_new_lo + e_new_hi * F::from(1 << 16);

        let equ_check = sum - (e_new_carry.clone() * F::from(1 << 32)) - e_new;

        let carry_check = Gate::range_check(e_new_carry, 0, 1);

        [("equality_check", equ_check), ("carry_check", carry_check)]
            .into_iter()
            .map(move |(name, poly)| (name, s_e_new.clone() * poly))
    }

    // s_digest on final round
    #[allow(clippy::too_many_arguments)]
    pub fn s_digest(
        s_digest: Expression<F>,
        lo_0: Expression<F>,
        hi_0: Expression<F>,
        word_0: Expression<F>,
        lo_1: Expression<F>,
        hi_1: Expression<F>,
        word_1: Expression<F>,
        lo_2: Expression<F>,
        hi_2: Expression<F>,
        word_2: Expression<F>,
        lo_3: Expression<F>,
        hi_3: Expression<F>,
        word_3: Expression<F>,
    ) -> impl IntoIterator<Item = Constraint<F>> {
        let check_lo_hi = |lo: Expression<F>, hi: Expression<F>, word: Expression<F>| {
            lo + hi * F::from(1 << 16) - word
        };

        Constraints::with_selector(
            s_digest,
            [
                ("check_lo_hi_0", check_lo_hi(lo_0, hi_0, word_0)),
                ("check_lo_hi_1", check_lo_hi(lo_1, hi_1, word_1)),
                ("check_lo_hi_2", check_lo_hi(lo_2, hi_2, word_2)),
                ("check_lo_hi_3", check_lo_hi(lo_3, hi_3, word_3)),
            ],
        )
    }
}
