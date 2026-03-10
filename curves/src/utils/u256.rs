use super::{U64Double, U64Words};

#[allow(dead_code)]
pub(crate) type U256 = U64Words<4>;
#[allow(dead_code)]
pub(crate) type U512 = U64Double<4>;

#[cfg(test)]
mod tests {
    use super::*;

    const fn u256(vals: [u64; 4]) -> U256 {
        U256::from(vals)
    }
    const fn u512(vals: [u64; 8]) -> U512 {
        U512::from(&vals)
    }

    // -------------------------------------------------
    // cmp
    // -------------------------------------------------

    #[test]
    fn cmp_equal() {
        let a = u256([1, 2, 3, 4]);
        assert_eq!(U256::cmp(&a, &a), 0);

        let a = u256([
            0xDEADBEEFDEADBEEF,
            0x0123456789ABCDEF,
            0x0123456789ABCDEF,
            0xFFFFFFFF00000000,
        ]);
        assert_eq!(U256::cmp(&a, &a), 0);
    }

    #[test]
    fn cmp_less() {
        let a = u256([0, 0, 0, 1]);
        let b = u256([0, 0, 0, 2]);
        assert_eq!(U256::cmp(&a, &b), -1);

        let a = u256([
            0xFFFFFFFFFFFFFFFF,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x1111111111111111,
        ]);
        let b = u256([
            0x0,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x2222222222222222,
        ]);
        assert_eq!(U256::cmp(&a, &b), -1);
    }

    #[test]
    fn cmp_greater() {
        let a = u256([0, 0, 0, 10]);
        let b = u256([0, 0, 0, 9]);
        assert_eq!(U256::cmp(&a, &b), 1);

        let a = u256([
            0xFFFFFFFFFFFFFFFF,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x1111111111111111,
        ]);
        let b = u256([
            0x0,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x2222222222222222,
        ]);
        assert_eq!(U256::cmp(&b, &a), 1);

        let a = u256([999, 0, 0, 5]);
        let b = u256([0, 0, 0, 4]);
        assert_eq!(U256::cmp(&a, &b), 1);
    }
    // -------------------------------------------------
    // add
    // -------------------------------------------------
    #[test]
    fn add_no_carry() {
        let a = u256([10, 0, 0, 0]);
        let b = u256([3, 0, 0, 0]);
        let (result, carry) = U256::add(&a, &b);
        let expected = u256([13, 0, 0, 0]);

        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(carry, 0);

        let a = u256([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
        ]);
        let b = u256([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x1111111111111111,
        ]);
        let (result, carry) = U256::add(&a, &b);
        let expected = u256([
            0x2222222222222222,
            0x4444444444444444,
            0x6666666666666666,
            0x5555555555555555,
        ]);

        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(carry, 0);
    }

    #[test]
    fn add_single_carry() {
        let a = u256([u64::MAX, 0, 0, 0]);
        let b = u256([1, 0, 0, 0]);
        let (result, carry) = U256::add(&a, &b);
        let expected = u256([0, 1, 0, 0]);

        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(carry, 0);
    }

    #[test]
    fn add_carry_chain() {
        let a = u256([u64::MAX, u64::MAX, 0, 0]);
        let b = u256([1, 0, 0, 0]);
        let (result, carry) = U256::add(&a, &b);
        let expected = u256([0, 0, 1, 0]);

        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(carry, 0);

        let a = u256([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0,
        ]);
        let b = u256([1, 0, 0, 0]);
        let (result, carry) = U256::add(&a, &b);
        let expected = u256([0, 0, 0, 1]);

        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(carry, 0);
    }

    #[test]
    fn add_overflow() {
        let a = u256([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = u256([1, 0, 0, 0]);

        let (result, carry) = U256::add(&a, &b);

        assert_eq!(U256::cmp(&result, &U256::zero()), 0);
        assert_ne!(carry, 0);
    }

    #[test]
    fn add_equal() {
        let a = u256([5, 5, 5, 5]);
        let (result, carry) = U256::add(&a, &a);
        let expected = u256([10, 10, 10, 10]);

        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(carry, 0);
    }

    // -------------------------------------------------
    // sub
    // -------------------------------------------------

    #[test]
    fn sub_no_borrow() {
        let a = u256([10, 0, 0, 0]);
        let b = u256([3, 0, 0, 0]);
        let (result, borrow) = U256::sub(&a, &b);
        let expected = u256([7, 0, 0, 0]);
        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(borrow, 0);

        let a = u256([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = u256([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
        ]);
        let (result, borrow) = U256::sub(&a, &b);
        let expected = u256([
            0xEEEEEEEEEEEEEEEE,
            0xDDDDDDDDDDDDDDDD,
            0xCCCCCCCCCCCCCCCC,
            0xBBBBBBBBBBBBBBBB,
        ]);
        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(borrow, 0);
    }

    #[test]
    fn sub_single_borrow() {
        let a = u256([0, 1, 0, 0]);
        let b = u256([1, 0, 0, 0]);
        let (result, borrow) = U256::sub(&a, &b);
        let expected = u256([u64::MAX, 0, 0, 0]);
        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(borrow, 0);
    }

    #[test]
    fn sub_borrow_chain() {
        let a = u256([0, 0, 1, 0]);
        let b = u256([1, 0, 0, 0]);
        let (result, borrow) = U256::sub(&a, &b);
        let expected = u256([u64::MAX, u64::MAX, 0, 0]);
        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(borrow, 0);

        let a = u256([
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
            0x1000000000000000,
        ]);
        let b = u256([1, 0, 0, 0]);
        let (result, borrow) = U256::sub(&a, &b);
        let expected = u256([u64::MAX, u64::MAX, u64::MAX, 0x0FFFFFFFFFFFFFFF]);
        assert_eq!(U256::cmp(&result, &expected), 0);
        assert_eq!(borrow, 0);

        let a = u256([1, 0, 0, 0]);
        let b = u256([
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
            0x1000000000000000,
        ]);
        let (result, borrow) = U256::sub(&a, &b);
        print!("{:?}", result);
        assert_eq!(
            U256::cmp(&result, &U256::from([1, 0, 0, 0xF000000000000000])),
            0
        );
        assert_ne!(borrow, 0);
    }

    #[test]
    fn sub_equal() {
        let a = u256([5, 5, 5, 5]);
        let (result, borrow) = U256::sub(&a, &a);
        assert_eq!(U256::cmp(&result, &U256::zero()), 0);
        assert_eq!(borrow, 0);
    }

    // -------------------------------------------------
    // mul
    // -------------------------------------------------

    #[test]
    fn mul_zero() {
        let a = u256([0; 4]);
        let b = u256([123, 0, 0, 0]);
        let result = U256::mul(&a, &b);
        assert_eq!(result, U512::zero());
    }

    #[test]
    fn mul_no_carry() {
        let a = u256([3, 0, 0, 0]);
        let b = u256([7, 0, 0, 0]);
        let result = U256::mul(&a, &b);
        let expected = U512::from(&[21, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(U512::cmp(&result, &expected), 0);
    }

    #[test]
    fn mul_with_carry() {
        let a = u256([u64::MAX, 0, 0, 0]);
        let b = u256([2, 0, 0, 0]);
        let result = U256::mul(&a, &b);
        let expected = U512::from(&[u64::MAX.wrapping_mul(2), 1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(U512::cmp(&result, &expected), 0);

        let a = u256([0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x0, 0x0]);
        let b = u256([0x2, 0x0, 0x0, 0x0]);
        let result = U256::mul(&a, &b);
        // Expected:
        // (2^128 - 1) * 2 = 2^129 - 2
        let expected = U512::from(&[0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 0, 0, 0]);
        assert_eq!(U512::cmp(&result, &expected), 0);

        let a = u256([1, 1, 0, 0]);
        let b = u256([1, 1, 0, 0]);
        let result = U256::mul(&a, &b);

        // (1 + 2^64)^2 = 1 + 2*(2^64) + 2^128
        let expected = U512::from(&[1, 2, 1, 0, 0, 0, 0, 0]);
        assert_eq!(U512::cmp(&result, &expected), 0);

        let a = u256([
            0x1234567890ABCDEF,
            0x0FEDCBA987654321,
            0xAAAAAAAAAAAAAAAA,
            0x5555555555555555,
        ]);

        let b = u256([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
        ]);
        let expected: U512 = U512::from(&[
            0xFEC94F918FF48BDF,
            0xFDB97530ED54320F,
            0x9D0369D03748D159,
            0x97530ECA86EDCBA9,
            0x9D6480F2B727104E,
            0x9DD9031C241B00D5,
            0x7D27D27D27D27D27,
            0x16C16C16C16C16C1,
        ]);

        assert_eq!(U256::mul(&a, &b), expected);
    }

    // -------------------------------------------------
    // pow2
    // -------------------------------------------------

    #[test]
    fn pow2_within() {
        let a = u256([123, 0, 0, 0]);
        let result = U256::pow2(&a, 1);
        let expected = u256([246, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u256([123, 0, 0, 0]);
        let result = U256::pow2(&a, 42);
        let expected = u256([540959720865792, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u256([0, 357, 0, 0]);
        let result = U256::pow2(&a, 42);
        let expected = u256([0, 1570102604464128, 0, 0]);
        assert_eq!(result, expected);
    }

    #[test]
    fn pow2_between() {
        let a = u256([3, 0, 0, 0]);
        let result = U256::pow2(&a, 64);
        let expected = u256([0, 3, 0, 0]);
        assert_eq!(result, expected);

        let a = u256([3, 0, 0, 0]);
        let result = U256::pow2(&a, 128);
        let expected = u256([0, 0, 3, 0]);
        assert_eq!(result, expected);
    }

    #[test]
    fn pow2_trans() {
        let a = u256([11240984670053072896, 0, 0, 0]);
        let result = U256::pow2(&a, 4);
        let expected = u256([13835058057463201792, 9, 0, 0]);
        assert_eq!(result, expected);
    }

    #[test]
    fn pow2_u512_within() {
        let a = u512([123, 0, 0, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 1);
        let expected = u512([246, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([123, 0, 0, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 42);
        let expected = u512([540959720865792, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([0, 357, 0, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 42);
        let expected = u512([0, 1570102604464128, 0, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([0, 0, 0, 0, 0, 357, 0, 0]);
        let result = U512::pow2(&a, 42);
        let expected = u512([0, 0, 0, 0, 0, 1570102604464128, 0, 0]);
        assert_eq!(result, expected);
    }

    #[test]
    fn pow2_u512_between() {
        let a = u512([3, 0, 0, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 64);
        let expected = u512([0, 3, 0, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([3, 0, 0, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 128);
        let expected = u512([0, 0, 3, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([0, 0, 0, 0, 3, 0, 0, 0]);
        let result = U512::pow2(&a, 128);
        let expected = u512([0, 0, 0, 0, 0, 0, 3, 0]);
        assert_eq!(result, expected);

        let a = u512([0, 0, 3, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 128);
        let expected = u512([0, 0, 0, 0, 3, 0, 0, 0]);
        assert_eq!(result, expected);
    }

    #[test]
    fn pow2_u512_trans() {
        let a = u512([11240984670053072896, 0, 0, 0, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 4);
        let expected = u512([13835058057463201792, 9, 0, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([0, 0, 0, 11240984670053072896, 0, 0, 0, 0]);
        let result = U512::pow2(&a, 4);
        let expected = u512([0, 0, 0, 13835058057463201792, 9, 0, 0, 0]);
        assert_eq!(result, expected);

        let a = u512([0, 0, 0, 0, 11240984670053072896, 0, 0, 0]);
        let result = U512::pow2(&a, 4);
        let expected = u512([0, 0, 0, 0, 13835058057463201792, 9, 0, 0]);
        assert_eq!(result, expected);
    }

    // -------------------------------------------------
    // modulo
    // -------------------------------------------------
    #[test]
    fn modulo_less_than_modulus() {
        let a = u256([5, 0, 0, 0]);
        let modulus = u256([10, 0, 0, 0]);
        let result = U256::modulo(&a, &modulus);
        assert_eq!(result, u256([5, 0, 0, 0]));
    }

    #[test]
    fn modulo_equal() {
        let a = u256([10, 0, 0, 0]);
        let modulus = u256([10, 0, 0, 0]);
        let result = U256::modulo(&a, &modulus);
        assert_eq!(result, u256([0; 4]));
    }

    #[test]
    fn modulo_greater() {
        let a = u256([25, 0, 0, 0]);
        let modulus = u256([10, 0, 0, 0]);
        let result = U256::modulo(&a, &modulus);
        assert_eq!(result, u256([5, 0, 0, 0]));
    }

    #[test]
    fn modulo_u512_less_than_modulus() {
        let a = u512([5, 0, 0, 0, 0, 0, 0, 0]);
        let modulus = u256([10, 0, 0, 0]);
        let result = U512::modulo_half(&a, &modulus);
        assert_eq!(result, u256([5, 0, 0, 0]));
    }

    #[test]
    fn modulo_u512_equal() {
        let a = u512([10, 0, 0, 0, 0, 0, 0, 0]);
        let modulus = u256([10, 0, 0, 0]);
        let result = U512::modulo_half(&a, &modulus);
        assert_eq!(result, u256([0; 4]));
    }

    #[test]
    fn modulo_u512_greater() {
        let a = u512([25, 0, 0, 0, 0, 0, 0, 0]);
        let modulus = u256([10, 0, 0, 0]);
        let result = U512::modulo_half(&a, &modulus);
        assert_eq!(result, u256([5, 0, 0, 0]));

        let a = u512([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
            0,
            0,
            0,
            0,
        ]);
        let modulus = u256([
            0xFFFFFFFFFFFFFFFF,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x1111111111111111,
        ]);
        let result = U512::modulo_half(&a, &modulus);
        let expected = u256([
            0x1111111111111114,
            0x2222222222222221,
            0,
            0x111111111111110F,
        ]);
        assert_eq!(result, expected);

        let a = u512([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
            0x4444444444444444,
            0x3333333333333333,
            0x2222222222222222,
            0x1111111111111111,
        ]);
        let modulus = u256([
            0xFFFFFFFFFFFFFFFF,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x1111111111111111,
        ]);
        let result = U512::modulo_half(&a, &modulus);
        let expected = u256([
            0x111111111111361A,
            0x777777777777677A,
            0x7777777777777B82,
            0x111111111110F7FA,
        ]);
        assert_eq!(result, expected);
    }
}
