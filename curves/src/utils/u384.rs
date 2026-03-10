use super::{U64Double, U64Words};

pub(crate) type U384 = U64Words<6>;

#[allow(dead_code)]
pub(crate) type U768 = U64Double<6>;

#[cfg(test)]
mod tests {
    use super::*;

    const fn u384(vals: [u64; 6]) -> U384 {
        U384::from(vals)
    }
    const fn u768(vals: [u64; 12]) -> U768 {
        U768::from(&vals)
    }

    // -------------------------------------------------
    // cmp tests
    // -------------------------------------------------
    #[test]
    fn cmp_equal() {
        let a = u384([1, 2, 3, 4, 5, 6]);
        assert_eq!(U384::cmp(&a, &a), 0);

        let a = u384([
            0xDEADBEEFDEADBEEF,
            0x0123456789ABCDEF,
            3,
            4,
            0x0123456789ABCDEF,
            6,
        ]);
        assert_eq!(U384::cmp(&a, &a), 0);
    }

    #[test]
    fn cmp_less() {
        let a = u384([1, 2, 3, 4, 5, 5]);
        let b = u384([1, 2, 3, 4, 5, 6]);
        assert_eq!(U384::cmp(&a, &b), -1);
        assert_eq!(U384::cmp(&b, &a), 1);
    }

    #[test]
    fn cmp_greater() {
        let a = u384([0, 0, 0, 0, 0, 10]);
        let b = u384([0, 0, 0, 0, 0, 9]);
        assert_eq!(U384::cmp(&a, &b), 1);

        let a = u384([
            0xFFFFFFFFFFFFFFFF,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
        ]);
        let b = u384([
            0x0,
            0xAAAAAAAAAAAAAAAA,
            0xBBBBBBBBBBBBBBBB,
            0x1111111111111111,
            0x2222222222222222,
            0x2222222222222222,
        ]);
        assert_eq!(U384::cmp(&a, &b), 1);
    }

    // -------------------------------------------------
    // sub tests
    // -------------------------------------------------
    #[test]
    fn sub_no_borrow() {
        let a = u384([10, 20, 30, 40, 50, 60]);
        let b = u384([1, 2, 3, 4, 5, 6]);
        let (result, borrow) = U384::sub(&a, &b);
        let expected = u384([9, 18, 27, 36, 45, 54]);
        assert_eq!(result, expected);
        assert_eq!(borrow, 0);

        let a = u384([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = u384([
            0x0,
            0x0,
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
        ]);
        let (result, borrow) = U384::sub(&a, &b);
        let expected = u384([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xEEEEEEEEEEEEEEEE,
            0xDDDDDDDDDDDDDDDD,
            0xCCCCCCCCCCCCCCCC,
            0xBBBBBBBBBBBBBBBB,
        ]);
        assert_eq!(result, expected);
        assert_eq!(borrow, 0);
    }

    #[test]
    fn sub_single_borrow() {
        let a = u384([0, 1, 0, 0, 0, 0]);
        let b = u384([1, 0, 0, 0, 0, 0]);
        let (result, borrow) = U384::sub(&a, &b);
        let expected = u384([u64::MAX, 0, 0, 0, 0, 0]);
        assert_eq!(result, expected);
        assert_eq!(borrow, 0);

        let a = u384([
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ]);
        let b = u384([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
            0x5555555555555555,
            0x6666666666666666,
        ]);
        let (result, borrow) = U384::sub(&a, &b);
        let expected = u384([
            0xEEEEEEEEEEEEEEEE,
            0xDDDDDDDDDDDDDDDD,
            0xCCCCCCCCCCCCCCCC,
            0xBBBBBBBBBBBBBBBB,
            0xAAAAAAAAAAAAAAAA,
            0x9999999999999999,
        ]);
        assert_eq!(result, expected);
        assert_eq!(borrow, 0);
    }

    #[test]
    fn sub_borrow_chain() {
        let a = u384([0, 0, 1, 0, 0, 0]);
        let b = u384([1, 0, 0, 0, 0, 0]);
        let (result, borrow) = U384::sub(&a, &b);
        let expected = u384([u64::MAX, u64::MAX, 0, 0, 0, 0]);
        assert_eq!(result, expected);
        assert_eq!(borrow, 0);

        let a = u384([
            0x1234_5678_9ABC_DEF0,
            0x0FED_CBA9_8765_4321,
            0xAAAA_BBBB_CCCC_DDDD,
            0x5555_6666_7777_8888,
            0xCAFE_BABE_DEAD_BEEF,
            0xDEAD_BEEF_F00D_CAFE,
        ]);
        let b = u384([
            0x2345_6789_ABCD_EF01,
            0x0FED_CBA9_8765_4321,
            0xBBBB_CCCC_DDDD_EEEE,
            0x4444_5555_6666_7777,
            0x0123_4567_89AB_CDEF,
            0xF00D_CAFE_DEAD_BEEF,
        ]);
        let (result, borrow) = U384::sub(&b, &a);
        let expected = u384([
            0x1111_1111_1111_1011,
            0x0000_0000_0000_0000,
            0x1111_1111_1111_1111,
            0xEEEE_EEEE_EEEE_EEEF,
            0x3624_8AA8_AAFE_0EFF,
            0x1160_0C0E_EE9F_F3F0,
        ]);

        assert_eq!(result, expected);
        assert_eq!(borrow, 0);

        let (_result, borrow) = U384::sub(&a, &b);
        assert_eq!(result, expected);
        assert_ne!(borrow, 0);
    }

    #[test]
    fn sub_equal() {
        let a = u384([5, 5, 5, 5, 5, 5]);
        let (result, _) = U384::sub(&a, &a);
        assert_eq!(result, U384::zero());
    }

    // -------------------------------------------------
    // mul tests
    // -------------------------------------------------
    #[test]
    fn mul_zero() {
        let a = u384([0; 6]);
        let b = u384([123, 0, 0, 0, 0, 0]);
        let result = U384::mul(&a, &b);
        assert_eq!(result, u768([0; 12]));
    }

    #[test]
    fn mul_no_carry() {
        let a = u384([1, 2, 0, 0, 0, 0]);
        let b = u384([3, 4, 0, 0, 0, 0]);
        let expected = u768([3, 10, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(U384::mul(&a, &b), expected);
    }

    #[test]
    fn mul_with_carry() {
        let a = u384([u64::MAX, 0, 0, 0, 0, 0]);
        let b = u384([2, 0, 0, 0, 0, 0]);
        let expected = u768([18446744073709551614, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(U384::mul(&a, &b), expected);

        let a = u384([
            0x1234567890ABCDEF,
            0x0FEDCBA987654321,
            0xAAAAAAAAAAAAAAAA,
            0x5555555555555555,
            0xCAFEBABECAFEBABE,
            0xDEADBEEFDEADBEEF,
        ]);
        let b = u384([
            0x1111111111111111,
            0x2222222222222222,
            0x3333333333333333,
            0x4444444444444444,
            0x0123456789ABCDEF,
            0xFEDCBA9876543210,
        ]);
        let expected = u768([
            0xFEC94F918FF48BDF,
            0xFDB97530ED54320F,
            0x9D0369D03748D159,
            0x97530ECA86EDCBA9,
            0x49291D913B08BA0D,
            0x82D996E373FB1DAD,
            0xC8ADDE4F79B539DC,
            0xB60A3348EF8919B8,
            0xE6519958CD49A272,
            0x388DECBC93939D17,
            0x87DC136F5B7C80A8,
            0xDDB06310EFE4B989,
        ]);
        assert_eq!(U384::mul(&a, &b), expected);
    }

    // -------------------------------------------------
    // modulo tests
    // -------------------------------------------------
    #[test]
    fn modulo_less_than_modulus() {
        let a = u768([5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        let modulus = u384([10, 0, 0, 0, 0, 0]);
        let expected = u384([5, 0, 0, 0, 0, 0]);
        assert_eq!(U768::modulo_half(&a, &modulus), expected);
    }

    #[test]
    fn modulo_equal() {
        let a = u768([10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        let modulus = u384([10, 0, 0, 0, 0, 0]);
        let expected = U384::zero();
        assert_eq!(U768::modulo_half(&a, &modulus), expected);
    }

    #[test]
    fn modulo_greater() {
        let a = u768([25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        let modulus = u384([10, 0, 0, 0, 0, 0]);
        let expected = u384([5, 0, 0, 0, 0, 0]);
        assert_eq!(U768::modulo_half(&a, &modulus), expected);
    }
}
