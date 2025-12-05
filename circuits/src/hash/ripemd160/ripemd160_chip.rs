//! Implementation in-circuit of the RIPEMD-160 hash function.

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

    |  T0 |  A0  |  A1   |  T1 |   A2  |   A3   |   A4  | A5 | A6 |
    |-----|------|-------|-----|-------|--------|-------|----|----|
    | T.1 |  A.1 | ~A.1  | T.3 |  A.3  |  ~A.3  |   A   |    |    |
    | T.2 |  A.2 | ~A.2  | T.4 |  A.4  |  ~A.4  | Rot(A)|    |    | <- q_rol

*/

/*
    A ⊞ B ⊞ C ⊞ D

    |  T0 |   A0  |   A1   |  T1 |   A2  |   A3   |   A4  | A5 | A6 | A7 |
    |-----|-------|--------|-----|-------|--------|-------|----|----|----|
    |  2  | carry | ~carry |  0  |   0   |   ~0   |   A   |  B |  C |  D | <- q_mod_add

*/
