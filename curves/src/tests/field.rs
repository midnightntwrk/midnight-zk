use ff::{Field, PrimeField};
use rand_core::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;

pub fn random_sqrt_tests<F: Field>() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    for _ in 0..10000 {
        let a = F::random(&mut rng);
        let a_sq = a.square();
        let a_again = a_sq.sqrt();
        assert_eq!(a_again.is_some().unwrap_u8(), 1);

        let a_again = a_again.unwrap();

        assert!(a == a_again || a == -a_again);
    }

    let mut c = F::ONE;
    for _ in 0..10000 {
        let c_sq = c.square();
        let c_again = c_sq.sqrt();
        assert_eq!(c_again.is_some().unwrap_u8(), 1);
        let c_again = c_again.unwrap();
        assert!(c == c_again || c == -c_again);
        c.add_assign(&F::ONE);
    }
}

pub fn random_field_tests<F: Field>() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    random_multiplication_tests::<F, _>(&mut rng);
    random_addition_tests::<F, _>(&mut rng);
    random_subtraction_tests::<F, _>(&mut rng);
    random_negation_tests::<F, _>(&mut rng);
    random_doubling_tests::<F, _>(&mut rng);
    random_squaring_tests::<F, _>(&mut rng);
    random_inversion_tests::<F, _>(&mut rng);
    random_expansion_tests::<F, _>(&mut rng);

    assert!(bool::from(F::ZERO.is_zero()));
    {
        let mut z = F::ZERO;
        z = z.neg();
        assert!(bool::from(z.is_zero()));
    }

    assert_eq!(F::ZERO.invert().is_none().unwrap_u8(), 1);

    // Multiplication by zero
    {
        let mut a = F::random(&mut rng);
        a.mul_assign(&F::ZERO);
        assert!(bool::from(a.is_zero()));
    }

    // Addition by zero
    {
        let mut a = F::random(&mut rng);
        let copy = a;
        a.add_assign(&F::ZERO);
        assert_eq!(a, copy);
    }
}

pub fn from_str_tests<F: PrimeField>() {
    {
        let a = "84395729384759238745923745892374598234705297301958723458712394587103249587213984572934750213947582345792304758273458972349582734958273495872304598234";
        let b = "38495729084572938457298347502349857029384609283450692834058293405982304598230458230495820394850293845098234059823049582309485203948502938452093482039";
        let c = "3248875134290623212325429203829831876024364170316860259933542844758450336418538569901990710701240661702808867062612075657861768196242274635305077449545396068598317421057721935408562373834079015873933065667961469731886739181625866970316226171512545167081793907058686908697431878454091011239990119126";

        let mut a = F::from_str_vartime(a).unwrap();
        let b = F::from_str_vartime(b).unwrap();
        let c = F::from_str_vartime(c).unwrap();

        a.mul_assign(&b);

        assert_eq!(a, c);
    }

    {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let n = rng.next_u64();

            let a = F::from_str_vartime(&format!("{}", n)).unwrap();
            let b = F::from(n);

            assert_eq!(a, b);
        }
    }

    assert!(F::from_str_vartime("").is_none());
    assert!(bool::from(F::from_str_vartime("0").unwrap().is_zero()));
    assert!(F::from_str_vartime("00").is_none());
    assert!(F::from_str_vartime("00000000000").is_none());
}

fn random_multiplication_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        let a = F::random(&mut *rng);
        let b = F::random(&mut *rng);
        let c = F::random(&mut *rng);

        let mut t0 = a; // (a * b) * c
        t0.mul_assign(&b);
        t0.mul_assign(&c);

        let mut t1 = a; // (a * c) * b
        t1.mul_assign(&c);
        t1.mul_assign(&b);

        let mut t2 = b; // (b * c) * a
        t2.mul_assign(&c);
        t2.mul_assign(&a);

        assert_eq!(t0, t1);
        assert_eq!(t1, t2);
    }
}

fn random_addition_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        let a = F::random(&mut *rng);
        let b = F::random(&mut *rng);
        let c = F::random(&mut *rng);

        let mut t0 = a; // (a + b) + c
        t0.add_assign(&b);
        t0.add_assign(&c);

        let mut t1 = a; // (a + c) + b
        t1.add_assign(&c);
        t1.add_assign(&b);

        let mut t2 = b; // (b + c) + a
        t2.add_assign(&c);
        t2.add_assign(&a);

        assert_eq!(t0, t1);
        assert_eq!(t1, t2);
    }
}

fn random_subtraction_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        let b = F::random(&mut *rng);
        let a = F::random(&mut *rng);

        let mut t0 = a; // (a - b)
        t0.sub_assign(&b);

        let mut t1 = b; // (b - a)
        t1.sub_assign(&a);

        let mut t2 = t0; // (a - b) + (b - a) = 0
        t2.add_assign(&t1);

        assert!(bool::from(t2.is_zero()));
    }
}

fn random_negation_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        let a = F::random(&mut *rng);
        let mut b = a;
        b = b.neg();
        b.add_assign(&a);

        assert!(bool::from(b.is_zero()), "negation");
    }
}

fn random_doubling_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        let mut a = F::random(&mut *rng);
        let mut b = a;
        a.add_assign(&b);
        b = b.double();

        assert_eq!(a, b, "doubling");
    }
}

fn random_squaring_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        let mut a = F::random(&mut *rng);
        let mut b = a;
        a.mul_assign(&b);
        b = b.square();

        assert_eq!(a, b, "squaring");
    }
}

fn random_inversion_tests<F: Field, R: RngCore>(rng: &mut R) {
    assert_eq!(F::ZERO.invert().is_none().unwrap_u8(), 1);

    for i in 0..10000 {
        let mut a = F::random(&mut *rng);
        let b = a.invert().unwrap(); // probablistically nonzero
        a.mul_assign(&b);

        assert_eq!(a, F::ONE, "inversion round {}", i);
    }
}

fn random_expansion_tests<F: Field, R: RngCore>(rng: &mut R) {
    for _ in 0..10000 {
        // Compare (a + b)(c + d) and (a*c + b*c + a*d + b*d)

        let a = F::random(&mut *rng);
        let b = F::random(&mut *rng);
        let c = F::random(&mut *rng);
        let d = F::random(&mut *rng);

        let mut t0 = a;
        t0.add_assign(&b);
        let mut t1 = c;
        t1.add_assign(&d);
        t0.mul_assign(&t1);

        let mut t2 = a;
        t2.mul_assign(&c);
        let mut t3 = b;
        t3.mul_assign(&c);
        let mut t4 = a;
        t4.mul_assign(&d);
        let mut t5 = b;
        t5.mul_assign(&d);

        t2.add_assign(&t3);
        t2.add_assign(&t4);
        t2.add_assign(&t5);

        assert_eq!(t0, t2);
    }
}
