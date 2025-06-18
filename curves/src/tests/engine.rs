use core::ops::MulAssign;

use ff::Field;
use group::{prime::PrimeCurveAffine, Curve, Group};
use pairing_lib::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

pub fn engine_tests<E: Engine + MultiMillerLoop>() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    for _ in 0..10 {
        let a = E::G1::random(&mut rng).to_affine();
        let b = E::G2::random(&mut rng).to_affine();

        assert!(a.pairing_with(&b) == b.pairing_with(&a));
        assert!(a.pairing_with(&b) == E::pairing(&a, &b));
    }

    for _ in 0..1000 {
        let z1 = E::G1Affine::identity();
        let z2 = E::G2Prepared::from(E::G2Affine::identity());

        let a = E::G1::random(&mut rng).to_affine();
        let b = E::G2Prepared::from(E::G2::random(&mut rng).to_affine());
        let c = E::G1::random(&mut rng).to_affine();
        let d = E::G2Prepared::from(E::G2::random(&mut rng).to_affine());

        assert_eq!(
            E::Gt::identity(),
            E::multi_miller_loop(&[(&z1, &b)]).final_exponentiation(),
        );

        assert_eq!(
            E::Gt::identity(),
            E::multi_miller_loop(&[(&a, &z2)]).final_exponentiation(),
        );

        assert_eq!(
            E::multi_miller_loop(&[(&z1, &b), (&c, &d)]).final_exponentiation(),
            E::multi_miller_loop(&[(&a, &z2), (&c, &d)]).final_exponentiation(),
        );

        assert_eq!(
            E::multi_miller_loop(&[(&a, &b), (&z1, &d)]).final_exponentiation(),
            E::multi_miller_loop(&[(&a, &b), (&c, &z2)]).final_exponentiation(),
        );
    }

    random_miller_loop_tests::<E>();
    random_bilinearity_tests::<E>();
}

fn random_miller_loop_tests<E: Engine + MultiMillerLoop>() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    // Exercise the miller loop for a reduced pairing
    for _ in 0..1000 {
        let a = E::G1::random(&mut rng).to_affine();
        let b = E::G2::random(&mut rng).to_affine();

        let p2 = E::pairing(&a, &b);

        let b = <E as MultiMillerLoop>::G2Prepared::from(b);
        let p1 = E::multi_miller_loop(&[(&a, &b)]).final_exponentiation();

        assert_eq!(p1, p2);
    }

    // Exercise a double miller loop
    for _ in 0..1000 {
        let a = E::G1::random(&mut rng).to_affine();
        let b = E::G2::random(&mut rng).to_affine();
        let c = E::G1::random(&mut rng).to_affine();
        let d = E::G2::random(&mut rng).to_affine();

        let ab = E::pairing(&a, &b);
        let cd = E::pairing(&c, &d);

        let abcd = ab + cd;

        let b = <E as MultiMillerLoop>::G2Prepared::from(b);
        let d = <E as MultiMillerLoop>::G2Prepared::from(d);

        let abcd_with_double_loop =
            E::multi_miller_loop(&[(&a, &b), (&c, &d)]).final_exponentiation();

        assert_eq!(abcd, abcd_with_double_loop);
    }
}

fn random_bilinearity_tests<E: Engine>() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    for _ in 0..1000 {
        let a = E::G1::random(&mut rng);
        let b = E::G2::random(&mut rng);

        let c = E::Fr::random(&mut rng);
        let d = E::Fr::random(&mut rng);

        let mut ac = a;
        ac.mul_assign(c);

        let mut ad = a;
        ad.mul_assign(d);

        let mut bc = b;
        bc.mul_assign(c);

        let mut bd = b;
        bd.mul_assign(d);

        // Check that `e([c]a, [d]b) == e([d]a, [c]b)`.
        let acbd = E::pairing(&ac.to_affine(), &bd.to_affine());
        let adbc = E::pairing(&ad.to_affine(), &bc.to_affine());
        assert_eq!(acbd, adbc);

        let cd = c * d;
        let acd = ac * d;
        let bcd = bc * d;

        // Check that `[d][c]a == [cd]a`.
        assert_eq!(acd, a * cd);
        assert_eq!(bcd, b * cd);

        // Check that `e([c]a, [d]b) == e([cd]a, b) == e(a, [cd]b) == [cd]e(a, b)`.
        assert_eq!(acbd, E::pairing(&acd.to_affine(), &b.to_affine()));
        assert_eq!(acbd, E::pairing(&a.to_affine(), &bcd.to_affine()));
        assert_eq!(acbd, E::pairing(&a.to_affine(), &b.to_affine()) * cd);
    }
}
