use core::{convert::TryFrom, fmt, marker::PhantomData};

use group::{prime::PrimeCurveAffine, Curve};
use serde::{
    de::{Error as DeserializeError, SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{
    fp::Fp, fp12::Fp12, fp2::Fp2, fp6::Fp6, Fq, G1Affine, G1Projective, G2Affine, G2Projective, Gt,
    MillerLoopResult,
};

const ERR_CODE: &str = "deserialized bytes don't encode a group element";

impl Serialize for G1Projective {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.to_affine().serialize(s)
    }
}

impl<'de> Deserialize<'de> for G1Projective {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(G1Affine::deserialize(d)?.to_curve())
    }
}

impl Serialize for G1Affine {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        serialize_affine(self, s)
    }
}

impl<'de> Deserialize<'de> for G1Affine {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        deserialize_affine(d)
    }
}

impl Serialize for G2Projective {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.to_affine().serialize(s)
    }
}

impl<'de> Deserialize<'de> for G2Projective {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(G2Affine::deserialize(d)?.to_curve())
    }
}

impl Serialize for G2Affine {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        serialize_affine(self, s)
    }
}

impl<'de> Deserialize<'de> for G2Affine {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        deserialize_affine(d)
    }
}

/// Serialize a group element using its compressed representation.
fn serialize_affine<S: Serializer, C: PrimeCurveAffine>(c: &C, s: S) -> Result<S::Ok, S::Error> {
    let compressed_bytes = c.to_bytes();
    let len = compressed_bytes.as_ref().len();
    let mut tup = s.serialize_tuple(len)?;
    for byte in compressed_bytes.as_ref() {
        tup.serialize_element(byte)?;
    }
    tup.end()
}

/// Deserializes the compressed representation of a group element.
fn deserialize_affine<'de, D: Deserializer<'de>, C: PrimeCurveAffine>(d: D) -> Result<C, D::Error> {
    struct TupleVisitor<C> {
        _ph: PhantomData<C>,
    }

    impl<'de, C: PrimeCurveAffine> Visitor<'de> for TupleVisitor<C> {
        type Value = C;

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let len = C::Repr::default().as_ref().len();
            write!(f, "a tuple of {} bytes", len)
        }

        #[inline]
        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<C, A::Error> {
            let mut compressed = C::Repr::default();
            for (i, byte) in compressed.as_mut().iter_mut().enumerate() {
                let len_err = || DeserializeError::invalid_length(i, &self);
                *byte = seq.next_element()?.ok_or_else(len_err)?;
            }
            let opt = C::from_bytes(&compressed);
            if opt.is_some().into() {
                Ok(opt.unwrap())
            } else {
                Err(DeserializeError::custom(ERR_CODE))
            }
        }
    }

    let len = C::Repr::default().as_ref().len();
    d.deserialize_tuple(len, TupleVisitor { _ph: PhantomData })
}

impl Serialize for Fq {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let bytes = self.to_bytes_le();
        let u64s = [
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap()),
        ];
        u64s.serialize(s)
    }
}

impl<'de> Deserialize<'de> for Fq {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let deser = <[u64; 4]>::deserialize(d)?;
        match Fq::from_u64s_le(&deser).into() {
            Some(scalar) => Ok(scalar),
            None => Err(D::Error::custom(ERR_CODE)),
        }
    }
}

impl Serialize for Fp {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let bytes = self.to_bytes_le();
        let u64s = [
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap()),
        ];
        u64s.serialize(s)
    }
}

impl<'de> Deserialize<'de> for MillerLoopResult {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let fp12 = Fp12::deserialize(d)?;
        Ok(MillerLoopResult(fp12))
    }
}

impl Serialize for MillerLoopResult {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(s)
    }
}

impl<'de> Deserialize<'de> for Gt {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let fp12 = Fp12::deserialize(d)?;
        Ok(Gt(fp12))
    }
}

impl Serialize for Gt {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(s)
    }
}

#[derive(Serialize, Deserialize)]
struct Fp2Ser {
    c0: Fp,
    c1: Fp,
}

#[derive(Serialize, Deserialize)]
struct Fp6Ser {
    c0: Fp2,
    c1: Fp2,
    c2: Fp2,
}

#[derive(Serialize, Deserialize)]
struct Fp12Ser {
    c0: Fp6,
    c1: Fp6,
}

impl Serialize for Fp2 {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        Fp2Ser {
            c0: self.c0(),
            c1: self.c1(),
        }
        .serialize(s)
    }
}

impl Serialize for Fp12 {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        Fp12Ser {
            c0: self.c0(),
            c1: self.c1(),
        }
        .serialize(s)
    }
}

impl Serialize for Fp6 {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        Fp6Ser {
            c0: self.c0(),
            c1: self.c1(),
            c2: self.c2(),
        }
        .serialize(s)
    }
}

impl<'de> Deserialize<'de> for Fp {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let deser = <[u64; 6]>::deserialize(d)?;
        match Fp::from_u64s_le(&deser).into() {
            Some(fp) => Ok(fp),
            None => Err(D::Error::custom(ERR_CODE)),
        }
    }
}

impl<'de> Deserialize<'de> for Fp2 {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let Fp2Ser { c0, c1 } = Fp2Ser::deserialize(d)?;
        Ok(Fp2::new(c0, c1))
    }
}

impl<'de> Deserialize<'de> for Fp6 {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let Fp6Ser { c0, c1, c2 } = Fp6Ser::deserialize(d)?;
        Ok(Fp6::new(c0, c1, c2))
    }
}

impl<'de> Deserialize<'de> for Fp12 {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let Fp12Ser { c0, c1 } = Fp12Ser::deserialize(d)?;
        Ok(Fp12::new(c0, c1))
    }
}

#[cfg(test)]
mod tests {
    use core::fmt::Debug;

    use ff::Field;
    use group::{Curve, Group};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::*;

    fn test_roundtrip<T: Serialize + for<'a> Deserialize<'a> + Debug + PartialEq>(t: &T) {
        // dbg!(t);
        let ser = serde_json::to_vec(t).unwrap();
        assert_eq!(*t, serde_json::from_slice(&ser).unwrap());
    }

    #[test]
    fn serde_g1() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let g = G1Projective::random(&mut rng);
            test_roundtrip(&g);
            test_roundtrip(&g.to_affine());
        }

        let g = G1Projective::identity();
        test_roundtrip(&g);
        assert_eq!(
            serde_json::from_slice::<G1Projective>(&hex::decode("5b3139322c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c305d").unwrap()).unwrap(),
            g
        );
        test_roundtrip(&g.to_affine());
        assert_eq!(
            serde_json::from_slice::<G1Affine>(&hex::decode("5b3139322c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c305d").unwrap()).unwrap(),
            g.to_affine(),
        );

        let g = G1Projective::generator();
        test_roundtrip(&g);
        assert_eq!(
            serde_json::from_slice::<G1Projective>(&hex::decode("5b3135312c3234312c3231312c3136372c34392c3135312c3231352c3134382c33382c3134392c39392c3134302c37392c3136392c3137322c31352c3139352c3130342c3134302c37392c3135312c3131362c3138352c352c3136312c37382c35382c36332c32332c32372c3137322c38382c3130382c38352c3233322c36332c3234392c3132322c32362c3233392c3235312c35382c3234302c31302c3231392c33342c3139382c3138375d").unwrap()).unwrap(),
            g
        );
        test_roundtrip(&g.to_affine());
        assert_eq!(
            serde_json::from_slice::<G1Affine>(&hex::decode("5b3135312c3234312c3231312c3136372c34392c3135312c3231352c3134382c33382c3134392c39392c3134302c37392c3136392c3137322c31352c3139352c3130342c3134302c37392c3135312c3131362c3138352c352c3136312c37382c35382c36332c32332c32372c3137322c38382c3130382c38352c3233322c36332c3234392c3132322c32362c3233392c3235312c35382c3234302c31302c3231392c33342c3139382c3138375d").unwrap()).unwrap(),
            g.to_affine(),
        );
    }

    #[test]
    fn serde_g2() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let g = G2Projective::random(&mut rng);
            test_roundtrip(&g);
            test_roundtrip(&g.to_affine());
        }

        let g = G2Projective::identity();
        test_roundtrip(&g);
        assert_eq!(
            serde_json::from_slice::<G2Projective>(&hex::decode("5b3139322c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c305d").unwrap()).unwrap(),
            g
        );
        test_roundtrip(&g.to_affine());
        assert_eq!(
            serde_json::from_slice::<G2Affine>(&hex::decode("5b3139322c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c302c305d").unwrap()).unwrap(),
            g.to_affine(),
        );

        let g = G2Projective::generator();
        test_roundtrip(&g);
        assert_eq!(
            serde_json::from_slice::<G2Projective>(&hex::decode("5b3134372c3232342c34332c39362c38322c3131332c3135392c39362c3132352c3137322c3231312c3136302c3133362c33392c37392c3130312c38392c3130372c3230382c3230382c3135332c33322c3138322c32362c3138312c3231382c39372c3138372c3232302c3132372c38302c37332c35312c37362c3234312c31382c31392c3134382c39332c38372c3232392c3137322c3132352c352c39332c342c34332c3132362c322c37342c3136322c3137382c3234302c3134332c31302c3134352c33382c382c352c33392c34352c3139372c31362c38312c3139382c3232382c3132322c3231322c3235302c36342c35392c322c3138302c38312c31312c3130302c3132322c3232372c3230392c3131392c31312c3137322c332c33382c3136382c352c3138372c3233392c3231322c3132382c38362c3230302c3139332c33332c3138392c3138345d").unwrap()).unwrap(),
            g
        );
        test_roundtrip(&g.to_affine());
        assert_eq!(
            serde_json::from_slice::<G2Affine>(&hex::decode("5b3134372c3232342c34332c39362c38322c3131332c3135392c39362c3132352c3137322c3231312c3136302c3133362c33392c37392c3130312c38392c3130372c3230382c3230382c3135332c33322c3138322c32362c3138312c3231382c39372c3138372c3232302c3132372c38302c37332c35312c37362c3234312c31382c31392c3134382c39332c38372c3232392c3137322c3132352c352c39332c342c34332c3132362c322c37342c3136322c3137382c3234302c3134332c31302c3134352c33382c382c352c33392c34352c3139372c31362c38312c3139382c3232382c3132322c3231322c3235302c36342c35392c322c3138302c38312c31312c3130302c3132322c3232372c3230392c3131392c31312c3137322c332c33382c3136382c352c3138372c3233392c3231322c3132382c38362c3230302c3139332c33332c3138392c3138345d").unwrap()).unwrap(),
            g.to_affine()
        );
    }

    #[test]
    fn serde_scalar() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..100 {
            let f = Fq::random(&mut rng);
            test_roundtrip(&f);
        }

        let f = Fq::ZERO;
        test_roundtrip(&f);
        // The hex string "5b302c302c302c305d" encodes the unicode string "[0,0,0,0]"
        // where each byte in the hex string encodes a unicode character: 0x58 =
        // "[", 0x30 = "0", 0x2c = ",", and 0x5d = "]".
        assert_eq!(
            serde_json::from_slice::<Fq>(&hex::decode("5b302c302c302c305d").unwrap()).unwrap(),
            f
        );

        let f = Fq::ONE;
        test_roundtrip(&f);
        assert_eq!(
            serde_json::from_slice::<Fq>(&hex::decode("5b312c302c302c305d").unwrap()).unwrap(),
            f
        );
    }

    #[test]
    fn serde_fp() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let f = Fp::random(&mut rng);
            test_roundtrip(&f);
        }

        let f = Fp::ZERO;
        test_roundtrip(&f);
        assert_eq!(
            serde_json::from_slice::<Fp>(&hex::decode("5b302c302c302c302c302c305d").unwrap())
                .unwrap(),
            f
        );

        let f = Fp::ONE;
        test_roundtrip(&f);
        assert_eq!(
            serde_json::from_slice::<Fp>(&hex::decode("5b312c302c302c302c302c305d").unwrap())
                .unwrap(),
            f
        );
    }

    #[test]
    fn serde_fp12() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..100 {
            let f = Fp12::random(&mut rng);
            test_roundtrip(&f);
        }

        let f = Fp12::ZERO;
        test_roundtrip(&f);
        assert_eq!(
            serde_json::from_slice::<Fp12>(&hex::decode("7b226330223a7b226330223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226331223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226332223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d7d2c226331223a7b226330223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226331223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226332223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d7d7d").unwrap()).unwrap(),
            f
        );

        let f = Fp12::ONE;
        test_roundtrip(&f);
        assert_eq!(
            serde_json::from_slice::<Fp12>(&hex::decode("7b226330223a7b226330223a7b226330223a5b312c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226331223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226332223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d7d2c226331223a7b226330223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226331223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d2c226332223a7b226330223a5b302c302c302c302c302c305d2c226331223a5b302c302c302c302c302c305d7d7d7d").unwrap()).unwrap(),
            f
        );
    }
}
