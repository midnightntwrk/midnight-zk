//! Examples on how to perform ECC operations using the ECC Chip inside of
//! ZkStdLib.

use ff::Field;
use group::Group;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    hash::poseidon::PoseidonChip,
    instructions::{
        hash::HashCPU, AssertionInstructions, AssignmentInstructions, ConversionInstructions,
        EccInstructions, PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedNative, AssignedNativePoint, Instantiable},
};
use midnight_curves::{Fr as JubjubScalar, JubjubAffine, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

type F = midnight_curves::Fq;

// A jubjub scalar, represented as a native field of the circuit.
#[derive(Clone, Default)]
struct Scalar(F);

impl From<F> for Scalar {
    fn from(value: F) -> Self {
        Self(value)
    }
}

impl From<JubjubScalar> for Scalar {
    fn from(value: JubjubScalar) -> Self {
        // Scalar elements always fit in F.
        Scalar(F::from_bytes_le(&value.to_bytes()).unwrap())
    }
}

impl Scalar {
    fn to_scalar(&self) -> JubjubScalar {
        // Creates a scalar by reducing the native value mod r.
        let mut buff = [0u8; 64];
        buff[..32].copy_from_slice(&self.0.to_bytes_le());
        JubjubScalar::from_bytes_wide(&buff)
    }
}

#[derive(Clone, Default)]
pub struct SchnorrSignature {
    s: Scalar,
    e: Scalar,
}

type SchnorrPK = JubjubSubgroup;

type SchnorrSK = JubjubScalar;

type Message = F;

#[derive(Clone, Default)]
pub struct SchnorrExample;

fn keygen(mut rng: impl RngCore) -> (SchnorrPK, SchnorrSK) {
    let sk = JubjubScalar::random(&mut rng);
    let pk = JubjubSubgroup::generator() * (-sk);
    (pk, sk)
}

fn sign(message: Message, secret_key: SchnorrSK, mut rng: impl RngCore) -> SchnorrSignature {
    let k = JubjubScalar::random(&mut rng);
    let r = JubjubSubgroup::generator() * k;

    let (x, y) = get_coords(r);

    let e = Scalar(PoseidonChip::hash(&[x, y, message]));
    let s = k + e.to_scalar() * secret_key;

    SchnorrSignature { s: s.into(), e }
}

fn verify(sig: SchnorrSignature, pk: SchnorrPK, m: Message) -> Result<(), Error> {
    // 1. rv= s * G + e * Pk
    let rv = JubjubSubgroup::generator() * sig.s.to_scalar() + pk * sig.e.to_scalar();

    let (x, y) = get_coords(rv);

    // 2. ev = hash( x || y || m)
    let ev = PoseidonChip::hash(&[x, y, m]);

    assert_eq!(ev, sig.e.0);
    Ok(())
}

// Returns the affine coordinates of a given Jubjub point.
fn get_coords(point: JubjubSubgroup) -> (F, F) {
    let point: Jubjub = point.into();
    let point: JubjubAffine = point.into();
    (point.get_u(), point.get_v())
}

impl Relation for SchnorrExample {
    type Instance = (SchnorrSignature, SchnorrPK, Message);
    type Witness = ();

    fn format_instance(instance: &Self::Instance) -> Vec<F> {
        let sig_s = instance.0.s.0;
        let sig_e = instance.0.e.0;
        let pk = AssignedNativePoint::<Jubjub>::as_public_input(&instance.1);
        let m = instance.2;
        [vec![sig_s, sig_e], pk, vec![m]].concat()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        _witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        // Jubjub chip.
        let jubjub = &std_lib.jubjub();

        // Assign public inputs.
        let (sig_s_val, sig_e_val) = instance
            .clone()
            .map(|(sig, _, _)| (sig.s.0, sig.e.0))
            .unzip();
        let (pk_val, m_val) = instance.map(|(_, pk, m)| (pk, m)).unzip();

        let sig_s: AssignedNative<F> = std_lib.assign_as_public_input(layouter, sig_s_val)?;
        let sig_e: AssignedNative<F> = std_lib.assign_as_public_input(layouter, sig_e_val)?;

        let pk = jubjub.assign_as_public_input(layouter, pk_val)?;
        let message = std_lib.assign_as_public_input(layouter, m_val)?;

        let generator: AssignedNativePoint<Jubjub> = std_lib
            .jubjub()
            .assign_fixed(layouter, <JubjubSubgroup as Group>::generator())?;

        let sig_s_scalar = jubjub.convert(layouter, &sig_s)?;
        let sig_e_scalar = jubjub.convert(layouter, &sig_e)?;

        // 1. rv= s * G + e * Pk
        let rv = std_lib
            .jubjub()
            .msm(layouter, &[sig_s_scalar, sig_e_scalar], &[generator, pk])?;

        let x = jubjub.x_coordinate(&rv);
        let y = jubjub.y_coordinate(&rv);

        // 2. ev = hash( x || y || m)
        let ev = std_lib.poseidon(layouter, &[x, y, message])?;

        std_lib.assert_equal(layouter, &ev, &sig_e)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: true,
            poseidon: true,
            sha256: None,
            secp256k1: false,
            bls12_381: false,
            base64: false,
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(SchnorrExample)
    }
}
fn main() {
    const K: u32 = 11;

    let srs = filecoin_srs(K);
    let mut rng = ChaCha8Rng::seed_from_u64(0xf001ba11);

    let relation = SchnorrExample;
    let vk = compact_std_lib::setup_vk(&srs, &relation);
    let pk = compact_std_lib::setup_pk(&relation, &vk);

    const N: usize = 5;

    let mut vks = vec![];
    let mut proofs = vec![];
    let mut instances = vec![];

    for _ in 0..N {
        let (schnorr_pk, sk) = keygen(&mut rng);
        let m = F::random(&mut rng);
        let sig = sign(m, sk, &mut rng);

        // sanity check
        assert!(verify(sig.clone(), schnorr_pk, m).is_ok());

        let instance = (sig, schnorr_pk, m);

        let proof = compact_std_lib::prove::<SchnorrExample, blake2b_simd::State>(
            &srs,
            &pk,
            &relation,
            &instance,
            (),
            &mut rng,
        )
        .expect("Proof generation should not fail");

        let instance = SchnorrExample::format_instance(&instance);

        vks.push(vk.clone());
        instances.push(instance);
        proofs.push(proof);
    }

    assert!(compact_std_lib::batch_verify::<blake2b_simd::State>(
        &srs.verifier_params(),
        &vks,
        &instances,
        &proofs
    )
    .is_ok())
}
