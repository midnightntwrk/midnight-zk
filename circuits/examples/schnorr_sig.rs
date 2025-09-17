//! Example of a variation of the Schnorr Signature scheme.
//!
//! It uses a native hash function (Poseidon) and a native elliptic curve
//! (Jubjub) to maximize efficiency.

use ff::Field;
use group::Group;
use midnight_circuits::{
    compact_std_lib::{self, Relation, ZkStdLib, ZkStdLibArch},
    ecc::native::AssignedScalarOfNativeCurve,
    hash::poseidon::PoseidonChip,
    instructions::{
        hash::HashCPU, AssertionInstructions, AssignmentInstructions, DecompositionInstructions,
        EccInstructions, PublicInputInstructions,
    },
    testing_utils::plonk_api::filecoin_srs,
    types::{AssignedNativePoint, Instantiable},
};
use midnight_curves::{Fr as JubjubScalar, JubjubAffine, JubjubExtended as Jubjub, JubjubSubgroup};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

type F = midnight_curves::Fq;

#[derive(Clone, Default)]
pub struct SchnorrSignature {
    s: JubjubScalar,
    e_bytes: [u8; 32],
}

type SchnorrPK = JubjubSubgroup;
type SchnorrSK = JubjubScalar;
type Message = F;

fn keygen(mut rng: impl RngCore) -> (SchnorrPK, SchnorrSK) {
    let sk = JubjubScalar::random(&mut rng);
    let pk = JubjubSubgroup::generator() * sk;
    (pk, sk)
}

fn sign(message: Message, secret_key: &SchnorrSK, mut rng: impl RngCore) -> SchnorrSignature {
    let k = JubjubScalar::random(&mut rng);
    let r = JubjubSubgroup::generator() * k;

    let (rx, ry) = get_coords(&r);
    let (pkx, pky) = get_coords(&(JubjubSubgroup::generator() * secret_key));

    let h = PoseidonChip::hash(&[pkx, pky, rx, ry, message]);
    let e_bytes = h.to_bytes_le();

    let s = {
        let mut buff = [0u8; 64];
        buff[..32].copy_from_slice(&e_bytes);
        let e = JubjubScalar::from_bytes_wide(&buff);
        k - e * secret_key
    };

    SchnorrSignature { s, e_bytes }
}

fn verify(sig: &SchnorrSignature, pk: &SchnorrPK, m: Message) -> bool {
    let mut buff = [0u8; 64];
    buff[..32].copy_from_slice(&sig.e_bytes);
    let e = JubjubScalar::from_bytes_wide(&buff);

    // 1. rv = s * G + e * Pk
    let rv = JubjubSubgroup::generator() * sig.s + pk * e;

    let (rx, ry) = get_coords(&rv);
    let (pkx, pky) = get_coords(pk);

    // 2. ev = hash( PK.x || PK.y || r.x || r.y || m)
    let h = PoseidonChip::hash(&[pkx, pky, rx, ry, m]);

    h.to_bytes_le() == sig.e_bytes
}

// Returns the affine coordinates of a given Jubjub point.
fn get_coords(point: &JubjubSubgroup) -> (F, F) {
    let point: &Jubjub = point.into();
    let point: JubjubAffine = point.into();
    (point.get_u(), point.get_v())
}

#[derive(Clone, Default)]
pub struct SchnorrExample;

impl Relation for SchnorrExample {
    type Instance = (SchnorrPK, Message);
    type Witness = SchnorrSignature;

    fn format_instance((pk, msg): &Self::Instance) -> Vec<F> {
        [
            AssignedNativePoint::<Jubjub>::as_public_input(pk),
            vec![*msg],
        ]
        .concat()
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let jubjub = &std_lib.jubjub();

        // Assign public inputs.
        let (pk_val, m_val) = instance.map(|(pk, m)| (pk, m)).unzip();
        let pk: AssignedNativePoint<Jubjub> = jubjub.assign_as_public_input(layouter, pk_val)?;
        let message = std_lib.assign_as_public_input(layouter, m_val)?;

        // Assign witness values.
        let (sig_s_val, sig_e_bytes_val) = witness.map(|sig| (sig.s, sig.e_bytes)).unzip();
        let sig_s: AssignedScalarOfNativeCurve<Jubjub> =
            std_lib.jubjub().assign(layouter, sig_s_val)?;
        let sig_e_bytes = std_lib.assign_many(layouter, &sig_e_bytes_val.transpose_array())?;

        let generator: AssignedNativePoint<Jubjub> =
            (std_lib.jubjub()).assign_fixed(layouter, <JubjubSubgroup as Group>::generator())?;

        let sig_e = std_lib.jubjub().scalar_from_le_bytes(layouter, &sig_e_bytes)?;

        // 1. rv = s * G + e * Pk
        let rv =
            (std_lib.jubjub()).msm(layouter, &[sig_s, sig_e.clone()], &[generator, pk.clone()])?;

        let coords = |p| (jubjub.x_coordinate(p), jubjub.y_coordinate(p));
        let (pkx, pky) = coords(&pk);
        let (rx, ry) = coords(&rv);

        // 2. ev = hash( PK.x || PK.y || r.x || r.y || m)
        let h = std_lib.poseidon(layouter, &[pkx, pky, rx, ry, message])?;
        let ev_bytes = std_lib.assigned_to_le_bytes(layouter, &h, None)?;

        assert_eq!(ev_bytes.len(), sig_e_bytes.len());
        (ev_bytes.iter().zip(sig_e_bytes.iter()))
            .try_for_each(|(ev, e)| std_lib.assert_equal(layouter, ev, e))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            jubjub: true,
            poseidon: true,
            sha256: false,
            secp256k1: false,
            bls12_381: false,
            base64: false,
            automaton: false,
            nr_pow2range_cols: 1,
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
        let sig = sign(m, &sk, &mut rng);

        // sanity check
        assert!(verify(&sig, &schnorr_pk, m));

        let instance = (schnorr_pk, m);

        let proof = compact_std_lib::prove::<SchnorrExample, blake2b_simd::State>(
            &srs, &pk, &relation, &instance, sig, &mut rng,
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
