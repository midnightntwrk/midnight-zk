use std::io::{self, Read};

use ff::FromUniformBytes;
use midnight_circuits::hash::poseidon::{constants::PoseidonField, PoseidonState};
use midnight_proofs::transcript::{Hashable, Sampleable, TranscriptHash};

/// A type implementing `TranscriptHash` in a very unique and efficient way in
/// the case of elliptic curve points.
///
/// A point is double-hashed, first with SHA512 and then with Poseidon.
/// This allows us to represent points in-circuit very succinctly by their
/// SHA512 hash mapped into a field element. Such (succinctly represented) point
/// can then be digested into the Fiat-Shamir transcript with Poseidon.
///
/// The caveat of this technique is that the SHA512 hashing is designed to take
/// place off-circuit and thus, for the sake of soundness, it can only be used
/// for in-circuit points that will be declared public. That way, the
/// off-circuit verifier can hash with SHA512 when preparing the raw public
/// inputs vector.
#[derive(Clone, Debug)]
pub struct LightPoseidonFS<F: PoseidonField>(PoseidonState<F>);

impl<F: PoseidonField> From<PoseidonState<F>> for LightPoseidonFS<F> {
    fn from(value: PoseidonState<F>) -> Self {
        LightPoseidonFS(value)
    }
}

impl<F: PoseidonField> TranscriptHash for LightPoseidonFS<F> {
    type Input = Vec<F>;
    type Output = F;

    fn init() -> Self {
        <PoseidonState<F> as TranscriptHash>::init().into()
    }

    fn absorb(&mut self, input: &Self::Input) {
        <PoseidonState<F> as TranscriptHash>::absorb(&mut self.0, input)
    }

    fn squeeze(&mut self) -> Self::Output {
        <PoseidonState<F> as TranscriptHash>::squeeze(&mut self.0)
    }
}

impl Hashable<LightPoseidonFS<midnight_curves::Fq>> for midnight_curves::G1Projective {
    fn to_input(&self) -> Vec<midnight_curves::Fq> {
        use sha2::Digest;
        let bytes = Hashable::<LightPoseidonFS<midnight_curves::Fq>>::to_bytes(self);
        let digest_bytes: [u8; 64] = sha2::Sha512::digest(bytes).into();
        vec![midnight_curves::Fq::from_uniform_bytes(&digest_bytes)]
    }

    fn to_bytes(&self) -> Vec<u8> {
        <midnight_curves::G1Projective as Hashable<PoseidonState<midnight_curves::Fq>>>::to_bytes(
            self,
        )
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        <midnight_curves::G1Projective as Hashable<PoseidonState<midnight_curves::Fq>>>::read(
            buffer,
        )
    }
}

impl Hashable<LightPoseidonFS<midnight_curves::Fq>> for midnight_curves::Fq {
    fn to_input(&self) -> Vec<midnight_curves::Fq> {
        <midnight_curves::Fq as Hashable<PoseidonState<midnight_curves::Fq>>>::to_input(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <midnight_curves::Fq as Hashable<PoseidonState<midnight_curves::Fq>>>::to_bytes(self)
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        <midnight_curves::Fq as Hashable<PoseidonState<midnight_curves::Fq>>>::read(buffer)
    }
}

impl Sampleable<LightPoseidonFS<midnight_curves::Fq>> for midnight_curves::Fq {
    fn sample(out: midnight_curves::Fq) -> Self {
        out
    }
}
