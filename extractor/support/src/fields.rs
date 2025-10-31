//! Re-exports of the field types used by the extractor.

use ff::PrimeField as _;
pub use midnight_curves::{
    Fp as MidnightFp, Fq as Blstrs, Fr as JubjubFr, G1Projective as G1, JubjubExtended as Jubjub,
    JubjubSubgroup,
};
use midnight_proofs::circuit::Layouter;
pub use midnight_proofs::halo2curves::secp256k1::{
    Fp as Secp256k1Fp, Fq as Secp256k1Fq, Secp256k1,
};

use crate::{
    big_to_fe,
    cells::{ctx::ICtx, load::LoadFromCells},
    circuit::injected::InjectedIR,
    error::Error,
    fe_to_big,
};

macro_rules! load_impl {
    ($t:ty) => {
        impl<C> LoadFromCells<Blstrs, C> for $t {
            fn load(
                ctx: &mut ICtx,
                _chip: &C,
                _layouter: &mut impl Layouter<Blstrs>,
                _injected_ir: &mut InjectedIR<Blstrs>,
            ) -> Result<Self, Error> {
                ctx.field_constant()
            }
        }
    };
}

load_impl!(Blstrs);
load_impl!(MidnightFp);
load_impl!(Secp256k1Fp);
load_impl!(Secp256k1Fq);

impl<C> LoadFromCells<Blstrs, C> for JubjubFr {
    fn load(
        ctx: &mut ICtx,
        chip: &C,
        layouter: &mut impl Layouter<Blstrs>,
        injected_ir: &mut InjectedIR<Blstrs>,
    ) -> Result<Self, Error> {
        assert!(
            Blstrs::NUM_BITS >= JubjubFr::NUM_BITS,
            "Loading foreign fields larger than native currently not supported"
        );
        let f = Blstrs::load(ctx, chip, layouter, injected_ir)?;
        Ok(big_to_fe::<JubjubFr>(fe_to_big(f)))
    }
}
