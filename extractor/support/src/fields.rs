//! Re-exports of the field types used by the extractor.

use crate::{
    big_to_fe,
    cells::{ctx::ICtx, load::LoadFromCells},
    circuit::injected::InjectedIR,
    error::Error,
    fe_to_big,
};
use ff::PrimeField as _;
use midnight_proofs::{circuit::Layouter, halo2curves::group::cofactor::CofactorGroup};

pub use midnight_curves::Fp as MidnightFp;
pub use midnight_curves::Fq as Blstrs;
pub use midnight_curves::Fr as JubjubFr;
pub use midnight_curves::JubjubExtended as Jubjub;
pub use midnight_curves::JubjubSubgroup;

impl<C> LoadFromCells<Self, C> for Blstrs {
    fn load(
        ctx: &mut ICtx,
        _chip: &C,
        _layouter: &mut impl Layouter<Self>,
        _injected_ir: &mut InjectedIR<Self>,
    ) -> Result<Self, Error> {
        ctx.field_constant()
    }
}

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
