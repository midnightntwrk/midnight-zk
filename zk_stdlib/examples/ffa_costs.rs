// [DROP] Measurement harness. Usage: cargo run --release -p midnight-zk-stdlib
// --example ffa_costs (env OPS=op1,op2 to select, K=16 for the circuit size,
// COST_REGIONS=1 for a per-region dump on stderr).
//! TEMPORARY measurement harness: rows of every foreign-field operation of
//! BLS12-381's base field over its scalar field, and of the point operations,
//! in the IVC circuit's architecture. Each operation is measured alone between
//! cost-model markers; its inputs are assigned before the window.

#![allow(clippy::redundant_clone, clippy::cloned_ref_to_slice_refs)]

use ff::{Field, PrimeField};
use group::Group;
use midnight_circuits::{
    instructions::*,
    types::{AssignedBit, AssignedField, AssignedNative},
};
use midnight_curves::{Fp, Fq as F, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, Value},
    dev::cost_model::{COST_MEASURE_END, COST_MEASURE_START},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
use rand::rngs::OsRng;

#[derive(Clone, Debug)]
struct Op(&'static str);

impl Relation for Op {
    type Instance = ();
    type Witness = ();
    type Error = Error;

    fn format_instance(_: &()) -> Result<Vec<F>, Error> {
        Ok(vec![])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _: Value<()>,
        _: Value<()>,
    ) -> Result<(), Error> {
        let ecc = std_lib.bls12_381();
        let fc = ecc.base_field_chip();

        // Inputs, outside the measured window.
        let a: AssignedField<F, Fp, G1Projective> =
            fc.assign(layouter, Value::known(Fp::random(OsRng)))?;
        let b: AssignedField<F, Fp, G1Projective> =
            fc.assign(layouter, Value::known(Fp::random(OsRng)))?;
        let c: AssignedField<F, Fp, G1Projective> =
            fc.assign(layouter, Value::known(Fp::random(OsRng)))?;
        let a_plus_b = fc.add(layouter, &a, &b)?;
        let bit: AssignedBit<F> = std_lib.assign(layouter, Value::known(true))?;
        let p: midnight_circuits::ecc::foreign::weierstrass_chip::AssignedForeignPoint<
            F,
            G1Projective,
            G1Projective,
        > = ecc.assign(layouter, Value::known(G1Projective::random(OsRng)))?;
        let q = ecc.assign(layouter, Value::known(G1Projective::random(OsRng)))?;
        let s1: AssignedNative<F> =
            std_lib.assign(layouter, Value::known(F::from_u128(u128::MAX)))?;
        let s2: AssignedNative<F> =
            std_lib.assign(layouter, Value::known(F::from_u128(u128::MAX - 7)))?;

        let _ = layouter.namespace(|| COST_MEASURE_START);
        match self.0 {
            // Foreign-field operations.
            "f_assign" => drop([
                fc.assign(layouter, Value::known(Fp::random(OsRng)))?,
                a.clone(),
            ]),
            "f_add" => drop(fc.add(layouter, &a, &b)?),
            "f_sub" => drop(fc.sub(layouter, &a, &b)?),
            "f_neg" => drop(fc.neg(layouter, &a)?),
            "f_add_constant" => drop(fc.add_constant(layouter, &a, Fp::from(5))?),
            "f_mul_by_constant" => drop(fc.mul_by_constant(layouter, &a, Fp::from(5))?),
            "f_mul" => drop(fc.mul(layouter, &a, &b, None)?),
            "f_square" => drop(fc.mul(layouter, &a, &a, None)?),
            "f_linear_comb_3" => drop(fc.linear_combination(
                layouter,
                &[
                    (Fp::from(2), a.clone()),
                    (Fp::from(3), b.clone()),
                    (Fp::from(5), c.clone()),
                ],
                Fp::ONE,
            )?),
            "f_div" => drop(fc.div(layouter, &a, &b)?),
            "f_inv" => drop(fc.inv(layouter, &a)?),
            "f_normalize" => drop(fc.normalize(layouter, &a_plus_b)?),
            "f_assert_equal" => fc.assert_equal(layouter, &a, &a)?,
            "f_is_equal" => drop(fc.is_equal(layouter, &a, &b)?),
            "f_is_zero" => drop(fc.is_zero(layouter, &a)?),
            "f_select" => drop(fc.select(layouter, &bit, &a, &b)?),
            // Point operations.
            "p_assign" => drop([
                ecc.assign(layouter, Value::known(G1Projective::random(OsRng)))?,
                p.clone(),
            ]),
            "p_incomplete_add" => drop(ecc.incomplete_add(layouter, &p, &q)?),
            "p_double" => drop(ecc.double(layouter, &p)?),
            "p_add" => drop(ecc.add(layouter, &p, &q)?),
            "p_negate" => drop(ecc.negate(layouter, &p)?),
            "p_msm_1x128" => {
                drop(ecc.msm_by_bounded_scalars(layouter, &[(s1.clone(), 128)], &[p.clone()])?)
            }
            "p_msm_2x128" => drop(ecc.msm_by_bounded_scalars(
                layouter,
                &[(s1.clone(), 128), (s2.clone(), 128)],
                &[p.clone(), q.clone()],
            )?),
            op => panic!("unknown op {op}"),
        }
        let _ = layouter.namespace(|| COST_MEASURE_END);
        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        // The IVC circuit's architecture.
        ZkStdLibArch {
            bls12_381: true,
            poseidon: true,
            nb_arith_cols: 9,
            nr_pow2range_cols: 8,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_: &mut R) -> std::io::Result<Self> {
        Ok(Op(""))
    }
}

fn main() {
    let k: u32 = std::env::var("K").map(|v| v.parse().unwrap()).unwrap_or(16);
    let ops: Vec<&'static str> = match std::env::var("OPS") {
        Ok(list) => list.split(',').map(|s| &*Box::leak(s.to_string().into_boxed_str())).collect(),
        Err(_) => vec![
            "f_assign",
            "f_add",
            "f_sub",
            "f_neg",
            "f_add_constant",
            "f_mul_by_constant",
            "f_mul",
            "f_square",
            "f_linear_comb_3",
            "f_div",
            "f_inv",
            "f_normalize",
            "f_assert_equal",
            "f_is_equal",
            "f_is_zero",
            "f_select",
            "p_assign",
            "p_incomplete_add",
            "p_double",
            "p_add",
            "p_negate",
            "p_msm_1x128",
            "p_msm_2x128",
        ],
    };
    for op in ops {
        eprintln!("BEGIN\t{op}");
        let model = midnight_zk_stdlib::cost_model(&Op(op), Some(k), false);
        println!("OP\t{op}\t{}", model.rows);
        eprintln!("END\t{op}");
    }
}
