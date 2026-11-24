// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0

use ff::{Field, WithSmallOrderMulGroup};
use midnight_curves::{Fq, fft::best_fft};
use midnight_gpu as gpu;
use midnight_proofs::{
    gpu::{
        QuotientDivide, QuotientJob, abi::PackedJob, adapter, test_switches::custom_gate_numerator,
    },
    plonk::{Advice, Column, ConstraintSystem, Constraints, Expression, Fixed, Instance},
    poly::{EvaluationDomain, ExtendedLagrangeCoeff, FftDomain, Polynomial},
};
use serde_json::Value;

use super::{
    check_hook, equal, field, fields, reason, scale_powers, stock_transform, uint, without_hooks,
};

struct Columns {
    fixed: Vec<Column<Fixed>>,
    advice: Vec<Column<Advice>>,
    instance: Vec<Column<Instance>>,
}

impl Columns {
    fn expression(&self, node: &Value, challenges: &[Fq]) -> Expression<Fq> {
        let arg = |key: &str| self.expression(&node[key], challenges);
        let col = || uint(&node["column"]) as usize;
        let rot = || i32::try_from(node["rotation"].as_i64().unwrap()).unwrap();
        match node["node"].as_str().unwrap() {
            "constant" => Expression::Constant(field(&node["value"])),
            // The vector supplies each challenge; fold it into a uniform literal.
            "challenge" => Expression::Constant(challenges[uint(&node["index"]) as usize]),
            "fixed" => self.fixed[col()].rot(rot()),
            "advice" => self.advice[col()].rot(rot()),
            "instance" => self.instance[col()].rot(rot()),
            "negated" => -arg("arg"),
            "sum" => arg("left") + arg("right"),
            "product" => arg("left") * arg("right"),
            "scaled" => arg("arg") * field(&node["scalar"]),
            other => panic!("unknown gate node {other}"),
        }
    }
}

type Extended = Polynomial<Fq, ExtendedLagrangeCoeff>;

fn columns(d: &EvaluationDomain<Fq>, json: &Value) -> Vec<Extended> {
    json.as_array()
        .unwrap()
        .iter()
        .map(|col| {
            let mut p = d.empty_extended();
            p.copy_from_slice(&fields(col));
            p
        })
        .collect()
}

// A fixture's arbitrary N evaluations need not be one degree-<n proof
// polynomial. Each residue modulo N/n is closed under every gate rotation.
// Interpolate its n samples on that base coset. At rows in this residue the
// real coefficient-input hook then sees exactly the fixture's original cells.
fn interpolate(
    cols: &[Extended],
    d: &EvaluationDomain<Fq>,
    residue: usize,
    ratio: usize,
    zeta: Fq,
) -> Vec<Vec<Fq>> {
    let shift = zeta * d.get_extended_omega().pow_vartime([residue as u64]);
    let shift_inv = shift.invert().unwrap();
    let divisor = Fq::from(1u64 << d.k()).invert().unwrap();
    cols.iter()
        .map(|col| {
            let rows: Vec<_> = col.iter().skip(residue).step_by(ratio).copied().collect();
            let mut coeffs = stock_transform(&rows, d.get_omega_inv(), d.k(), Some(divisor));
            scale_powers(&mut coeffs, shift_inv);
            coeffs
        })
        .collect()
}

// Return coefficients, the only quotient result that crosses back to the
// caller.
fn hook(job: &QuotientJob<'_, Fq>, why: Option<&str>) -> Option<Vec<Fq>> {
    let packed = PackedJob::new(job);
    let mut out = vec![Fq::from(17); job.divide.len];
    let taken = check_hook(
        "quotient",
        || gpu::stats().quotient,
        why,
        || {
            // SAFETY: the job and all slices live through this synchronous call.
            unsafe { gpu::quotient(packed.as_ptr(), adapter::scalars_mut(&mut out)) }
        },
    );
    if !taken {
        assert!(
            out.iter().all(|&x| x == Fq::from(17)),
            "declined quotient changed output"
        );
    }
    taken.then_some(out)
}

pub(super) fn coset(
    d: &EvaluationDomain<Fq>,
    coeffs: &[Fq],
    expected: &[Fq],
    z: Fq,
    why: Option<&str>,
) {
    // The gate subtracts the fixture's extended column from the kernel's coset.
    // Every quotient coefficient vanishes iff every extended cell matches.
    let mut cs = ConstraintSystem::default();
    let adv = cs.advice_column();
    let fixed = cs.fixed_column();
    cs.create_gate("oracle coset difference", |_| {
        Constraints::without_selector(vec![adv.rot(0) - fixed.rot(0)])
    });
    let mut oracle = d.empty_extended();
    oracle.copy_from_slice(expected);
    let (_, gates) = custom_gate_numerator(
        &cs,
        [&[oracle.clone()], &[oracle], &[]],
        d.extended_k(),
        d.extended_k() - d.k(),
        Fq::ONE,
    );
    let zero = d.empty_extended();
    let job = QuotientJob {
        k: d.k(),
        ext_k: d.extended_k(),
        zeta: [z, z.square()],
        extended_omega: d.get_extended_omega(),
        advice: vec![coeffs],
        instance: vec![],
        fixed: vec![Some(expected)],
        l0: &zero,
        l_last: &zero,
        l_active: &zero,
        y: Fq::ONE,
        beta: Fq::ZERO,
        gamma: Fq::ZERO,
        delta_start: Fq::ZERO,
        delta: Fq::ZERO,
        gates,
        permutation: None,
        lookups: vec![],
        trash: vec![],
        divide: QuotientDivide {
            t_inv: vec![Fq::ONE],
            omega_inv: d.get_extended_omega().invert().unwrap(),
            divisor: Fq::from(expected.len() as u64).invert().unwrap(),
            zeta_out: [z.square(), z],
            len: expected.len(),
        },
    };
    if let Some(h) = hook(&job, why) {
        assert!(
            h.iter().all(|x| *x == Fq::ZERO),
            "quotient coset differs from the fixture"
        );
    }
}

pub(super) fn run(case: &Value, lane: super::Lane) -> bool {
    let n_ext = uint(&case["extended_size"]);
    let ratio = uint(&case["ratio"]);
    assert!(n_ext.is_power_of_two() && ratio.is_power_of_two() && ratio <= n_ext);
    let k = (n_ext / ratio).ilog2();
    let d = EvaluationDomain::new(ratio + 1, k);
    let fd = FftDomain::new(&d);
    let ext_k = d.extended_k();
    let w = d.get_extended_omega();
    let z = case.get("zeta").map_or(Fq::ZETA, field);
    if case.get("quotient_coeffs").is_some() {
        assert_eq!(uint(&case["n"]), 1 << k);
        assert_eq!(field(&case["omega_ext"]), w);
    }
    let ratio = ratio as usize;
    let y = field(&case["y"]);
    let challenges = fields(&case["challenges"]);
    let [fixed, advice, instance] =
        ["fixed", "advice", "instance"].map(|key| columns(&d, &case[key]));
    let mut cs = ConstraintSystem::default();
    let col = Columns {
        fixed: fixed.iter().map(|_| cs.fixed_column()).collect(),
        advice: advice.iter().map(|_| cs.advice_column()).collect(),
        instance: instance.iter().map(|_| cs.instance_column()).collect(),
    };
    let expressions: Vec<_> = case["gates"]
        .as_array()
        .unwrap()
        .iter()
        .map(|g| col.expression(g, &challenges))
        .collect();
    if !expressions.is_empty() {
        cs.create_gate("oracle gates", |_| {
            Constraints::without_selector(expressions)
        });
    }
    let evaluate = |advice: &[Extended], instance: &[Extended]| {
        custom_gate_numerator(&cs, [&fixed, advice, instance], ext_k, ratio.ilog2(), y)
    };
    let (stock, gates) = without_hooks(|| evaluate(&advice, &instance));
    let expected = fields(&case["numerator"]);
    equal(&stock, &expected, "stock quotient numerator");

    let zero = d.empty_extended();
    // The oracle may choose the conjugate of the stock domain's cube root.
    let twiddle = w.pow_vartime([1u64 << k]);
    let mut x_n = z.pow_vartime([1u64 << k]);
    let t_inv: Vec<_> = (0..ratio)
        .map(|_| {
            let inv = (x_n - Fq::ONE).invert().unwrap();
            x_n *= twiddle;
            inv
        })
        .collect();
    let inverse_coset = |divided: Extended| {
        let mut coeffs = fd.extended_to_coeff(divided);
        scale_powers(&mut coeffs, Fq::ZETA * z.invert().unwrap());
        coeffs
    };
    let divide = |numerator: &[Fq]| {
        let mut p = d.empty_extended();
        p.copy_from_slice(numerator);
        if z == Fq::ZETA {
            return d.divide_by_vanishing_poly(p);
        }
        for (r, v) in p.iter_mut().enumerate() {
            *v *= t_inv[r % ratio];
        }
        p
    };
    if let Some(coeffs) = case.get("quotient_coeffs") {
        equal(
            &inverse_coset(divide(&stock)),
            &fields(coeffs),
            "stock quotient coefficients",
        );
    }
    if lane == super::Lane::Cpu {
        return true;
    }
    let mut divided = d.empty_extended();
    for residue in 0..ratio {
        let a = interpolate(&advice, &d, residue, ratio, z);
        let i = interpolate(&instance, &d, residue, ratio, z);
        let job = QuotientJob {
            k,
            ext_k,
            extended_omega: w,
            zeta: [z, z.square()],
            advice: a.iter().map(Vec::as_slice).collect(),
            instance: i.iter().map(Vec::as_slice).collect(),
            fixed: fixed.iter().map(|p| Some(&p[..])).collect(),
            l0: &zero,
            l_last: &zero,
            l_active: &zero,
            y,
            beta: Fq::ZERO,
            gamma: Fq::ZERO,
            delta_start: Fq::ZERO,
            delta: Fq::ZERO,
            gates: gates.clone(),
            permutation: None,
            lookups: vec![],
            trash: vec![],
            divide: QuotientDivide {
                t_inv: t_inv.clone(),
                omega_inv: w.invert().unwrap(),
                divisor: Fq::from(n_ext as u64).invert().unwrap(),
                zeta_out: [z.square(), z],
                len: n_ext as usize,
            },
        };
        let mut h = hook(&job, reason(case)).unwrap_or_else(|| {
            let extend = |cols: Vec<Vec<Fq>>| -> Vec<_> {
                cols.into_iter()
                    .map(|mut c| {
                        scale_powers(&mut c, z * Fq::ZETA.invert().unwrap());
                        fd.coeff_to_extended(d.coeff_from_vec(c))
                    })
                    .collect()
            };
            without_hooks(|| {
                let (nu, _) = evaluate(&extend(a), &extend(i));
                inverse_coset(divide(&nu))
            })
        });
        // The ABI returns coefficients. Reverse its invertible division and
        // coset interpolation, retaining the full N coefficients for this test.
        scale_powers(&mut h, z);
        best_fft(&mut h, w, ext_k);
        for row in (residue..h.len()).step_by(ratio) {
            assert_eq!(
                h[row],
                expected[row] * t_inv[row % ratio],
                "quotient at row {row}"
            );
            divided[row] = h[row];
        }
    }
    if let Some(coeffs) = case.get("quotient_coeffs") {
        equal(
            &inverse_coset(divided),
            &fields(coeffs),
            "reconstructed hook quotient coefficients",
        );
    }
    true
}
