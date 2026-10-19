//! Prover-side traces in Lagrange form: linear combinations of traces (the
//! witness side of folding) and the `y⃗`-combined identities `fᵢ` on every row
//! `i` of the domain `H`.

use std::borrow::Cow;

use ff::{PrimeField, WithSmallOrderMulGroup};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::{
    instance::{combine_scalars, combine_vectors},
    sparse_gates::SparseGates,
};
use crate::{
    plonk::{ProvingKey, argument::prover::Committed, traces::ProverTrace},
    poly::{LagrangeCoeff, Polynomial, commitment::PolynomialCommitmentScheme},
};

/// Entry-wise `Σⱼ wⱼ·listsⱼ` of equally long lists of polynomials.
fn combine_polys<F: PrimeField, B: Send + Sync>(
    lists: &[&[Polynomial<F, B>]],
    weights: &[F],
) -> Vec<Polynomial<F, B>> {
    assert_eq!(weights.len(), lists.len());
    assert!(!lists.is_empty());
    let len = lists[0].len();
    assert!(lists.iter().all(|list| list.len() == len));
    (0..len)
        .into_par_iter()
        .map(|i| {
            let polys: Vec<_> = lists.iter().map(|list| &list[i]).collect();
            Polynomial::linear_combination(&polys, weights)
        })
        .collect()
}

/// The trace `Σⱼ weightsⱼ·tracesⱼ`: instance and witness polynomials and
/// every challenge, all combined with the same weights. The fixed (phase-0)
/// group is shared, not combined: every trace must hold the same one.
///
/// # Panics
///
/// Panics if `traces` is empty or not as long as `weights`, if the traces do
/// not share their phase-0 group, or if they differ in shape.
pub(crate) fn linear_combination<'a, F: PrimeField>(
    traces: &[&ProverTrace<'a, F, LagrangeCoeff>],
    weights: &[F],
) -> ProverTrace<'a, F, LagrangeCoeff> {
    assert_eq!(weights.len(), traces.len());
    let first = traces.first().expect("no trace to combine");
    assert!(
        traces.iter().all(|t| std::ptr::eq(t.phase0_committed, first.phase0_committed)),
        "combining traces of different phase-0 groups"
    );
    let vector = |field: for<'t> fn(&'t ProverTrace<'a, F, LagrangeCoeff>) -> &'t [F]| {
        let vectors: Vec<&[F]> = traces.iter().map(|t| field(t)).collect();
        combine_vectors(weights, &vectors)
    };
    let scalar = |field: fn(&ProverTrace<'a, F, LagrangeCoeff>) -> F| {
        let values: Vec<F> = traces.iter().map(|t| field(t)).collect();
        combine_scalars(weights, &values)
    };
    let instance_polys: Vec<&[_]> = traces.iter().map(|t| &t.instance_polys[..]).collect();
    let instance_values: Vec<&[_]> = traces.iter().map(|t| &t.instance_values[..]).collect();
    let phase1: Vec<_> = traces.iter().map(|t| &t.phase1_committed).collect();
    let phase2: Vec<_> = traces.iter().map(|t| &t.phase2_committed).collect();
    ProverTrace {
        instance_polys: combine_polys(&instance_polys, weights),
        instance_values: combine_polys(&instance_values, weights),
        phase0_committed: first.phase0_committed,
        phase1_committed: Committed::linear_combination(&phase1, weights),
        phase2_committed: Committed::linear_combination(&phase2, weights),
        beta: scalar(|t| t.beta),
        gamma: scalar(|t| t.gamma),
        theta: vector(|t| &t.theta),
        trash_challenges: vector(|t| &t.trash_challenges),
        y: vector(|t| &t.y),
    }
}

/// `l₀`, `l_last` (first blinding row minus one) and `l_active_row` on `H`,
/// in Lagrange form: the selector polynomials the evaluator expects.
fn lagrange_selectors<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
) -> [Polynomial<F, LagrangeCoeff>; 3] {
    let domain = &pk.vk.domain;
    let last = domain.n as usize - pk.vk.cs.blinding_factors() - 1;
    let mut l0 = domain.empty_lagrange();
    l0[0] = F::ONE;
    let mut l_last = domain.empty_lagrange();
    l_last[last] = F::ONE;
    let mut l_active_row = domain.empty_lagrange();
    for value in l_active_row.iter_mut().take(last) {
        *value = F::ONE;
    }
    [l0, l_last, l_active_row]
}

/// `fᵢ = Σ_m y_m·id_m(row i)` for every row `i` of `H`, with the trace's own
/// (possibly combined) challenges, public inputs and witness. Lagrange form
/// throughout: no FFT. The custom gates are evaluated only on the rows where
/// they are active.
pub(crate) fn evaluate_rows<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<'_, F, LagrangeCoeff>,
) -> Polynomial<F, LagrangeCoeff> {
    let sparse = pk
        .ev
        .sparse_gates
        .get_or_init(|| SparseGates::new(&pk.vk.cs, &pk.vk.domain, &pk.fixed_values));
    let values = sparse.evaluate(
        &pk.vk.domain,
        trace.phase1_committed.polys_of(&pk.vk.cs.advice_labels()),
        &trace.instance_values,
        &pk.fixed_values,
        &trace.y,
    );
    add_non_gate_rows(pk, trace, values)
}

/// [`evaluate_rows`] with every gate evaluated on every row (the evaluator
/// of the plain prover); reference for [`evaluate_rows`].
#[cfg(test)]
pub(crate) fn evaluate_rows_dense<
    F: WithSmallOrderMulGroup<3>,
    CS: PolynomialCommitmentScheme<F>,
>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<'_, F, LagrangeCoeff>,
) -> Polynomial<F, LagrangeCoeff> {
    let values = pk.ev.evaluate_custom_gates::<LagrangeCoeff>(
        &pk.vk.domain,
        &pk.vk.cs,
        trace.phase1_committed.polys_of(&pk.vk.cs.advice_labels()),
        &trace.instance_values,
        &pk.fixed_values,
        &trace.y,
        trace.beta,
        &trace.theta,
        &trace.trash_challenges,
    );
    add_non_gate_rows(pk, trace, values)
}

/// Adds the permutation, lookup and trash identities to the custom-gate
/// `values`.
fn add_non_gate_rows<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>>(
    pk: &ProvingKey<F, CS>,
    trace: &ProverTrace<'_, F, LagrangeCoeff>,
    mut values: Polynomial<F, LagrangeCoeff>,
) -> Polynomial<F, LagrangeCoeff> {
    let [l0, l_last, l_active_row] = lagrange_selectors(pk);
    pk.ev.add_non_gate_identities::<LagrangeCoeff, LagrangeCoeff>(
        &mut values,
        &pk.vk.domain,
        &pk.vk.cs,
        trace.phase1_committed.polys_of(&pk.vk.cs.advice_labels()),
        &trace.instance_values,
        &pk.fixed_values,
        &trace.y,
        trace.beta,
        trace.gamma,
        &trace.theta,
        &trace.trash_challenges,
        &trace.phase1_committed,
        &trace.phase2_committed,
        Cow::Borrowed,
        &l0,
        &l_last,
        &l_active_row,
        &pk.sigmas.values,
    );
    values
}

#[cfg(test)]
mod tests {
    use blake2b_simd::State;
    use ff::Field;
    use midnight_curves::{Bls12, Fq};
    use rand_core::OsRng;

    use super::*;
    use crate::{
        plonk::{
            keygen_pk, keygen_vk_with_k,
            protogalaxy::folding_degree,
            prover::commit_phases,
            test_circuit::{K, SquareCircuit},
        },
        poly::kzg::{KZGCommitmentScheme, params::ParamsKZG},
        transcript::{CircuitTranscript, Transcript},
    };

    type CS = KZGCommitmentScheme<Bls12>;
    type Pk = ProvingKey<Fq, CS>;
    type Trace<'a> = ProverTrace<'a, Fq, LagrangeCoeff>;

    fn setup() -> (ParamsKZG<Bls12>, Pk) {
        let params = CS::gen_params(K);
        let vk = keygen_vk_with_k::<_, CS, _>(&params, &SquareCircuit::default(), K).unwrap();
        let pk = keygen_pk(vk, &SquareCircuit::default()).unwrap();
        (params, pk)
    }

    /// The commit phases of `circuit`, with its own public input.
    fn trace_of<'a>(params: &ParamsKZG<Bls12>, pk: &'a Pk, circuit: SquareCircuit) -> Trace<'a> {
        let instance = [circuit.public_input()];
        let (trace, _) = commit_phases(
            params,
            pk,
            &circuit,
            #[cfg(feature = "committed-instances")]
            0,
            &[&instance],
            &mut CircuitTranscript::<State>::init(),
            OsRng,
        )
        .unwrap();
        trace
    }

    /// Every polynomial of the trace, as plain values, in a fixed order.
    fn polys(trace: &Trace<'_>) -> Vec<Vec<Fq>> {
        let groups = [&trace.phase1_committed, &trace.phase2_committed];
        (trace.instance_polys.iter().map(|p| p.to_vec()))
            .chain(trace.instance_values.iter().map(|p| p.to_vec()))
            .chain(
                groups
                    .into_iter()
                    .flat_map(|g| g.par_polys().map(|(_, p)| p.to_vec()).collect::<Vec<_>>()),
            )
            .collect()
    }

    /// Every challenge of the trace, in a fixed order.
    fn challenges(trace: &Trace<'_>) -> Vec<Fq> {
        (trace.theta.iter())
            .chain([&trace.beta, &trace.gamma])
            .chain(&trace.trash_challenges)
            .chain(&trace.y)
            .copied()
            .collect()
    }

    fn assert_same(a: &Trace<'_>, b: &Trace<'_>) {
        assert_eq!(polys(a), polys(b));
        assert_eq!(challenges(a), challenges(b));
    }

    #[test]
    fn evaluate_rows_is_zero_on_honest_traces() {
        let (params, pk) = setup();
        for start in [0, 3] {
            let trace = trace_of(
                &params,
                &pk,
                SquareCircuit {
                    start,
                    corrupt: false,
                },
            );
            let rows = evaluate_rows(&pk, &trace);
            assert_eq!(rows.len(), 1 << K);
            assert!(rows.iter().all(|v| bool::from(v.is_zero())));
        }
    }

    #[test]
    fn evaluate_rows_detects_a_corrupted_trace() {
        let (params, pk) = setup();
        let trace = trace_of(
            &params,
            &pk,
            SquareCircuit {
                start: 0,
                corrupt: true,
            },
        );
        let rows = evaluate_rows(&pk, &trace);
        assert!(rows.iter().any(|v| !bool::from(v.is_zero())));
    }

    #[test]
    fn linear_combination_with_unit_weights_selects_a_trace() {
        let (params, pk) = setup();
        let a = trace_of(
            &params,
            &pk,
            SquareCircuit {
                start: 0,
                corrupt: false,
            },
        );
        let b = trace_of(
            &params,
            &pk,
            SquareCircuit {
                start: 3,
                corrupt: false,
            },
        );
        assert_ne!(polys(&a), polys(&b));
        assert_ne!(challenges(&a), challenges(&b));

        let (zero, one) = (Fq::ZERO, Fq::ONE);
        assert_same(&linear_combination(&[&a, &b], &[one, zero]), &a);
        assert_same(&linear_combination(&[&a, &b], &[zero, one]), &b);
    }

    #[test]
    fn linear_combination_interpolates_between_two_traces() {
        let (params, pk) = setup();
        let a = trace_of(
            &params,
            &pk,
            SquareCircuit {
                start: 0,
                corrupt: false,
            },
        );
        let b = trace_of(
            &params,
            &pk,
            SquareCircuit {
                start: 3,
                corrupt: false,
            },
        );
        let x = Fq::random(OsRng);
        let c = linear_combination(&[&a, &b], &[Fq::ONE - x, x]);

        let at = |t: &Trace<'_>| (polys(t), challenges(t));
        let ((pa, ca), (pb, cb), (pc, cc)) = (at(&a), at(&b), at(&c));
        let fold = |a: &[Fq], b: &[Fq]| -> Vec<Fq> {
            a.iter().zip(b).map(|(a, b)| *a + x * (*b - *a)).collect()
        };
        assert_eq!(cc, fold(&ca, &cb));
        assert_eq!(pc.len(), pa.len());
        for ((pa, pb), pc) in pa.iter().zip(&pb).zip(&pc) {
            assert_eq!(*pc, fold(pa, pb));
        }
    }

    #[test]
    fn folding_degree_is_at_least_the_circuit_degree() {
        let (_, pk) = setup();
        let cs = &pk.vk.cs;
        assert!(folding_degree(cs) >= cs.degree());
    }
}
