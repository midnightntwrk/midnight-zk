use std::{borrow::Cow, sync::OnceLock};

use ff::{PrimeField, WithSmallOrderMulGroup};
use group::ff::Field;
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use super::{ConstraintSystem, Expression, protogalaxy::sparse_gates::SparseGates};
use crate::{
    plonk::{Any, argument},
    poly::{EvaluationDomain, Polynomial, PolynomialLabel, PolynomialRepresentation, Rotation},
    utils::arithmetic::parallelize,
};

#[inline]
pub(crate) fn get_rotation_idx(idx: usize, rot: i32, log_scale: u32, log_n: u32) -> usize {
    let mask = (1usize << log_n) - 1;
    idx.wrapping_add(((rot as isize) << log_scale) as usize) & mask
}

/// Value used in a calculation
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd)]
pub enum ValueSource {
    /// This is a constant value
    Constant(usize),
    /// This is an intermediate value
    Intermediate(usize),
    /// This is a fixed column
    Fixed(usize, usize),
    /// This is an advice (witness) column
    Advice(usize, usize),
    /// This is an instance (external) column
    Instance(usize, usize),
    /// beta
    Beta(),
    /// theta\[i\]
    Theta(usize),
    /// trash_powers\[i\] (`c^i` for a fresh instance)
    TrashPow(usize),
    /// y\[i\]
    Y(usize),
    /// Previous value
    PreviousValue(),
}

impl Default for ValueSource {
    fn default() -> Self {
        ValueSource::Constant(0)
    }
}

/// Calculation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Calculation {
    /// This is an addition
    Add(ValueSource, ValueSource),
    /// This is a subtraction
    Sub(ValueSource, ValueSource),
    /// This is a product
    Mul(ValueSource, ValueSource),
    /// This is a square
    Square(ValueSource),
    /// This is a double
    Double(ValueSource),
    /// This is a negation
    Negate(ValueSource),
    /// This is a linear combination: `val = a + Σᵢ cᵢ * bᵢ` over `(cᵢ, bᵢ)`
    LinearCombination(ValueSource, Vec<(ValueSource, ValueSource)>),
    /// This is a simple assignment
    Store(ValueSource),
}

impl Calculation {
    /// Every value source this calculation reads.
    fn sources(&self) -> Vec<&ValueSource> {
        match self {
            Calculation::Add(a, b) | Calculation::Sub(a, b) | Calculation::Mul(a, b) => vec![a, b],
            Calculation::Square(a)
            | Calculation::Double(a)
            | Calculation::Negate(a)
            | Calculation::Store(a) => vec![a],
            Calculation::LinearCombination(s, terms) => {
                std::iter::once(s).chain(terms.iter().flat_map(|(c, t)| [c, t])).collect()
            }
        }
    }
}

/// Wraps a `GraphEvaluator` for lookups with named handles to the evaluator
/// outputs.
#[derive(Clone, Debug)]
pub struct LookupGraphEvaluator<F: PrimeField> {
    /// The underlying computation graph
    pub graph: GraphEvaluator<F>,
    /// Value containing the sum of partial products, Σⱼ ∏_{k≠j}(fₖ + β)
    pub sum_partial_products: ValueSource,
    /// Value containing the product, ∏ⱼ(fⱼ + β)
    pub product: ValueSource,
    /// Value containing the compressed table value (t + β)
    pub table: ValueSource,
    /// Selector of the lookup argument
    pub selector: ValueSource,
}

/// Evaluator
#[derive(Clone, Debug)]
pub struct Evaluator<F: PrimeField> {
    ///  Custom gates evaluation
    pub custom_gates: GraphEvaluator<F>,
    /// Flattened custom gates for fast evaluation.
    pub custom_gates_flat: FlatGraphEvaluator<F>,
    ///  Lookups evaluation (one Vec per BatchedArgument, one entry per
    /// flattened arg)
    pub lookups: Vec<Vec<LookupGraphEvaluator<F>>>,
    /// Flattened lookup evaluators (parallel to `lookups`).
    pub lookups_flat: Vec<Vec<FlatGraphEvaluator<F>>>,
    ///  Trashcans evaluation
    pub trashcans: Vec<GraphEvaluator<F>>,
    /// Flattened trash evaluators (parallel to `trashcans`).
    pub trashcans_flat: Vec<FlatGraphEvaluator<F>>,
    /// Row-sparse custom-gate evaluator of the folding prover, built on first
    /// use (a clone starts with an empty cell).
    pub(crate) sparse_gates: OnceLock<SparseGates<F>>,
}

/// GraphEvaluator
#[derive(Clone, Debug)]
pub struct GraphEvaluator<F: PrimeField> {
    /// Constants
    pub constants: Vec<F>,
    /// Rotations
    pub rotations: Vec<i32>,
    /// Calculations
    pub calculations: Vec<CalculationInfo>,
    /// Number of intermediates
    pub num_intermediates: usize,
}

/// CalculationInfo
#[derive(Clone, Debug)]
pub struct CalculationInfo {
    /// Calculation
    pub calculation: Calculation,
    /// Target
    pub target: usize,
}

// ---------------------------------------------------------------------------
// Flattened graph evaluator — pre-resolves all ValueSource lookups into
// unified buffer indices for a tighter evaluation loop.
// ---------------------------------------------------------------------------

/// Operation kind for the flattened evaluator.
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum FlatOpKind {
    Add,
    Sub,
    Mul,
    Square,
    Double,
    Negate,
    /// Fused multiply-add: `dst = a * b + c`. Used for linear
    /// combinations.
    MulAdd,
}

/// A single flattened operation. All operands are indices into the unified
/// values buffer — no enum dispatch needed at evaluation time.
#[derive(Clone, Copy, Debug)]
pub struct FlatOp {
    pub kind: FlatOpKind,
    pub dst: u32,
    /// Source operands (indices into the values buffer).
    /// - Binary ops use `a` and `b`.
    /// - Unary ops use `a` only.
    /// - MulAdd uses `a`, `b`, and `c`.
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

/// Number of scalar named slots in the values buffer
/// (beta, previous_value). The `trash`, `theta` and `y` slots follow.
const NUM_SCALAR_SLOTS: usize = 2;

/// Tag values for [`ColumnRead::col_type`].
const COL_TYPE_FIXED: u8 = 0;
const COL_TYPE_ADVICE: u8 = 1;
const COL_TYPE_INSTANCE: u8 = 2;

/// Column read: load a value from a polynomial column at a rotated index.
#[derive(Clone, Copy, Debug)]
pub struct ColumnRead {
    /// One of [`COL_TYPE_FIXED`], [`COL_TYPE_ADVICE`], [`COL_TYPE_INSTANCE`].
    pub col_type: u8,
    /// Column index within its type.
    pub col_idx: u16,
    /// Index into the rotations array (for Fixed/Advice/Instance).
    /// For Challenge: the challenge index.
    pub rot_idx: u8,
    /// Destination index in the values buffer.
    pub dst: u32,
}

/// Pre-flattened graph for fast evaluation. Built from a [`GraphEvaluator`]
/// at keygen time via [`GraphEvaluator::flatten`].
///
/// The values buffer layout (with `S = NUM_SCALAR_SLOTS + n_trash + n_theta + n_y`):
/// ```text
/// [0 .. C)                   constants (static)
/// [C .. C+S)                 beta, previous_value,
///                            trash[0..n_trash], theta[0..n_theta], y[0..n_y]
/// [C+S .. C+S+R)             column read results (loaded per element)
/// [C+S+R .. C+S+R+I)         intermediates (computed per element)
/// ```
/// `n_trash` (resp. `n_theta`, `n_y`) is one more than the largest `TrashPow(i)`
/// (resp. `Theta(i)`, `Y(i)`) the graph reads.
#[derive(Clone, Debug)]
pub struct FlatGraphEvaluator<F> {
    /// Pre-loaded constants (copied into values buffer once per prove).
    pub constants: Vec<F>,
    /// Rotation values (same as GraphEvaluator::rotations).
    pub rotations: Vec<i32>,
    /// Column reads to perform at the start of each element.
    pub column_reads: Vec<ColumnRead>,
    /// Flattened operations.
    pub ops: Vec<FlatOp>,
    /// Total values buffer length.
    pub values_len: usize,
    /// Index offsets for named slots.
    pub beta_idx: u32,
    pub previous_value_idx: u32,
    /// Index of `trash[0]`, followed by the other `n_trash - 1` slots.
    pub trash_idx: u32,
    pub n_trash: usize,
    /// Index of `theta[0]`, followed by the other `n_theta - 1` slots.
    pub theta_idx: u32,
    pub n_theta: usize,
    /// Index of `y[0]`, followed by the other `n_y - 1` slots.
    pub y_idx: u32,
    pub n_y: usize,
    /// Index of the first intermediate.
    pub intermediates_offset: usize,
    /// Index of the final result.
    pub result_idx: u32,
}

impl<F: PrimeField> GraphEvaluator<F> {
    /// Convert this graph into a flattened evaluator for faster evaluation.
    pub fn flatten(&self) -> FlatGraphEvaluator<F> {
        let challenge_offset = self.constants.len();
        let beta_idx = challenge_offset as u32;
        let previous_value_idx = (challenge_offset + 1) as u32;

        // Number of `trash`/`theta`/`y` slots: one past the largest index read.
        let (mut n_trash, mut n_theta, mut n_y) = (0, 0, 0);
        for calc_info in &self.calculations {
            for vs in calc_info.calculation.sources() {
                match *vs {
                    ValueSource::TrashPow(i) => n_trash = n_trash.max(i + 1),
                    ValueSource::Theta(i) => n_theta = n_theta.max(i + 1),
                    ValueSource::Y(i) => n_y = n_y.max(i + 1),
                    _ => (),
                }
            }
        }
        let trash_idx = (challenge_offset + NUM_SCALAR_SLOTS) as u32;
        let theta_idx = trash_idx + n_trash as u32;
        let y_idx = theta_idx + n_theta as u32;

        let column_read_offset = challenge_offset + NUM_SCALAR_SLOTS + n_trash + n_theta + n_y;

        // First pass: collect column reads and assign their buffer indices.
        let mut column_reads = Vec::new();
        let mut column_read_map: Vec<(ValueSource, u32)> = Vec::new();

        /// Walk a single [`Calculation`] and collect every column-style
        /// [`ValueSource`] it reads (Fixed, Advice, Instance, Challenge) into
        /// the shared dedup map and descriptor list.
        ///
        /// For each such source seen for the first time, a [`ColumnRead`]
        /// descriptor is appended to `column_reads` and the `(source, dst)`
        /// pair is recorded in `reads`, where `dst` is the source's slot in
        /// the unified values buffer (`base_offset + reads.len()` at the time
        /// of insertion). Subsequent occurrences of the same source are
        /// deduplicated so each distinct column access maps to a single slot.
        ///
        /// `reads` and `column_reads` are threaded across all calculations of
        /// the graph so indices stay consistent after flattening. Non-column
        /// sources (constants, intermediates, challenges-like globals such as
        /// beta/theta/y) are ignored here — those are resolved later by
        /// `resolve`.
        fn find_column_reads(
            calc: &Calculation,
            reads: &mut Vec<(ValueSource, u32)>,
            column_reads: &mut Vec<ColumnRead>,
            base_offset: usize,
        ) {
            let check = |vs: &ValueSource| {
                if matches!(
                    vs,
                    ValueSource::Fixed(..) | ValueSource::Advice(..) | ValueSource::Instance(..)
                ) && !reads.iter().any(|(v, _)| *v == *vs)
                {
                    let dst = (base_offset + reads.len()) as u32;
                    let cr = match *vs {
                        ValueSource::Fixed(c, r) => ColumnRead {
                            col_type: COL_TYPE_FIXED,
                            col_idx: c as u16,
                            rot_idx: r as u8,
                            dst,
                        },
                        ValueSource::Advice(c, r) => ColumnRead {
                            col_type: COL_TYPE_ADVICE,
                            col_idx: c as u16,
                            rot_idx: r as u8,
                            dst,
                        },
                        ValueSource::Instance(c, r) => ColumnRead {
                            col_type: COL_TYPE_INSTANCE,
                            col_idx: c as u16,
                            rot_idx: r as u8,
                            dst,
                        },
                        _ => unreachable!(),
                    };
                    column_reads.push(cr);
                    reads.push((*vs, dst));
                }
            };

            calc.sources().into_iter().for_each(check);
        }

        for calc_info in &self.calculations {
            find_column_reads(
                &calc_info.calculation,
                &mut column_read_map,
                &mut column_reads,
                column_read_offset,
            );
        }

        let num_column_reads = column_reads.len();
        let intermediates_offset = column_read_offset + num_column_reads;

        // Resolve a ValueSource to a values-buffer index.
        let resolve = |vs: &ValueSource| -> u32 {
            match *vs {
                ValueSource::Constant(idx) => idx as u32,
                ValueSource::Intermediate(idx) => (intermediates_offset + idx) as u32,
                ValueSource::Beta() => beta_idx,
                ValueSource::Theta(i) => theta_idx + i as u32,
                ValueSource::TrashPow(i) => trash_idx + i as u32,
                ValueSource::Y(i) => y_idx + i as u32,
                ValueSource::PreviousValue() => previous_value_idx,
                ValueSource::Fixed(..) | ValueSource::Advice(..) | ValueSource::Instance(..) => {
                    column_read_map.iter().find(|(v, _)| *v == *vs).unwrap().1
                }
            }
        };

        // Second pass: flatten calculations into FlatOps.
        let mut ops = Vec::with_capacity(self.calculations.len() * 2);

        for calc_info in &self.calculations {
            let dst = (intermediates_offset + calc_info.target) as u32;
            match &calc_info.calculation {
                Calculation::Add(a, b) => ops.push(FlatOp {
                    kind: FlatOpKind::Add,
                    dst,
                    a: resolve(a),
                    b: resolve(b),
                    c: 0,
                }),
                Calculation::Sub(a, b) => ops.push(FlatOp {
                    kind: FlatOpKind::Sub,
                    dst,
                    a: resolve(a),
                    b: resolve(b),
                    c: 0,
                }),
                Calculation::Mul(a, b) => ops.push(FlatOp {
                    kind: FlatOpKind::Mul,
                    dst,
                    a: resolve(a),
                    b: resolve(b),
                    c: 0,
                }),
                Calculation::Square(v) => ops.push(FlatOp {
                    kind: FlatOpKind::Square,
                    dst,
                    a: resolve(v),
                    b: 0,
                    c: 0,
                }),
                Calculation::Double(v) => ops.push(FlatOp {
                    kind: FlatOpKind::Double,
                    dst,
                    a: resolve(v),
                    b: 0,
                    c: 0,
                }),
                Calculation::Negate(v) => ops.push(FlatOp {
                    kind: FlatOpKind::Negate,
                    dst,
                    a: resolve(v),
                    b: 0,
                    c: 0,
                }),
                Calculation::Store(v) => {
                    // Store is a copy from a column/constant/etc into an intermediate.
                    // In the flattened format, the column read is pre-loaded, so this
                    // is just a copy: dst = src.
                    let src = resolve(v);
                    // Optimization: if dst == src, skip the copy. Otherwise emit Add with 0.
                    // NOTE: This is relying in the first constant being  0, should be reviewed.
                    if dst != src {
                        ops.push(FlatOp {
                            kind: FlatOpKind::Add,
                            dst,
                            a: src,
                            b: 0, // Constant(0) = F::ZERO, add identity.
                            c: 0,
                        });
                    }
                }
                Calculation::LinearCombination(start, terms) => {
                    let start_idx = resolve(start);
                    // First: dst = start_value.
                    if dst != start_idx {
                        ops.push(FlatOp {
                            kind: FlatOpKind::Add,
                            dst,
                            a: start_idx,
                            b: 0,
                            c: 0,
                        });
                    }
                    // Then: dst = coeff[i] * term[i] + dst.
                    for (coeff, term) in terms {
                        ops.push(FlatOp {
                            kind: FlatOpKind::MulAdd,
                            dst,
                            a: resolve(coeff),
                            b: resolve(term),
                            c: dst,
                        });
                    }
                }
            }
        }

        let values_len = intermediates_offset + self.num_intermediates;
        let result_idx = ops.last().map_or(0, |op| op.dst);

        FlatGraphEvaluator {
            constants: self.constants.clone(),
            rotations: self.rotations.clone(),
            column_reads,
            ops,
            values_len,
            beta_idx,
            previous_value_idx,
            trash_idx,
            n_trash,
            theta_idx,
            n_theta,
            y_idx,
            n_y,
            intermediates_offset,
            result_idx,
        }
    }
}

impl<F: PrimeField> FlatGraphEvaluator<F> {
    /// Resolve a `ValueSource::Intermediate` handle to a flat buffer index.
    /// Used to read specific outputs (e.g., lookup's sum_partial_products)
    /// from the values buffer after evaluation.
    pub fn resolve_idx(&self, vs: ValueSource) -> usize {
        match vs {
            ValueSource::Intermediate(idx) => self.intermediates_offset + idx,
            _ => panic!("resolve_idx only supports Intermediate, got {vs:?}"),
        }
    }

    /// Create a fresh values buffer, pre-filled with constants and challenges.
    /// Only the first `n_trash` (resp. `n_theta`, `n_y`) elements of `trash_powers`
    /// (resp. `theta`, `y`)
    /// are read by the graph.
    pub fn new_values_buffer(&self, beta: &F, theta: &[F], trash_powers: &[F], y: &[F]) -> Vec<F> {
        let mut values = vec![F::ZERO; self.values_len];
        values[..self.constants.len()].copy_from_slice(&self.constants);
        values[self.beta_idx as usize] = *beta;
        let trash_idx = self.trash_idx as usize;
        values[trash_idx..trash_idx + self.n_trash].copy_from_slice(&trash_powers[..self.n_trash]);
        let theta_idx = self.theta_idx as usize;
        values[theta_idx..theta_idx + self.n_theta].copy_from_slice(&theta[..self.n_theta]);
        let y_idx = self.y_idx as usize;
        values[y_idx..y_idx + self.n_y].copy_from_slice(&y[..self.n_y]);
        values
    }

    /// Evaluate the graph at one domain element. The `values` buffer is reused
    /// across elements (only column reads and intermediates are overwritten).
    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<B: PolynomialRepresentation>(
        &self,
        values: &mut [F],
        fixed: &[Polynomial<F, B>],
        advice: &[Polynomial<F, B>],
        instance: &[Polynomial<F, B>],
        rotations: &[usize],
        previous_value: &F,
    ) -> F {
        values[self.previous_value_idx as usize] = *previous_value;

        // Step 1: Load column values into the buffer.
        for cr in &self.column_reads {
            values[cr.dst as usize] = match cr.col_type {
                COL_TYPE_FIXED => fixed[cr.col_idx as usize][rotations[cr.rot_idx as usize]],
                COL_TYPE_ADVICE => advice[cr.col_idx as usize][rotations[cr.rot_idx as usize]],
                COL_TYPE_INSTANCE => instance[cr.col_idx as usize][rotations[cr.rot_idx as usize]],
                _ => unreachable!(),
            };
        }

        // Step 2: Evaluate flattened operations.
        for op in &self.ops {
            let d = op.dst as usize;
            values[d] = match op.kind {
                FlatOpKind::Add => values[op.a as usize] + values[op.b as usize],
                FlatOpKind::Sub => values[op.a as usize] - values[op.b as usize],
                FlatOpKind::Mul => values[op.a as usize] * values[op.b as usize],
                FlatOpKind::Square => values[op.a as usize].square(),
                FlatOpKind::Double => values[op.a as usize].double(),
                FlatOpKind::Negate => -values[op.a as usize],
                FlatOpKind::MulAdd => {
                    values[op.a as usize] * values[op.b as usize] + values[op.c as usize]
                }
            };
        }

        values[self.result_idx as usize]
    }
}

impl<F: PrimeField> FlatGraphEvaluator<F> {
    /// Evaluate the graph over a chunk of domain elements with compile-time
    /// batch size `BATCH`. Processes BATCH elements per graph traversal,
    /// amortizing op dispatch. LLVM fully unrolls the inner `for b in 0..BATCH`
    /// loops into straight-line code.
    ///
    /// `template_buf` is a pre-filled values buffer (constants + challenges).
    /// `output[i]` is both input (previous_value) and output (result).
    #[allow(clippy::too_many_arguments)]
    // The `for b in 0..BATCH` loops below index BATCH parallel buffers; rewriting
    // them as iterators would obscure the const-generic unroll. `b` is the index.
    #[allow(clippy::needless_range_loop)]
    pub fn evaluate_chunk<const BATCH: usize, Repr: PolynomialRepresentation>(
        &self,
        template_buf: &[F],
        output: &mut [F],
        start: usize,
        fixed: &[Polynomial<F, Repr>],
        advice: &[Polynomial<F, Repr>],
        instance: &[Polynomial<F, Repr>],
        log_scale: u32,
        log_n: u32,
    ) {
        let chunk_len = output.len();
        let pv_i = self.previous_value_idx as usize;
        let result_i = self.result_idx as usize;
        let mask = (1usize << log_n) - 1;
        let num_rots = self.rotations.len();

        // Pre-compute rotation strides for incremental index calculation.
        let rot_strides: Vec<usize> = self
            .rotations
            .iter()
            .map(|&rot| ((rot as isize) << log_scale) as usize)
            .collect();

        // BATCH values buffers, reused across batches.
        let mut bufs: [Vec<F>; BATCH] = std::array::from_fn(|_| template_buf.to_vec());
        let mut all_rots: [Vec<usize>; BATCH] = std::array::from_fn(|_| vec![0usize; num_rots]);

        let mut pos = 0;

        // Main loop: full batches of BATCH elements.
        while pos + BATCH <= chunk_len {
            // Load column values for BATCH elements.
            for b in 0..BATCH {
                let idx = start + pos + b;
                for (ri, stride) in rot_strides.iter().enumerate() {
                    all_rots[b][ri] = idx.wrapping_add(*stride) & mask;
                }
                bufs[b][pv_i] = output[pos + b];
                for cr in &self.column_reads {
                    let rot = all_rots[b][cr.rot_idx as usize];
                    bufs[b][cr.dst as usize] = match cr.col_type {
                        COL_TYPE_FIXED => fixed[cr.col_idx as usize][rot],
                        COL_TYPE_ADVICE => advice[cr.col_idx as usize][rot],
                        COL_TYPE_INSTANCE => instance[cr.col_idx as usize][rot],
                        _ => unreachable!(),
                    };
                }
            }

            // Execute ops — one dispatch, BATCH unrolled field operations.
            for op in &self.ops {
                let d = op.dst as usize;
                let a = op.a as usize;
                let bi = op.b as usize;
                let c = op.c as usize;
                match op.kind {
                    FlatOpKind::Add => {
                        for b in 0..BATCH {
                            bufs[b][d] = bufs[b][a] + bufs[b][bi];
                        }
                    }
                    FlatOpKind::Sub => {
                        for b in 0..BATCH {
                            bufs[b][d] = bufs[b][a] - bufs[b][bi];
                        }
                    }
                    FlatOpKind::Mul => {
                        for b in 0..BATCH {
                            bufs[b][d] = bufs[b][a] * bufs[b][bi];
                        }
                    }
                    FlatOpKind::Square => {
                        for b in 0..BATCH {
                            bufs[b][d] = bufs[b][a].square();
                        }
                    }
                    FlatOpKind::Double => {
                        for b in 0..BATCH {
                            bufs[b][d] = bufs[b][a].double();
                        }
                    }
                    FlatOpKind::Negate => {
                        for b in 0..BATCH {
                            bufs[b][d] = -bufs[b][a];
                        }
                    }
                    FlatOpKind::MulAdd => {
                        for b in 0..BATCH {
                            bufs[b][d] = bufs[b][a] * bufs[b][bi] + bufs[b][c];
                        }
                    }
                }
            }

            for b in 0..BATCH {
                output[pos + b] = bufs[b][result_i];
            }
            pos += BATCH;
        }

        // Tail: remaining elements (< BATCH), processed one at a time.
        if pos < chunk_len {
            let mut buf = bufs.into_iter().next().unwrap();
            let mut rot_indices = all_rots.into_iter().next().unwrap();
            while pos < chunk_len {
                let idx = start + pos;
                for (ri, stride) in rot_strides.iter().enumerate() {
                    rot_indices[ri] = idx.wrapping_add(*stride) & mask;
                }
                output[pos] = self.evaluate::<Repr>(
                    &mut buf,
                    fixed,
                    advice,
                    instance,
                    &rot_indices,
                    &output[pos],
                );
                pos += 1;
            }
        }
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluator<F> {
    /// Creates a new evaluation structure
    pub fn new(cs: &ConstraintSystem<F>) -> Self {
        let dummy_flat = FlatGraphEvaluator {
            constants: Vec::new(),
            rotations: Vec::new(),
            column_reads: Vec::new(),
            ops: Vec::new(),
            values_len: 0,
            beta_idx: 0,
            previous_value_idx: 0,
            trash_idx: 0,
            n_trash: 0,
            theta_idx: 0,
            n_theta: 0,
            y_idx: 0,
            n_y: 0,
            intermediates_offset: 0,
            result_idx: 0,
        };
        let mut ev = Evaluator {
            custom_gates: GraphEvaluator::default(),
            custom_gates_flat: dummy_flat,
            lookups: Vec::new(),
            lookups_flat: Vec::new(),
            trashcans: Vec::new(),
            trashcans_flat: Vec::new(),
            sparse_gates: OnceLock::new(),
        };

        // Custom gates: gate polynomial `k` is multiplied by `y[k]`.
        let mut terms = Vec::new();
        for gate in cs.gates.iter() {
            for poly in gate.polynomials() {
                let part = ev.custom_gates.add_expression(poly);
                terms.push((ValueSource::Y(terms.len()), part));
            }
        }
        ev.custom_gates.add_calculation(Calculation::LinearCombination(
            ValueSource::PreviousValue(),
            terms,
        ));

        // Lookups: a tuple `(e_0, …, e_{l-1})` is compressed as `Σᵢ θᵢ·eᵢ`.
        let compress = |graph: &mut GraphEvaluator<F>, expressions: &[Expression<F>]| {
            let terms = (expressions.iter().enumerate())
                .map(|(i, expr)| (ValueSource::Theta(i), graph.add_expression(expr)))
                .collect();
            graph.add_calculation(Calculation::LinearCombination(
                ValueSource::Constant(0),
                terms,
            ))
        };
        for lookup in cs.lookups.iter() {
            let lookup = lookup.chunk_by_degree(cs.lookup_chunk_bound());
            let flat_evals = lookup
                .input_expression_chunks()
                .iter()
                .map(|chunk| {
                    let mut graph = GraphEvaluator::default();

                    // Each input expression gets compressed with θ and shifted by β
                    let compressed_inputs_cosets: Vec<_> = chunk
                        .iter()
                        .map(|expressions| {
                            let compressed = compress(&mut graph, expressions);

                            graph.add_calculation(Calculation::Add(compressed, ValueSource::Beta()))
                        })
                        .collect();

                    let compressed_table_coset = compress(&mut graph, lookup.table_expressions());

                    let partial_products = (0..compressed_inputs_cosets.len())
                        .map(|i| {
                            let mut acc =
                                graph.add_calculation(Calculation::Store(ValueSource::Constant(1)));
                            for (j, coset) in compressed_inputs_cosets.iter().enumerate() {
                                if j != i {
                                    acc = graph.add_calculation(Calculation::Mul(acc, *coset));
                                }
                            }
                            acc
                        })
                        .collect::<Vec<_>>();

                    let mut sum_partial_products =
                        graph.add_calculation(Calculation::Store(partial_products[0]));
                    let mut product =
                        graph.add_calculation(Calculation::Store(compressed_inputs_cosets[0]));
                    // Compute ∏ⱼ(fⱼ + β) and Σⱼ ∏_{k≠j}(fₖ + β)
                    for (calculation, partial_prod) in
                        compressed_inputs_cosets.into_iter().zip(partial_products).skip(1)
                    {
                        sum_partial_products = graph
                            .add_calculation(Calculation::Add(sum_partial_products, partial_prod));
                        product = graph.add_calculation(Calculation::Mul(product, calculation));
                    }

                    // Add β: compressed_table + β
                    let table = graph.add_calculation(Calculation::Add(
                        compressed_table_coset,
                        ValueSource::Beta(),
                    ));

                    let selector = graph.add_expression(lookup.selector_expression());
                    let selector = graph.add_calculation(Calculation::Store(selector));

                    LookupGraphEvaluator {
                        selector,
                        graph,
                        sum_partial_products,
                        product,
                        table,
                    }
                })
                .collect();

            ev.lookups.push(flat_evals);
        }

        // Trashcans
        for trash in cs.trashcans.iter() {
            let mut graph = GraphEvaluator::default();

            // Σ_j c^{m-1-j} · e_j, with the powers of `c` read from the buffer.
            let m = trash.constraint_expressions().len();
            let terms = trash
                .constraint_expressions()
                .iter()
                .enumerate()
                .map(|(j, expr)| (ValueSource::TrashPow(m - 1 - j), graph.add_expression(expr)))
                .collect();

            graph.add_calculation(Calculation::LinearCombination(
                ValueSource::Constant(0),
                terms,
            ));

            ev.trashcans.push(graph);
        }

        // Flatten all graphs for faster evaluation.
        ev.custom_gates_flat = ev.custom_gates.flatten();
        ev.lookups_flat = ev
            .lookups
            .iter()
            .map(|batch| batch.iter().map(|le| le.graph.flatten()).collect())
            .collect();
        ev.trashcans_flat = ev.trashcans.iter().map(|g| g.flatten()).collect();
        ev
    }

    /// Evaluate numerator polynomial `nu(X)` of the quotient polynomial
    /// `h(X) = nu(X) / (X^n-1)`.
    ///
    /// Folds the proof's `(advice, instance, lookups, trashcans, permutation)`
    /// identities into a `values` accumulator: identity `k` is multiplied by
    /// the verifier challenge `y[k]`, in the order of
    /// [`ConstraintSystem::nb_y_challenges`].
    ///
    /// TODO: drop the `previous_value` plumbing — the parameter on
    /// `FlatGraphEvaluator::evaluate` / `Calculation::evaluate`, the
    /// `ValueSource::PreviousValue` variant, the `previous_value_idx` slot,
    /// and the `LinearCombination(PreviousValue, ..)` start. With single-proof
    /// processing, `previous_value` is always `F::ZERO` and the leading
    /// `Add(prev, 0)` flat op is dead.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn evaluate_numerator<
        'p,
        B: PolynomialRepresentation + 'p,
        P: PolynomialRepresentation,
    >(
        &self,
        domain: &EvaluationDomain<F>,
        cs: &ConstraintSystem<F>,
        advice: &[Polynomial<F, B>],
        instance: &[Polynomial<F, B>],
        fixed: &[Polynomial<F, B>],
        y: &[F],
        beta: F,
        gamma: F,
        theta: &[F],
        trash_powers: &[F],
        phase1_committed: &'p argument::prover::Committed<F, P>,
        phase2_committed: &'p argument::prover::Committed<F, P>,
        to_b: impl Fn(&'p Polynomial<F, P>) -> Cow<'p, Polynomial<F, B>> + Sync,
        l0: &Polynomial<F, B>,
        l_last: &Polynomial<F, B>,
        l_active_row: &Polynomial<F, B>,
        permutation_cosets: &[Polynomial<F, B>],
    ) -> Polynomial<F, B> {
        let t_en = std::time::Instant::now();
        let mut values = self.evaluate_custom_gates(
            domain,
            cs,
            advice,
            instance,
            fixed,
            y,
            beta,
            theta,
            trash_powers,
        );
        let en_gates = t_en.elapsed().as_secs_f64() * 1e3;
        self.add_non_gate_identities(
            &mut values,
            domain,
            cs,
            advice,
            instance,
            fixed,
            y,
            beta,
            gamma,
            theta,
            trash_powers,
            phase1_committed,
            phase2_committed,
            to_b,
            l0,
            l_last,
            l_active_row,
            permutation_cosets,
        );
        eprintln!("[evaluate_numerator] gates={en_gates:.2}");
        values
    }

    /// The custom-gate part of the numerator: `Σ_k y[k]·gate_poly_k` at every
    /// point of `B`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn evaluate_custom_gates<B: PolynomialRepresentation>(
        &self,
        domain: &EvaluationDomain<F>,
        cs: &ConstraintSystem<F>,
        advice: &[Polynomial<F, B>],
        instance: &[Polynomial<F, B>],
        fixed: &[Polynomial<F, B>],
        y: &[F],
        beta: F,
        theta: &[F],
        trash_powers: &[F],
    ) -> Polynomial<F, B> {
        let log_scale = B::k(domain) - domain.k();
        let log_n = B::k(domain);
        assert_eq!(y.len(), cs.nb_y_challenges());
        let nb_gate_polys: usize = cs.gates.iter().map(|g| g.polynomials().len()).sum();
        let y_gates = &y[..nb_gate_polys];

        let mut values = B::empty(domain);

        // Custom gates — flattened evaluator with const-generic batch size.
        // BATCH is a compile-time constant so LLVM fully unrolls the inner
        // `for b in 0..BATCH` loops, amortizing opcode dispatch across
        // BATCH elements and exposing independent Fq ops to the CPU's
        // out-of-order pipeline.
        let flat = &self.custom_gates_flat;
        let template = flat.new_values_buffer(&beta, theta, trash_powers, y_gates);
        parallelize(&mut values, |values, start| {
            flat.evaluate_chunk::<4, B>(
                &template, values, start, fixed, advice, instance, log_scale, log_n,
            );
        });
        values
    }

    /// Adds the permutation, lookup and trash identities (those after the
    /// custom gates in the `y` order) to `values`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_non_gate_identities<
        'p,
        B: PolynomialRepresentation + 'p,
        P: PolynomialRepresentation,
    >(
        &self,
        values: &mut Polynomial<F, B>,
        domain: &EvaluationDomain<F>,
        cs: &ConstraintSystem<F>,
        advice: &[Polynomial<F, B>],
        instance: &[Polynomial<F, B>],
        fixed: &[Polynomial<F, B>],
        y: &[F],
        beta: F,
        gamma: F,
        theta: &[F],
        trash_powers: &[F],
        phase1_committed: &'p argument::prover::Committed<F, P>,
        phase2_committed: &'p argument::prover::Committed<F, P>,
        to_b: impl Fn(&'p Polynomial<F, P>) -> Cow<'p, Polynomial<F, B>> + Sync,
        l0: &Polynomial<F, B>,
        l_last: &Polynomial<F, B>,
        l_active_row: &Polynomial<F, B>,
        permutation_cosets: &[Polynomial<F, B>],
    ) {
        let log_scale = B::k(domain) - domain.k();
        let omega = B::omega(domain);
        let log_n = B::k(domain);
        let one = F::ONE;

        let p = &cs.permutation;

        // Split `y` into the challenges of each group of identities.
        assert_eq!(y.len(), cs.nb_y_challenges());
        let nb_gate_polys: usize = cs.gates.iter().map(|g| g.polynomials().len()).sum();
        let y_rest = &y[nb_gate_polys..];
        let (y_perm, mut y_rest) = y_rest.split_at(cs.nb_permutation_identities());
        // Per lookup: a boundary, one helper per chunk and an accumulator.
        let y_lookups: Vec<&[F]> = (self.lookups.iter())
            .map(|chunks| {
                let (y_lookup, rest) = y_rest.split_at(2 + chunks.len());
                y_rest = rest;
                y_lookup
            })
            .collect();
        let y_trash = y_rest;

        let t_en = std::time::Instant::now();
        // Permutations
        if !cs.permutation().columns.is_empty() {
            let blinding_factors = cs.blinding_factors();
            let last_rotation = Rotation(-((blinding_factors + 1) as i32));
            let chunk_len = cs.degree() - 2;
            let delta_start = beta * &B::g_coset(domain);

            let num_sets = cs.permutation().num_sets(cs.degree());

            let permutation_product_cosets: Vec<Cow<'p, Polynomial<F, B>>> = (0..num_sets)
                .into_par_iter()
                .map(|i| {
                    let poly =
                        phase2_committed.poly(&PolynomialLabel::PermutationAccumulator(i)).expect(
                            "the phase-2 group has no polynomial for a permutation accumulator",
                        );
                    to_b(poly)
                })
                .collect();

            let first_set_permutation_product_coset = permutation_product_cosets.first().unwrap();
            let last_set_permutation_product_coset = permutation_product_cosets.last().unwrap();

            // Permutation constraints
            parallelize(&mut *values, |values, start| {
                let mut beta_term = omega.pow_vartime([start as u64, 0, 0, 0]);
                for (i, value) in values.iter_mut().enumerate() {
                    let idx = start + i;
                    let r_next = get_rotation_idx(idx, 1, log_scale, log_n);
                    let r_last = get_rotation_idx(idx, last_rotation.0, log_scale, log_n);
                    let mut y = y_perm.iter();

                    // Enforce only for the first set.
                    // l_0(X) * (1 - z_0(X)) = 0
                    *value += *y.next().unwrap()
                        * (one - first_set_permutation_product_coset[idx])
                        * l0[idx];
                    // Enforce only for the last set.
                    // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
                    *value += *y.next().unwrap()
                        * (last_set_permutation_product_coset[idx]
                            * last_set_permutation_product_coset[idx]
                            - last_set_permutation_product_coset[idx])
                        * l_last[idx];
                    // Except for the first set, enforce.
                    // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
                    for set_idx in 0..num_sets {
                        if set_idx != 0 {
                            *value += *y.next().unwrap()
                                * (permutation_product_cosets[set_idx][idx]
                                    - permutation_product_cosets[set_idx - 1][r_last])
                                * l0[idx];
                        }
                    }
                    // And for all the sets we enforce:
                    // (1 - (l_last(X) + l_blind(X))) * (
                    //   z_i(\omega X) \prod_j (p(X) + \beta s_j(X) + \gamma)
                    // - z_i(X) \prod_j (p(X) + \delta^j \beta X + \gamma)
                    // )
                    let mut current_delta = delta_start * beta_term;
                    for ((permutation_product_coset, columns), cosets) in permutation_product_cosets
                        .iter()
                        .zip(p.columns.chunks(chunk_len))
                        .zip(permutation_cosets.chunks(chunk_len))
                    {
                        let mut left = permutation_product_coset[r_next];
                        for (values, permutation) in columns
                            .iter()
                            .map(|&column| match column.column_type() {
                                Any::Advice => &advice[column.index()],
                                Any::Fixed => &fixed[column.index()],
                                Any::Instance => &instance[column.index()],
                            })
                            .zip(cosets.iter())
                        {
                            left *= values[idx] + beta * permutation[idx] + gamma;
                        }

                        let mut right = permutation_product_coset[idx];
                        for values in columns.iter().map(|&column| match column.column_type() {
                            Any::Advice => &advice[column.index()],
                            Any::Fixed => &fixed[column.index()],
                            Any::Instance => &instance[column.index()],
                        }) {
                            right *= values[idx] + current_delta + gamma;
                            current_delta *= &F::DELTA;
                        }

                        *value += *y.next().unwrap() * (left - right) * l_active_row[idx];
                    }
                    beta_term *= &omega;
                }
            });
        }

        let en_perm = t_en.elapsed().as_secs_f64() * 1e3;
        let t_en = std::time::Instant::now();
        // Pre-compute all lookup cosets in parallel. This trades peak memory
        // for parallelism: the FFTs for different lookups can now overlap.
        let all_lookup_cosets: Vec<_> = cs
            .lookups
            .iter()
            .map(|l| l.chunk_by_degree(cs.lookup_chunk_bound()))
            .enumerate()
            .collect::<Vec<_>>()
            .par_iter()
            .map(|(argument_index, lookup)| {
                let multiplicities_poly = phase1_committed
                    .poly(&PolynomialLabel::LogupMultiplicities(*argument_index))
                    .unwrap();

                let helper_polys: Vec<_> = (0..lookup.input_expression_chunks.len())
                    .map(|j| {
                        phase2_committed
                            .poly(&PolynomialLabel::LogupHelper(*argument_index, j))
                            .unwrap()
                    })
                    .collect();

                let aggregator_poly = phase2_committed
                    .poly(&PolynomialLabel::LogupAggregator(*argument_index))
                    .unwrap();

                // Compute cosets

                let multiplicities_coset = to_b(multiplicities_poly);

                let helper_cosets: Vec<_> = helper_polys.into_iter().map(&to_b).collect();

                let aggregator_poly = to_b(aggregator_poly);

                (helper_cosets, aggregator_poly, multiplicities_coset)
            })
            .collect();

        // Pre-compute all trash cosets in parallel (lookup cosets
        // are already pre-computed above).
        let trash_cosets: Vec<_> = phase2_committed
            .par_polys()
            .filter_map(|(label, trash_poly)| match label {
                PolynomialLabel::Trash(_) => Some(to_b(trash_poly)),
                _ => None,
            })
            .collect();

        // Pre-resolve lookup output indices for the flat evaluator.
        let lookup_output_indices: Vec<Vec<(usize, usize, usize, usize)>> = self
            .lookups
            .iter()
            .zip(self.lookups_flat.iter())
            .map(|(batch, flat_batch)| {
                batch
                    .iter()
                    .zip(flat_batch.iter())
                    .map(|(le, flat)| {
                        (
                            flat.resolve_idx(le.sum_partial_products),
                            flat.resolve_idx(le.product),
                            flat.resolve_idx(le.table),
                            flat.resolve_idx(le.selector),
                        )
                    })
                    .collect()
            })
            .collect();

        // Pre-resolve trash selector column indices.
        let trash_selector_cols: Vec<usize> = cs
            .trashcans
            .iter()
            .map(|arg| match arg.selector() {
                Expression::Fixed(query) => query.column_index(),
                _ => unreachable!(),
            })
            .collect();

        // Fused lookup + trash constraint evaluation in a single pass
        // over `values`, using flattened evaluators for reduced dispatch.
        let en_lookup_pre = t_en.elapsed().as_secs_f64() * 1e3;
        let t_en = std::time::Instant::now();
        let run_block = |values: &mut Polynomial<F, B>, do_l: bool, do_t: bool| {
        parallelize(values, |values, start| {
            // Per-thread flat values buffers for all lookups.
            let mut all_lookup_bufs: Vec<Vec<Vec<F>>> = self
                .lookups_flat
                .iter()
                .map(|batch| {
                    batch
                        .iter()
                        .map(|flat| flat.new_values_buffer(&beta, theta, trash_powers, y))
                        .collect()
                })
                .collect();
            // Per-thread flat values buffers for all trash arguments.
            let mut trash_bufs: Vec<Vec<F>> = self
                .trashcans_flat
                .iter()
                .map(|flat| flat.new_values_buffer(&beta, theta, trash_powers, y))
                .collect();

            let mut rot_indices = vec![
                0usize;
                self.custom_gates_flat.rotations.len().max(
                    self.lookups_flat
                        .iter()
                        .flat_map(|b| b.iter())
                        .chain(self.trashcans_flat.iter())
                        .map(|f| f.rotations.len())
                        .max()
                        .unwrap_or(0)
                )
            ];

            for (i, value) in values.iter_mut().enumerate() {
                let idx = start + i;
                let r_next = get_rotation_idx(idx, 1, log_scale, log_n);

                // --- Lookup constraints ---
                if do_l { for (n, (helper_cosets, aggregator_coset, multiplicities_coset)) in
                    all_lookup_cosets.iter().enumerate()
                {
                    let mut y = y_lookups[n].iter();
                    *value += *y.next().unwrap() * aggregator_coset[idx] * (l0[idx] + l_last[idx]);

                    let mut sum_helpers = F::ZERO;
                    let mut table_value = F::ZERO;
                    let mut selector = F::ZERO;
                    let flat_batch = &self.lookups_flat[n];
                    let output_batch = &lookup_output_indices[n];
                    let bufs = &mut all_lookup_bufs[n];

                    for (fi, flat) in flat_batch.iter().enumerate() {
                        for (ri, rot) in flat.rotations.iter().enumerate() {
                            rot_indices[ri] = get_rotation_idx(idx, *rot, log_scale, log_n);
                        }
                        flat.evaluate::<B>(
                            &mut bufs[fi],
                            fixed,
                            advice,
                            instance,
                            &rot_indices,
                            &F::ZERO,
                        );

                        let (spp_idx, prod_idx, tbl_idx, sel_idx) = output_batch[fi];
                        let sum_partial_products = bufs[fi][spp_idx];
                        let product = bufs[fi][prod_idx];

                        // We only resolve the table and selector in the first batch
                        if fi == 0 {
                            table_value = bufs[fi][tbl_idx];
                            selector = bufs[fi][sel_idx];
                        }

                        // Helper constraint: h(X) · ∏ⱼ(fⱼ(X) + β) = Σⱼ ∏_{k≠j}(fₖ(X) + β)
                        *value += *y.next().unwrap()
                            * (helper_cosets[fi][idx] * product - sum_partial_products);

                        sum_helpers += helper_cosets[fi][idx];
                    }

                    // Accumulator constraint:
                    // (Z(ωX) - Z(X)- s·Σᵢhᵢ(X))·(t(X) + β) + m(X) = 0
                    *value += *y.next().unwrap()
                        * l_active_row[idx]
                        * ((aggregator_coset[r_next]
                            - aggregator_coset[idx]
                            - selector * sum_helpers)
                            * table_value
                            + multiplicities_coset[idx]);
                }

                } // end do_l
                // --- Trash constraints ---
                if do_t { for (n, trash_poly) in trash_cosets.iter().enumerate() {
                    let flat = &self.trashcans_flat[n];
                    for (ri, rot) in flat.rotations.iter().enumerate() {
                        rot_indices[ri] = get_rotation_idx(idx, *rot, log_scale, log_n);
                    }
                    let compressed_expression = flat.evaluate::<B>(
                        &mut trash_bufs[n],
                        fixed,
                        advice,
                        instance,
                        &rot_indices,
                        &F::ZERO,
                    );

                    let q = fixed[trash_selector_cols[n]][idx];
                    *value += y_trash[n] * (compressed_expression - (one - q) * trash_poly[idx]);
                } }
            }
        });
        };
        let diag = std::env::var("PERF2_DIAG").is_ok();
        let (mut v_l, mut v_t) = if diag { (values.clone(), values.clone()) } else { (values.clone(), values.clone()) };
        run_block(values, true, true);
        let en_final = t_en.elapsed().as_secs_f64() * 1e3;
        if diag {        let t_x = std::time::Instant::now();
        run_block(&mut v_l, true, false);
        let only_l = t_x.elapsed().as_secs_f64() * 1e3;
        let t_x = std::time::Instant::now();
        run_block(&mut v_t, false, true);
        let only_t = t_x.elapsed().as_secs_f64() * 1e3;
        eprintln!("[perf2] lookup+trash block: both={en_final:.2} lookup_only={only_l:.2} trash_only={only_t:.2}");
        }
        {
            static ONCE: std::sync::Once = std::sync::Once::new();
            ONCE.call_once(|| {
                let nl = cs.lookups.len();
                let nb: usize = self.lookups_flat.iter().map(|b| b.len()).sum();
                let widths: Vec<usize> = cs.lookups.iter().map(|l| l.table_expressions().len()).collect();
                eprintln!("[perf2] lookups={nl} flat_batches(helpers)={nb} table_widths={widths:?} trashcans={} perm_sets={} perm_cols={} cs.degree={}", cs.trashcans.len(), cs.permutation().num_sets(cs.degree()), cs.permutation().columns.len(), cs.degree());
            });
        }
        eprintln!(
            "[evaluate_numerator] perm={en_perm:.2} lookup_precomp={en_lookup_pre:.2} lookup+trash={en_final:.2}"
        );
    }
}

impl<F: PrimeField> Default for GraphEvaluator<F> {
    fn default() -> Self {
        Self {
            // Fixed positions to allow easy access
            constants: vec![F::ZERO, F::ONE, F::from(2u64)],
            rotations: Vec::new(),
            calculations: Vec::new(),
            num_intermediates: 0,
        }
    }
}

impl<F: PrimeField> GraphEvaluator<F> {
    /// Adds a rotation
    fn add_rotation(&mut self, rotation: &Rotation) -> usize {
        let position = self.rotations.iter().position(|&c| c == rotation.0);
        match position {
            Some(pos) => pos,
            None => {
                self.rotations.push(rotation.0);
                self.rotations.len() - 1
            }
        }
    }

    /// Adds a constant
    fn add_constant(&mut self, constant: &F) -> ValueSource {
        let position = self.constants.iter().position(|&c| c == *constant);
        ValueSource::Constant(match position {
            Some(pos) => pos,
            None => {
                self.constants.push(*constant);
                self.constants.len() - 1
            }
        })
    }

    /// Adds a calculation.
    /// Currently does the simplest thing possible: just stores the
    /// resulting value so the result can be reused  when that calculation
    /// is done multiple times.
    fn add_calculation(&mut self, calculation: Calculation) -> ValueSource {
        let existing_calculation = self.calculations.iter().find(|c| c.calculation == calculation);
        match existing_calculation {
            Some(existing_calculation) => ValueSource::Intermediate(existing_calculation.target),
            None => {
                let target = self.num_intermediates;
                self.calculations.push(CalculationInfo {
                    calculation,
                    target,
                });
                self.num_intermediates += 1;
                ValueSource::Intermediate(target)
            }
        }
    }

    /// Flattened evaluator of the single gate polynomial `poly`, returning
    /// `y[k]·poly` for the challenge `k` given as `Y(0)`.
    pub(crate) fn flat_single_gate(poly: &Expression<F>) -> FlatGraphEvaluator<F> {
        let mut graph = Self::default();
        let part = graph.add_expression(poly);
        graph.add_calculation(Calculation::LinearCombination(
            ValueSource::PreviousValue(),
            vec![(ValueSource::Y(0), part)],
        ));
        graph.flatten()
    }

    /// Generates an optimized evaluation for the expression
    fn add_expression(&mut self, expr: &Expression<F>) -> ValueSource {
        match expr {
            Expression::Constant(scalar) => self.add_constant(scalar),
            Expression::Selector(_selector) => unreachable!(),
            Expression::Fixed(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Fixed(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Advice(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Advice(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Instance(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Instance(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Negated(a) => match **a {
                Expression::Constant(scalar) => self.add_constant(&-scalar),
                _ => {
                    let result_a = self.add_expression(a);
                    match result_a {
                        ValueSource::Constant(0) => result_a,
                        _ => self.add_calculation(Calculation::Negate(result_a)),
                    }
                }
            },
            Expression::Sum(a, b) => {
                // Undo subtraction stored as a + (-b) in expressions
                match &**b {
                    Expression::Negated(b_int) => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b_int);
                        if result_a == ValueSource::Constant(0) {
                            self.add_calculation(Calculation::Negate(result_b))
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else {
                            self.add_calculation(Calculation::Sub(result_a, result_b))
                        }
                    }
                    _ => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b);
                        if result_a == ValueSource::Constant(0) {
                            result_b
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else if result_a <= result_b {
                            self.add_calculation(Calculation::Add(result_a, result_b))
                        } else {
                            self.add_calculation(Calculation::Add(result_b, result_a))
                        }
                    }
                }
            }
            Expression::Product(a, b) => {
                let result_a = self.add_expression(a);
                let result_b = self.add_expression(b);
                if result_a == ValueSource::Constant(0) || result_b == ValueSource::Constant(0) {
                    ValueSource::Constant(0)
                } else if result_a == ValueSource::Constant(1) {
                    result_b
                } else if result_b == ValueSource::Constant(1) {
                    result_a
                } else if result_a == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_b))
                } else if result_b == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_a))
                } else if result_a == result_b {
                    self.add_calculation(Calculation::Square(result_a))
                } else if result_a <= result_b {
                    self.add_calculation(Calculation::Mul(result_a, result_b))
                } else {
                    self.add_calculation(Calculation::Mul(result_b, result_a))
                }
            }
            Expression::Scaled(a, f) => {
                if *f == F::ZERO {
                    ValueSource::Constant(0)
                } else if *f == F::ONE {
                    self.add_expression(a)
                } else {
                    let cst = self.add_constant(f);
                    let result_a = self.add_expression(a);
                    self.add_calculation(Calculation::Mul(result_a, cst))
                }
            }
        }
    }
}

/// Simple evaluation of an expression
pub fn evaluate<F: Field, B: PolynomialRepresentation>(
    expression: &Expression<F>,
    size: usize,
    log_scale: u32,
    fixed: &[Polynomial<F, B>],
    advice: &[Polynomial<F, B>],
    instance: &[Polynomial<F, B>],
) -> Vec<F> {
    let mut values = vec![F::ZERO; size];
    let log_n = size.ilog2();
    parallelize(&mut values, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = start + i;
            *value = expression.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| {
                    fixed[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, log_scale, log_n)]
                },
                &|query| {
                    advice[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, log_scale, log_n)]
                },
                &|query| {
                    instance[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, log_scale, log_n)]
                },
                &|a| -a,
                &|a, b| a + b,
                &|a, b| a * b,
                &|a, scalar| a * scalar,
            );
        }
    });
    values
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use ff::Field;
    use midnight_curves::Fq;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::*;
    use crate::{
        plonk::{AdviceQuery, FixedQuery, InstanceQuery},
        poly::{LagrangeCoeff, Polynomial, Rotation},
    };

    fn rand_poly(rng: &mut ChaCha20Rng, n: usize) -> Polynomial<Fq, LagrangeCoeff> {
        Polynomial {
            values: (0..n).map(|_| Fq::random(&mut *rng)).collect(),
            _marker: PhantomData,
        }
    }

    // Note: We need this instead of Expression::evaluate to test for
    // Store as well.
    /// Reference evaluator for `GraphEvaluator` without flattening.
    #[allow(clippy::too_many_arguments)]
    fn ref_evaluate(
        graph: &GraphEvaluator<Fq>,
        fixed: &[Polynomial<Fq, LagrangeCoeff>],
        advice: &[Polynomial<Fq, LagrangeCoeff>],
        instance: &[Polynomial<Fq, LagrangeCoeff>],
        rots: &[usize],
        beta: Fq,
        theta: &[Fq],
        tc: &[Fq],
        y: &[Fq],
        prev: Fq,
    ) -> Fq {
        let mut im = vec![Fq::ZERO; graph.num_intermediates];
        let r = |vs: &ValueSource, im: &[Fq]| match *vs {
            ValueSource::Constant(i) => graph.constants[i],
            ValueSource::Intermediate(i) => im[i],
            ValueSource::Fixed(c, k) => fixed[c][rots[k]],
            ValueSource::Advice(c, k) => advice[c][rots[k]],
            ValueSource::Instance(c, k) => instance[c][rots[k]],
            ValueSource::Beta() => beta,
            ValueSource::Theta(i) => theta[i],
            ValueSource::TrashPow(i) => tc[i],
            ValueSource::Y(i) => y[i],
            ValueSource::PreviousValue() => prev,
        };
        for ci in &graph.calculations {
            im[ci.target] = match &ci.calculation {
                Calculation::Add(a, b) => r(a, &im) + r(b, &im),
                Calculation::Sub(a, b) => r(a, &im) - r(b, &im),
                Calculation::Mul(a, b) => r(a, &im) * r(b, &im),
                Calculation::Square(v) => r(v, &im).square(),
                Calculation::Double(v) => r(v, &im).double(),
                Calculation::Negate(v) => -r(v, &im),
                Calculation::Store(v) => r(v, &im),
                Calculation::LinearCombination(s, terms) => {
                    let mut acc = r(s, &im);
                    for (c, t) in terms {
                        acc += r(c, &im) * r(t, &im);
                    }
                    acc
                }
            };
        }
        *im.last().expect("non-empty graph")
    }

    /// Assert `FlatGraphEvaluator::{evaluate, evaluate_chunk}` agrees with the
    /// ref_evaluate for `graph` for several BATCH sizes.
    fn check_graph(graph: &GraphEvaluator<Fq>, n: usize, seed: u64) {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);

        let log_n = n.trailing_zeros();
        // Log scaling factor for the extended domain. No extended domain log 1 = 0.
        let log_scale = 0u32;

        let fixed: Vec<_> = (0..3).map(|_| rand_poly(&mut rng, n)).collect();
        let advice: Vec<_> = (0..3).map(|_| rand_poly(&mut rng, n)).collect();
        let instance: Vec<_> = (0..2).map(|_| rand_poly(&mut rng, n)).collect();

        let prev: Vec<_> = (0..n).map(|_| Fq::random(&mut rng)).collect();

        let beta = Fq::random(&mut rng);
        let tc: Vec<Fq> = (0..2).map(|_| Fq::random(&mut rng)).collect();
        let theta: Vec<Fq> = (0..3).map(|_| Fq::random(&mut rng)).collect();
        let y: Vec<Fq> = (0..3).map(|_| Fq::random(&mut rng)).collect();

        let flat = graph.flatten();
        let challenges = flat.new_values_buffer(&beta, &theta, &tc, &y);
        let rots = |idx: usize| -> Vec<usize> {
            graph
                .rotations
                .iter()
                .map(|&r| get_rotation_idx(idx, r, log_scale, log_n))
                .collect()
        };

        let expected: Vec<Fq> = (0..n)
            .map(|idx| {
                ref_evaluate(
                    graph,
                    &fixed,
                    &advice,
                    &instance,
                    &rots(idx),
                    beta,
                    &theta,
                    &tc,
                    &y,
                    prev[idx],
                )
            })
            .collect();

        // Per-element `evaluate` check.
        // Checks negative (under 0) and positive (over n) wrap-around.
        for idx in 0..n {
            let mut buf = flat.new_values_buffer(&beta, &theta, &tc, &y);
            let got = flat.evaluate::<LagrangeCoeff>(
                &mut buf,
                &fixed,
                &advice,
                &instance,
                &rots(idx),
                &prev[idx],
            );
            assert_eq!(expected[idx], got, "evaluate mismatch at idx={idx}");
        }

        // `evaluate_chunk` parity across BATCH sizes and partial windows.
        macro_rules! check_chunk {
            ($B:literal, $start:expr, $len:expr) => {{
                let mut out: Vec<Fq> = prev[$start..$start + $len].to_vec();
                flat.evaluate_chunk::<$B, LagrangeCoeff>(
                    &challenges,
                    &mut out,
                    $start,
                    &fixed,
                    &advice,
                    &instance,
                    log_scale,
                    log_n,
                );
                assert_eq!(
                    &expected[$start..$start + $len],
                    out.as_slice(),
                    "BATCH={} start={} len={}",
                    $B,
                    $start,
                    $len
                );
            }};
        }
        check_chunk!(1, 0, n);
        check_chunk!(2, 0, n);
        check_chunk!(3, 0, n);
        check_chunk!(4, 0, n);
        check_chunk!(8, 0, n);
        check_chunk!(4, 1, n - 1);
        check_chunk!(4, 3, 5);
        check_chunk!(4, n - 1, 1);
    }

    /// `FlatGraphEvaluator` must agree with the original `GraphEvaluator`,
    /// both for a hand-built graph that uses every [`Calculation`] variant
    /// and for a graph built via `add_expression`.
    #[test]
    fn flat_matches_graph() {
        // Hand-built graph: every Calculation variant, all column types,
        // negative/positive rotations, and every named challenge slot.
        let mut g = GraphEvaluator::<Fq>::default();
        let (rm1, r0, r1, r2) = (
            g.add_rotation(&Rotation(-1)),
            g.add_rotation(&Rotation(0)),
            g.add_rotation(&Rotation(1)),
            g.add_rotation(&Rotation(2)),
        );

        // Fixed, advice and instance value sources.
        let f0 = g.add_calculation(Calculation::Store(ValueSource::Fixed(0, r0)));
        let f1 = g.add_calculation(Calculation::Store(ValueSource::Fixed(1, rm1)));
        let a0 = g.add_calculation(Calculation::Store(ValueSource::Advice(0, r1)));
        let a1 = g.add_calculation(Calculation::Store(ValueSource::Advice(1, r2)));
        let i0 = g.add_calculation(Calculation::Store(ValueSource::Instance(0, r0)));

        // Operations on all types of value sources.
        let add = g.add_calculation(Calculation::Add(f0, a0));
        let sub = g.add_calculation(Calculation::Sub(a1, i0));
        let mul = g.add_calculation(Calculation::Mul(add, sub));
        let sq = g.add_calculation(Calculation::Square(a0));
        let dbl = g.add_calculation(Calculation::Double(f1));
        let neg = g.add_calculation(Calculation::Negate(mul));
        let wb = g.add_calculation(Calculation::Mul(add, ValueSource::Beta()));
        let wt = g.add_calculation(Calculation::Add(wb, ValueSource::Theta(1)));
        let wc = g.add_calculation(Calculation::Sub(wt, ValueSource::TrashPow(1)));

        // Constant as a Calculation operand.
        let with_const = g.add_calculation(Calculation::Add(neg, ValueSource::Constant(2)));

        // Linear combination on challenge Y(2) of previous calculations.
        let lc2 = g.add_calculation(Calculation::LinearCombination(
            ValueSource::Constant(0),
            [sq, dbl, neg, wc, with_const].into_iter().map(|t| (ValueSource::Y(2), t)).collect(),
        ));

        // Linear combination with indexed challenges of previous calculations.
        g.add_calculation(Calculation::LinearCombination(
            ValueSource::PreviousValue(),
            vec![
                (ValueSource::Y(0), sq),
                (ValueSource::Theta(2), dbl),
                (ValueSource::Y(1), lc2),
                (with_const, wc),
            ],
        ));
        check_graph(&g, 16, 0xCAFE);

        // Expression path: q * (a * b - c) + 7 * d.
        // Uses Sum / Product / Negated / Scaled simplifications inside
        // `add_expression`.
        let fixed_query = |col_idx, rot| {
            Expression::<Fq>::Fixed(FixedQuery {
                index: Some(col_idx),
                column_index: col_idx,
                rotation: Rotation(rot),
            })
        };
        let advice_query = |col_idx, rot| {
            Expression::<Fq>::Advice(AdviceQuery {
                index: Some(col_idx),
                column_index: col_idx,
                rotation: Rotation(rot),
            })
        };
        let instance_query = |col_idx, rot| {
            Expression::<Fq>::Instance(InstanceQuery {
                index: Some(col_idx),
                column_index: col_idx,
                rotation: Rotation(rot),
            })
        };

        let expr = fixed_query(0, 0)
            * (advice_query(0, 0) * advice_query(1, 1) - advice_query(2, -1))
            + Expression::Scaled(Box::new(instance_query(0, 0)), Fq::from(7u64));

        let mut g = GraphEvaluator::default();
        let _ = g.add_expression(&expr);
        check_graph(&g, 16, 0xBEEF);
    }
}
