// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The job's polynomials and tables in the form of the numerator kernel
//! (`shaders/include/quotient.h`): the CUDA crate's arena of device pointers
//! (`Arena` in `gpu/src/quotient.rs`) becomes a buffer of 32-bit words with
//! word offsets, and a polynomial a handle `(bank << 30) | index` into one of
//! three flat buffers. Every check of the CUDA crate's `checked` and
//! `Arena::program` is made here, on host data, before any device work.

use std::collections::HashMap;

use super::abi::{
    COLUMN_ADVICE, COLUMN_FIXED, COLUMN_INSTANCE, INDEX_MASK, LookupAbi, OP_MUL_ADD, ProgramAbi,
    QuotientJobAbi, TAG_READ, TAG_SLOT, TAG_UNIFORM, TrashAbi, slice,
};
use crate::{Scalar, account::Reason, field};

/// A polynomial handle is `(bank << HANDLE_SHIFT) | index`.
pub(crate) const HANDLE_SHIFT: u32 = 30;
pub(crate) const BANK_PROOF: u32 = 0;
pub(crate) const BANK_KEY_RES: u32 = 1;
pub(crate) const BANK_KEY_TMP: u32 = 2;
/// Polynomials per bank.
pub(crate) const MAX_BANK_POLYS: usize = 1 << HANDLE_SHIFT;

/// The word counts of `shaders/include/quotient.h`.
const OP_WORDS: usize = 5;
const PROG_WORDS: usize = 8;
const LOOKUP_WORDS: usize = 4;
const CHUNK_WORDS: usize = 2;
const TRASH_WORDS: usize = 4;

/// The job, flattened: its polynomials and the kernel's tables.
pub(crate) struct Tables<'j> {
    /// The proof's polynomials (coefficients, `2^k` each), distinct, in the
    /// order of their cosets in the proof bank.
    pub(crate) proof: Vec<&'j [Scalar]>,
    /// The proving-key polynomials (extended cosets), distinct.
    pub(crate) keys: Vec<&'j [Scalar]>,
    /// The kernel's words. A key handle is written as its index in `keys`
    /// and fixed by [`Tables::place_keys`].
    pub(crate) words: Vec<u32>,
    /// The programs' uniforms.
    pub(crate) uniforms: Vec<Scalar>,
    /// The word offsets of the key handles in `words`.
    key_words: Vec<usize>,
    /// Word offsets of the gates program, the permutation's handles, the
    /// lookup descriptors and the trash descriptors.
    pub(crate) gates: u32,
    pub(crate) perm: u32,
    pub(crate) lookups: u32,
    pub(crate) trash: u32,
    /// Handles (key indices until placed) of `l0`, `l_last`, `l_active`.
    pub(crate) lagrange: [u32; 3],
    /// Field multiplications per row, about (the command-buffer split).
    pub(crate) cost_per_row: u64,
    /// The index of each distinct polynomial, by address.
    proof_ix: HashMap<usize, usize>,
    key_ix: HashMap<usize, usize>,
    /// The lengths of a proof polynomial and of a key polynomial.
    n: usize,
    en: usize,
}

fn handle(bank: u32, index: usize) -> u32 {
    (bank << HANDLE_SHIFT) | index as u32
}

/// The job's columns as handles (a fixed column as its key index).
struct Columns {
    advice: Vec<u32>,
    instance: Vec<u32>,
    /// `None`: a fixed column the job does not read.
    fixed: Vec<Option<u32>>,
}

impl Columns {
    /// `(handle, is a key index)` of column `c` of `kind`; `None` for a
    /// column the job does not have.
    fn get(&self, kind: u32, c: u32) -> Option<(u32, bool)> {
        match kind {
            COLUMN_FIXED => self.fixed.get(c as usize).copied().flatten().map(|h| (h, true)),
            COLUMN_ADVICE => self.advice.get(c as usize).map(|h| (*h, false)),
            COLUMN_INSTANCE => self.instance.get(c as usize).map(|h| (*h, false)),
            _ => None,
        }
    }
}

impl<'j> Tables<'j> {
    /// Flattens `j`, with every check of the CUDA crate's `checked` and
    /// `Arena::program` on its tables (`shape`, or `unreduced` for a
    /// program's uniform), in the CUDA crate's order.
    ///
    /// # Safety
    /// The job's contract: every pointer and count of `j` is valid, and its
    /// header has passed [`super::checked`] (so `k` and `ext_k` are lengths
    /// the polynomials have).
    pub(crate) unsafe fn new(j: &'j QuotientJobAbi) -> Result<Self, Reason> {
        let mut t = Tables {
            proof: Vec::new(),
            keys: Vec::new(),
            words: Vec::new(),
            uniforms: Vec::new(),
            key_words: Vec::new(),
            gates: 0,
            perm: 0,
            lookups: 0,
            trash: 0,
            lagrange: [0; 3],
            cost_per_row: 0,
            proof_ix: HashMap::new(),
            key_ix: HashMap::new(),
            n: 1usize << j.k,
            en: 1usize << j.ext_k,
        };
        // SAFETY (every `slice` and method below): the job's contract.
        let cols = unsafe {
            Columns {
                advice: slice(j.advice, j.nadvice)
                    .iter()
                    .map(|p| t.proof_handle(*p))
                    .collect::<Result<_, _>>()?,
                instance: slice(j.instance, j.ninstance)
                    .iter()
                    .map(|p| t.proof_handle(*p))
                    .collect::<Result<_, _>>()?,
                fixed: slice(j.fixed, j.nfixed)
                    .iter()
                    .map(|p| {
                        if p.is_null() {
                            Ok(None)
                        } else {
                            t.key_index(*p).map(Some)
                        }
                    })
                    .collect::<Result<_, _>>()?,
            }
        };
        for (i, p) in [j.l0, j.l_last, j.l_active].into_iter().enumerate() {
            // SAFETY: as above.
            t.lagrange[i] = unsafe { t.key_index(p)? };
        }
        // SAFETY: as above.
        unsafe {
            t.gates = t.program(&j.gates, j.nslots, &cols)?;
            if j.perm_nsets > 0 {
                t.permutation(j, &cols)?;
            }
            t.lookup_tables(slice(j.lookups, j.nlookups), j.nslots, &cols)?;
            t.trash_tables(slice(j.trash, j.ntrash), j.nslots, &cols)?;
        }
        if t.words.len() > u32::MAX as usize / 2 || t.uniforms.len() > u32::MAX as usize / 2 {
            return Err(Reason::Shape);
        }
        Ok(t)
    }

    /// A proof polynomial's handle (its coset in the proof bank).
    ///
    /// # Safety
    /// A non-null `p` is valid for `2^k` reads for `'j`.
    unsafe fn proof_handle(&mut self, p: *const Scalar) -> Result<u32, Reason> {
        if p.is_null() {
            return Err(Reason::Shape);
        }
        let next = self.proof_ix.len();
        let i = *self.proof_ix.entry(p as usize).or_insert_with(|| {
            // SAFETY: the caller's contract.
            self.proof.push(unsafe { slice(p, self.n) });
            next
        });
        if i >= MAX_BANK_POLYS {
            return Err(Reason::Shape);
        }
        Ok(handle(BANK_PROOF, i))
    }

    /// A key polynomial's index in `keys`.
    ///
    /// # Safety
    /// A non-null `p` is valid for `2^ext_k` reads for `'j`.
    unsafe fn key_index(&mut self, p: *const Scalar) -> Result<u32, Reason> {
        if p.is_null() {
            return Err(Reason::Shape);
        }
        let next = self.key_ix.len();
        let i = *self.key_ix.entry(p as usize).or_insert_with(|| {
            // SAFETY: the caller's contract.
            self.keys.push(unsafe { slice(p, self.en) });
            next
        });
        if i >= MAX_BANK_POLYS {
            return Err(Reason::Shape);
        }
        Ok(i as u32)
    }

    fn push_handle(&mut self, h: u32, key: bool) {
        if key {
            self.key_words.push(self.words.len());
        }
        self.words.push(h);
    }

    /// The permutation's handles: the accumulators, the permuted columns,
    /// the sigmas.
    ///
    /// # Safety
    /// The job's contract.
    unsafe fn permutation(&mut self, j: &'j QuotientJobAbi, cols: &Columns) -> Result<(), Reason> {
        // SAFETY: the job's contract.
        let (products, kinds, index, sigma) = unsafe {
            (
                slice(j.perm_products, j.perm_nsets),
                slice(j.perm_column_kind, j.perm_ncolumns),
                slice(j.perm_column_index, j.perm_ncolumns),
                slice(j.perm_sigma, j.perm_ncolumns),
            )
        };
        let start = self.words.len();
        for p in products {
            // SAFETY: the job's contract.
            let h = unsafe { self.proof_handle(*p)? };
            self.words.push(h);
        }
        for (k, c) in kinds.iter().zip(index) {
            let (h, key) = cols.get(*k, *c).ok_or(Reason::Shape)?;
            self.push_handle(h, key);
        }
        for s in sigma {
            // SAFETY: the job's contract.
            let i = unsafe { self.key_index(*s)? };
            self.push_handle(i, true);
        }
        self.perm = start as u32;
        self.cost_per_row += 4 * j.perm_ncolumns as u64 + 6 * j.perm_nsets as u64;
        Ok(())
    }

    /// The lookups: the programs first, then the chunk tables, then the
    /// descriptors.
    ///
    /// # Safety
    /// The job's contract.
    unsafe fn lookup_tables(
        &mut self,
        lookups: &[LookupAbi],
        nslots: u32,
        cols: &Columns,
    ) -> Result<(), Reason> {
        let mut descs = Vec::with_capacity(lookups.len());
        for l in lookups {
            if l.nchunks == 0 {
                return Err(Reason::Shape);
            }
            // SAFETY: the job's contract.
            let (progs, helpers) =
                unsafe { (slice(l.programs, l.nchunks), slice(l.helpers, l.nchunks)) };
            let mut chunks = Vec::with_capacity(l.nchunks);
            for (p, h) in progs.iter().zip(helpers) {
                if p.noutputs != 4 {
                    return Err(Reason::Shape);
                }
                // SAFETY: the job's contract.
                let off = unsafe { self.program(p, nslots, cols)? };
                // SAFETY: the job's contract.
                chunks.push((unsafe { self.proof_handle(*h)? }, off));
            }
            // SAFETY: the job's contract.
            let agg = unsafe { self.proof_handle(l.aggregator)? };
            // SAFETY: the job's contract.
            let mult = unsafe { self.proof_handle(l.multiplicities)? };
            descs.push((agg, mult, chunks));
            self.cost_per_row += 6 + 3 * l.nchunks as u64;
        }
        let mut chunk_offs = Vec::with_capacity(descs.len());
        for (_, _, chunks) in &descs {
            chunk_offs.push(self.words.len() as u32);
            for (h, off) in chunks {
                let chunk: [u32; CHUNK_WORDS] = [*h, *off];
                self.words.extend(chunk);
            }
        }
        self.lookups = self.words.len() as u32;
        for ((agg, mult, chunks), off) in descs.iter().zip(chunk_offs) {
            let desc: [u32; LOOKUP_WORDS] = [*agg, *mult, chunks.len() as u32, off];
            self.words.extend(desc);
        }
        Ok(())
    }

    /// The trash arguments: the programs first, then the descriptors.
    ///
    /// # Safety
    /// The job's contract.
    unsafe fn trash_tables(
        &mut self,
        trash: &[TrashAbi],
        nslots: u32,
        cols: &Columns,
    ) -> Result<(), Reason> {
        let mut descs = Vec::with_capacity(trash.len());
        for a in trash {
            if a.program.noutputs != 1 {
                return Err(Reason::Shape);
            }
            let sel = cols
                .fixed
                .get(a.selector_column as usize)
                .copied()
                .flatten()
                .ok_or(Reason::Shape)?;
            // SAFETY: the job's contract.
            let off = unsafe { self.program(&a.program, nslots, cols)? };
            // SAFETY: the job's contract.
            descs.push((unsafe { self.proof_handle(a.trash)? }, sel, off));
            self.cost_per_row += 3;
        }
        self.trash = self.words.len() as u32;
        for (h, sel, off) in descs {
            let desc: [u32; TRASH_WORDS] = [h, sel, off, 0];
            // the selector is a key handle
            self.key_words.push(self.words.len() + 1);
            self.words.extend(desc);
        }
        Ok(())
    }

    /// Packs a program after the checks of the CUDA crate's
    /// `Arena::program`: every operand in range, every slot below the job's
    /// slots, every read on a column the job has, the uniforms reduced.
    /// Returns its word offset.
    ///
    /// # Safety
    /// The job's contract: the program's pointers are valid for their counts.
    unsafe fn program(
        &mut self,
        p: &ProgramAbi,
        nslots: u32,
        cols: &Columns,
    ) -> Result<u32, Reason> {
        // SAFETY: the caller's contract.
        let (ops, reads, uniforms, outputs) = unsafe {
            (
                slice(p.ops, p.nops),
                slice(p.reads, p.nreads),
                slice(p.uniforms, p.nuniforms),
                slice(p.outputs, p.noutputs),
            )
        };
        let ok_operand = |o: u32| {
            let i = (o & INDEX_MASK) as usize;
            match o >> 30 {
                TAG_UNIFORM => i < uniforms.len(),
                TAG_READ => i < reads.len(),
                TAG_SLOT => i < nslots as usize,
                _ => false,
            }
        };
        let ops_ok = ops.iter().all(|op| {
            op.kind <= OP_MUL_ADD
                && op.dst < nslots
                && ok_operand(op.a)
                && ok_operand(op.b)
                && ok_operand(op.c)
        });
        if !ops_ok || !outputs.iter().all(|o| ok_operand(*o)) || p.nslots > nslots {
            return Err(Reason::Shape);
        }
        let read_cols: Vec<(u32, bool)> = reads
            .iter()
            .map(|r| cols.get(r.kind, r.column))
            .collect::<Option<_>>()
            .ok_or(Reason::Shape)?;
        if !field::all_reduced(uniforms) {
            return Err(Reason::Unreduced);
        }
        let ops_off = self.words.len() + PROG_WORDS;
        let reads_off = ops_off + OP_WORDS * ops.len();
        let outs_off = reads_off + 2 * reads.len();
        let start = self.words.len();
        let header: [u32; PROG_WORDS] = [
            ops_off as u32,
            ops.len() as u32,
            reads_off as u32,
            reads.len() as u32,
            self.uniforms.len() as u32,
            outs_off as u32,
            outputs.len() as u32,
            0,
        ];
        self.words.extend(header);
        for op in ops {
            let op: [u32; OP_WORDS] = [op.kind, op.dst, op.a, op.b, op.c];
            self.words.extend(op);
        }
        for (r, (h, key)) in reads.iter().zip(read_cols) {
            self.push_handle(h, key);
            self.words.push(r.rotation as u32);
        }
        self.words.extend_from_slice(outputs);
        self.uniforms.extend_from_slice(uniforms);
        self.cost_per_row += ops.len() as u64;
        Ok(start as u32)
    }

    /// Writes the key handles: `bank_of[i]` is `(bank, index)` of key `i`.
    /// Returns the handles of `l0`, `l_last`, `l_active`.
    pub(crate) fn place_keys(&mut self, bank_of: &[(u32, usize)]) -> [u32; 3] {
        // every key word holds an index into `keys`, which `bank_of` covers
        for &w in &self.key_words {
            let (b, i) = bank_of[self.words[w] as usize];
            self.words[w] = handle(b, i);
        }
        self.lagrange.map(|k| {
            let (b, i) = bank_of[k as usize];
            handle(b, i)
        })
    }
}
