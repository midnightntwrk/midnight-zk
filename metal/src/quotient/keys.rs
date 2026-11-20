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

//! Resident proving-key copies (the CUDA crate's `register_key` and
//! `KeyHandle`).
//!
//! [`register_key`] records extended-coset polynomials by address, length and
//! content digest, each with a slot in the handle's device copy for that
//! length. [`plan`] lends one copy to a quotient for the call;
//! [`Lent::give_back`] returns it, or drops it if the handle is gone or the
//! copies were evicted meanwhile.
//!
//! Digest checks: inside a request a polynomial is checked at its first serve
//! and trusted after that (the registrant keeps it unchanged during the
//! request). Outside a request every serve checks every registered polynomial
//! it reads. A slot this call fills is hashed over the bytes copied into it,
//! so a slot is never marked present with unverified content. A polynomial
//! whose content changed is counted ([`key_stale`]), loses its registration
//! and is uploaded for the call only.
//!
//! The copies are freed at [`crate::end_request`] unless [`keep_resident`], by
//! [`evict_key_copies`], or when the handle is dropped.

use std::{
    collections::HashMap,
    sync::{
        Mutex, MutexGuard, OnceLock,
        atomic::{AtomicBool, AtomicU64, Ordering::Relaxed},
    },
};

use crate::{Scalar, ctx::Buffer};

/// Bytes per hashed chunk of the digest.
const CHUNK: usize = 16 << 20;

fn sha256(b: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: valid input and output buffers.
    unsafe { blst::blst_sha256(out.as_mut_ptr(), b.as_ptr(), b.len()) };
    out
}

/// The content digest of each of `vs`: SHA-256 of the length and of each
/// 16 MiB chunk's SHA-256, as the CUDA crate's `ident::digest`. All chunks are
/// hashed together on all cores.
pub(crate) fn digest_many(vs: &[&[Scalar]]) -> Vec<[u8; 32]> {
    let bytes: Vec<&[u8]> = vs
        .iter()
        .map(|v| {
            // SAFETY: plain limbs, no padding.
            unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, size_of_val(*v)) }
        })
        .collect();
    let chunks: Vec<&[u8]> = bytes.iter().flat_map(|b| b.chunks(CHUNK)).collect();
    let mut ds = vec![[0u8; 32]; chunks.len()];
    let threads = std::thread::available_parallelism()
        .map_or(4, |t| t.get())
        .clamp(1, 16)
        .min(chunks.len());
    if threads <= 1 {
        for (d, c) in ds.iter_mut().zip(&chunks) {
            *d = sha256(c);
        }
    } else {
        // each thread takes the next chunk
        let next = std::sync::atomic::AtomicUsize::new(0);
        std::thread::scope(|sc| {
            let hs: Vec<_> = (0..threads)
                .map(|_| {
                    sc.spawn(|| {
                        let mut done = Vec::new();
                        loop {
                            let i = next.fetch_add(1, Relaxed);
                            let Some(c) = chunks.get(i) else { break };
                            done.push((i, sha256(c)));
                        }
                        done
                    })
                })
                .collect();
            for h in hs {
                // `sha256` does not panic; only a failed allocation can, and the
                // hook turns that into a decline
                for (i, d) in h.join().expect("a digest thread") {
                    ds[i] = d;
                }
            }
        });
    }
    // each polynomial's chunk digests are the next `n` of `ds`
    let mut at = 0;
    bytes
        .iter()
        .map(|b| {
            let n = b.len().div_ceil(CHUNK);
            let mut top = Vec::with_capacity(8 + 32 * n);
            top.extend_from_slice(&(b.len() as u64).to_le_bytes());
            for d in &ds[at..at + n] {
                top.extend_from_slice(d);
            }
            at += n;
            sha256(&top)
        })
        .collect()
}

/// A registered polynomial.
struct Entry {
    /// The handle.
    id: u64,
    /// Its index in the handle's copy of its length (`key.1`).
    slot: usize,
    digest: [u8; 32],
    /// The request in which its content last matched the digest.
    seen: u64,
}

/// The device copy of the polynomials of one length of one handle.
struct KeyCopy {
    /// The handle's polynomials of this length (slots of the copy).
    npolys: usize,
    /// The copy, `npolys * len` values; `None` before the first quotient,
    /// after an eviction, or while lent.
    buf: Option<Buffer>,
    /// Which slots hold their polynomial, verified against its digest.
    present: Vec<bool>,
}

#[derive(Default)]
struct Registry {
    /// By `(address, length)`.
    entries: HashMap<(usize, usize), Entry>,
    /// By `(handle, polynomial length)`.
    copies: HashMap<(u64, usize), KeyCopy>,
    /// Increments at every eviction: a copy lent before it is not returned.
    evictions: u64,
}

impl Registry {
    /// Checks the polynomial at `key` against `digest`, its content's digest
    /// now. A match marks it checked in `epoch`; a mismatch counts it stale and
    /// drops its registration and slot. Returns whether it is still
    /// registered as `planned` with that content.
    fn check(
        &mut self,
        key: (usize, usize),
        planned: Option<(u64, usize)>,
        digest: &[u8; 32],
        epoch: u64,
    ) -> bool {
        let Some(e) = self.entries.get_mut(&key) else {
            return false;
        };
        if Some((e.id, e.slot)) != planned {
            return false;
        }
        if e.digest == *digest {
            e.seen = epoch;
            return true;
        }
        let (id, slot) = (e.id, e.slot);
        KEY_STALE.fetch_add(1, Relaxed);
        self.entries.remove(&key);
        // the slot no longer holds a registered polynomial
        if let Some(c) = self.copies.get_mut(&(id, key.1))
            && let Some(pr) = c.present.get_mut(slot)
        {
            *pr = false;
        }
        false
    }
}

static REGISTRY: Mutex<Option<Registry>> = Mutex::new(None);
static NEXT_ID: AtomicU64 = AtomicU64::new(1);
static KEY_STALE: AtomicU64 = AtomicU64::new(0);
/// The current request ([`begin_request`] and [`end_request`] increment it).
static EPOCH: AtomicU64 = AtomicU64::new(1);
/// Whether a request is open. Outside one every serve checks its digests.
static OPEN: AtomicBool = AtomicBool::new(false);
static KEEP: OnceLock<AtomicBool> = OnceLock::new();

fn registry() -> MutexGuard<'static, Option<Registry>> {
    REGISTRY.lock().unwrap_or_else(|e| e.into_inner())
}

fn keep() -> &'static AtomicBool {
    KEEP.get_or_init(|| {
        AtomicBool::new(std::env::var("MIDNIGHT_METAL_KEEP_KEYS").as_deref() == Ok("1"))
    })
}

/// Whether the device copies of registered proving-key polynomials stay after
/// a request (default `false`, or `MIDNIGHT_METAL_KEEP_KEYS=1`).
pub fn keep_resident() -> bool {
    keep().load(Relaxed)
}

/// Sets [`keep_resident`].
pub fn set_keep_resident(on: bool) {
    keep().store(on, Relaxed);
}

/// A new request: each digest is checked again at its next serve.
pub(crate) fn begin_request() {
    EPOCH.fetch_add(1, Relaxed);
    OPEN.store(true, Relaxed);
}

/// The end of a request: frees the copies unless [`keep_resident`].
pub(crate) fn end_request() {
    OPEN.store(false, Relaxed);
    // a request begun after this one ended checks again (a new epoch)
    EPOCH.fetch_add(1, Relaxed);
    if !keep_resident() {
        evict_key_copies();
    }
}

/// Frees every device copy (registrations stay). Returns the bytes freed; a
/// copy lent to a running quotient is freed when returned and not counted.
pub fn evict_key_copies() -> u64 {
    let mut freed = Vec::new();
    {
        let mut r = registry();
        let Some(r) = r.as_mut() else { return 0 };
        r.evictions += 1;
        for c in r.copies.values_mut() {
            freed.extend(c.buf.take());
            c.present.iter_mut().for_each(|p| *p = false);
        }
    }
    // zeroed in the background and pooled, outside the lock
    let bytes = freed.iter().map(|b| b.len_bytes() as u64).sum();
    crate::ctx::release_later(freed);
    bytes
}

/// The registration of proving-key polynomials. While it lives the registrant
/// keeps them alive and, within a request, unchanged. Dropping it frees the
/// device copies.
#[derive(Debug)]
pub struct KeyHandle {
    id: u64,
    keys: Vec<(usize, usize)>,
}

impl KeyHandle {
    /// Whether every registered polynomial still has its registered content
    /// (full digests).
    pub fn verify(&self, polys: &[&[Scalar]]) -> bool {
        if polys.len() != self.keys.len() {
            return false;
        }
        let ds = digest_many(polys);
        let r = registry();
        polys.iter().zip(&self.keys).zip(&ds).all(|((p, key), d)| {
            (p.as_ptr() as usize, p.len()) == *key
                && r.as_ref()
                    .and_then(|r| r.entries.get(key))
                    .is_some_and(|e| e.id == self.id && e.digest == *d)
        })
    }

    /// The bytes of this handle's device copies now (0 when not made, evicted
    /// or lent).
    pub fn resident_bytes(&self) -> u64 {
        registry().as_ref().map_or(0, |r| {
            r.copies
                .iter()
                .filter(|((id, _), _)| *id == self.id)
                .filter_map(|(_, c)| c.buf.as_ref())
                .map(|b| b.len_bytes() as u64)
                .sum()
        })
    }
}

impl Drop for KeyHandle {
    fn drop(&mut self) {
        let copies: Vec<KeyCopy> = {
            let mut r = registry();
            let Some(r) = r.as_mut() else { return };
            for key in &self.keys {
                if r.entries.get(key).is_some_and(|e| e.id == self.id) {
                    r.entries.remove(key);
                }
            }
            let mine: Vec<(u64, usize)> =
                r.copies.keys().filter(|(id, _)| *id == self.id).copied().collect();
            mine.iter().filter_map(|k| r.copies.remove(k)).collect()
        };
        // the buffers are zeroed and freed outside the registry lock
        drop(copies);
    }
}

/// Registers proving-key polynomials by their digests. A polynomial
/// registered again moves to the new handle. Each length has its own device
/// copy, and a quotient serves from the copy of its extended length only.
pub fn register_key(polys: &[&[Scalar]]) -> KeyHandle {
    let id = NEXT_ID.fetch_add(1, Relaxed);
    // hash before taking the lock
    let entries: Vec<((usize, usize), [u8; 32])> = polys
        .iter()
        .map(|p| (p.as_ptr() as usize, p.len()))
        .zip(digest_many(polys))
        .collect();
    let now = EPOCH.load(Relaxed);
    let mut r = registry();
    let r = r.get_or_insert_with(Registry::default);
    let mut keys = Vec::with_capacity(entries.len());
    // the next slot of each length
    let mut slots: HashMap<usize, usize> = HashMap::new();
    for (key, d) in entries {
        let next = slots.entry(key.1).or_default();
        r.entries.insert(
            key,
            Entry {
                id,
                slot: *next,
                digest: d,
                seen: now,
            },
        );
        *next += 1;
        keys.push(key);
    }
    for (len, npolys) in slots {
        r.copies.insert(
            (id, len),
            KeyCopy {
                npolys,
                buf: None,
                present: vec![false; npolys],
            },
        );
    }
    KeyHandle { id, keys }
}

/// Registered polynomials now.
pub fn keys_registered() -> usize {
    registry().as_ref().map_or(0, |r| r.entries.len())
}

/// Registered polynomials dropped at a quotient because their content
/// changed, since process start.
pub fn key_stale() -> u64 {
    KEY_STALE.load(Relaxed)
}

/// Where a proving-key polynomial of a job is read from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Place {
    /// Slot of the lent resident copy.
    Resident(usize),
    /// Uploaded for the call.
    Temp,
}

/// The resident copy lent to one quotient: returned by [`Lent::give_back`].
pub(crate) struct Lent {
    id: u64,
    /// The length of its polynomials: the job's extended length.
    len: usize,
    /// The copy (`None`: the caller allocates [`Lent::bytes`] bytes).
    pub(crate) buf: Option<Buffer>,
    pub(crate) npolys: usize,
    /// Which slots hold their verified polynomial; only [`settle`] sets one.
    pub(crate) present: Vec<bool>,
    /// The registry's evictions when it was lent.
    evictions: u64,
}

impl Lent {
    /// The bytes of the copy: `npolys` polynomials of the job's length.
    pub(crate) fn bytes(&self) -> usize {
        self.npolys * self.len * size_of::<Scalar>()
    }

    /// Returns the copy to the registry when its handle lives and no eviction
    /// happened; drops it otherwise.
    pub(crate) fn give_back(self) {
        let back = {
            let mut r = registry();
            match r.as_mut() {
                Some(r) if r.evictions == self.evictions => {
                    match r.copies.get_mut(&(self.id, self.len)) {
                        Some(c) if c.buf.is_none() && c.npolys == self.npolys => {
                            c.buf = self.buf;
                            c.present = self.present;
                            None
                        }
                        _ => self.buf,
                    }
                }
                _ => self.buf,
            }
        };
        // dropped outside the registry lock
        drop(back);
    }
}

/// The placement of a job's proving-key polynomials, made by [`plan`] and
/// settled by [`settle`].
pub(crate) struct Plan {
    /// Where each polynomial is read from, assuming that every registered
    /// one still has its content; [`settle`] makes a stale one `Temp`.
    pub(crate) places: Vec<Place>,
    /// The copy lent for the call.
    pub(crate) lent: Option<Lent>,
    /// Indices of the registered polynomials whose digest is checked in this
    /// call, ascending.
    pub(crate) check: Vec<usize>,
    /// `(handle, slot)` of each registered polynomial as [`plan`] found it.
    regs: Vec<Option<(u64, usize)>>,
    /// The request of the plan.
    epoch: u64,
}

impl Plan {
    /// Whether polynomial `i` goes in a slot this call fills; its digest is
    /// then computed over the bytes copied into the slot.
    pub(crate) fn fills(&self, i: usize) -> bool {
        match (self.places[i], self.lent.as_ref()) {
            (Place::Resident(slot), Some(l)) => !l.present[slot],
            _ => false,
        }
    }

    /// Placed polynomials whose digest is checked in this call.
    pub(crate) fn resident_checked(&self) -> usize {
        self.check
            .iter()
            .filter(|&&i| matches!(self.places[i], Place::Resident(_)))
            .count()
    }
}

/// The handle with the most registered polynomials of length `en` (lowest id
/// on ties).
fn most_registered(regs: &[Option<(u64, usize)>], keys: &[&[Scalar]], en: usize) -> Option<u64> {
    let mut counts: HashMap<u64, usize> = HashMap::new();
    for ((id, _), k) in regs.iter().zip(keys).filter_map(|(f, k)| f.map(|f| (f, k))) {
        if k.len() == en {
            *counts.entry(id).or_default() += 1;
        }
    }
    counts.into_iter().max_by_key(|(id, n)| (*n, u64::MAX - id)).map(|c| c.0)
}

/// Plans the placement of the job's proving-key polynomials (`keys`, all of
/// length `en`) without hashing them: the handle with the most of them lends
/// its copy and its polynomials go in their slots; the others are uploaded.
/// The caller hashes [`Plan::check`] while the device works, and [`settle`]
/// drops stale ones before any slot is read.
pub(crate) fn plan(keys: &[&[Scalar]], en: usize) -> Plan {
    let now = EPOCH.load(Relaxed);
    let open = OPEN.load(Relaxed);
    let mut p = Plan {
        places: vec![Place::Temp; keys.len()],
        lent: None,
        check: Vec::new(),
        regs: vec![None; keys.len()],
        epoch: now,
    };
    let mut released = Vec::new();
    {
        let mut r = registry();
        let Some(reg) = r.as_mut() else {
            return p;
        };
        for (i, k) in keys.iter().enumerate() {
            let key = (k.as_ptr() as usize, k.len());
            let Some(e) = reg.entries.get(&key) else {
                continue;
            };
            p.regs[i] = Some((e.id, e.slot));
            if !open || e.seen != now {
                p.check.push(i);
            }
        }
        // the length is part of the registration's key, so the copy of
        // length `en` holds every polynomial counted
        if let Some(best) = most_registered(&p.regs, keys, en)
            && let Some(c) = reg.copies.get_mut(&(best, en))
            && c.present.len() == c.npolys
        {
            // memory-safety guards, unreachable for a registry built by
            // `register_key`: a buffer not laid out for this length is freed,
            // not read, and a slot past the copy is not used
            let bytes = c.npolys * en * size_of::<Scalar>();
            if c.buf.as_ref().is_some_and(|b| b.len_bytes() != bytes) {
                released.extend(c.buf.take());
            }
            for ((pl, f), k) in p.places.iter_mut().zip(&p.regs).zip(keys) {
                if let Some((id, slot)) = f
                    && *id == best
                    && k.len() == en
                    && *slot < c.npolys
                {
                    *pl = Place::Resident(*slot);
                }
            }
            // without a copy no slot is present
            let present = if c.buf.is_some() {
                c.present.clone()
            } else {
                vec![false; c.npolys]
            };
            p.lent = Some(Lent {
                id: best,
                len: en,
                buf: c.buf.take(),
                npolys: c.npolys,
                present,
                evictions: reg.evictions,
            });
        }
    }
    crate::ctx::release_later(released);
    // every slot filled by this call is verified in this call
    for i in 0..keys.len() {
        if p.fills(i) && !p.check.contains(&i) {
            p.check.push(i);
        }
    }
    p.check.sort_unstable();
    p
}

/// Settles a [`plan`] with the digests of [`Plan::check`], in order. A match
/// marks the polynomial checked and its filled slot present; a mismatch, or a
/// registration gone meanwhile, makes it `Temp` and drops its registration and
/// slot. Returns whether a polynomial placed in a slot became `Temp`.
pub(crate) fn settle(p: &mut Plan, keys: &[&[Scalar]], digests: &[[u8; 32]]) -> bool {
    debug_assert_eq!(p.check.len(), digests.len());
    let mut moved = false;
    let mut r = registry();
    for (&i, d) in p.check.iter().zip(digests) {
        let key = (keys[i].as_ptr() as usize, keys[i].len());
        let fresh = r.as_mut().is_some_and(|reg| reg.check(key, p.regs[i], d, p.epoch));
        let Place::Resident(slot) = p.places[i] else {
            continue;
        };
        // filled by this call and verified, or present already
        if let Some(pr) = p.lent.as_mut().and_then(|l| l.present.get_mut(slot)) {
            *pr = fresh;
        }
        if !fresh {
            p.places[i] = Place::Temp;
            moved = true;
        }
    }
    moved
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The digest of each polynomial, one at a time, as the definition
    /// reads: SHA-256 of the length and of each chunk's SHA-256.
    fn reference(v: &[Scalar]) -> [u8; 32] {
        // SAFETY: plain limbs, no padding.
        let b = unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, size_of_val(v)) };
        let mut top = (b.len() as u64).to_le_bytes().to_vec();
        for c in b.chunks(CHUNK) {
            top.extend_from_slice(&sha256(c));
        }
        sha256(&top)
    }

    /// Hashing several polynomials together gives each one's own digest
    /// (empty, shorter than a chunk, several chunks with a partial last one).
    #[test]
    fn digests_of_several_polynomials_are_their_own() {
        let words = |n: usize, seed: u64| -> Vec<Scalar> {
            (0..n as u64)
                .map(|i| [i ^ seed, i.wrapping_mul(0x9e37_79b9_7f4a_7c15), seed, !i])
                .collect()
        };
        let per_chunk = CHUNK / size_of::<Scalar>();
        let polys = [
            words(0, 1),
            words(3, 2),
            words(per_chunk, 3),
            words(2 * per_chunk + 5, 4),
            words(per_chunk / 2, 5),
        ];
        let refs: Vec<&[Scalar]> = polys.iter().map(|p| p.as_slice()).collect();
        let want: Vec<[u8; 32]> = refs.iter().map(|p| reference(p)).collect();
        assert_eq!(digest_many(&refs), want);
        assert_eq!(digest_many(&refs[3..4]), want[3..4]);
        assert!(digest_many(&[]).is_empty());
    }
}
