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

//! A fixed-capacity owner for witness-dependent field values of the hook
//! layer (feature `gpu`).
//!
//! An [`ErasingVec`] allocates its whole capacity once, at construction,
//! and never reallocates: it has no growing operation, and appending past
//! the capacity panics instead of moving the allocation. On drop it zeroes
//! the whole allocation (capacity, not only length) with volatile writes
//! and a compiler fence, so the writes cannot be removed as dead stores,
//! and only then frees the allocation. This crate does not depend on a
//! zeroing crate, so the volatile zeroing is written by hand here.
//!
//! [`ErasingVec::from_vec`] adopts the allocation of a stock `Vec` without
//! copying it, for values stock code hands over as a `Vec`; the allocation
//! is zeroed on drop from that point on. [`ErasingVec::into_vec`] is the
//! reverse hand-over, also without copying, for the point where stock code
//! that takes a `Vec` must finally receive the values; after that
//! hand-over the stock owner controls the allocation.
#![allow(unsafe_code)]

use std::{
    alloc::{Layout, alloc, dealloc, handle_alloc_error},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::{NonNull, write_volatile},
    sync::atomic::{Ordering, compiler_fence},
};

use ff::PrimeField;

/// Minimum bytes per thread of [`zero_bytes`].
const PAR_ZERO_BYTES: usize = 1 << 20;

/// The parts of the range are cut at multiples of this many bytes.
const ZERO_TASK_BYTES: usize = 1 << 18;

/// Most threads of one [`zero_bytes`] call: it is bound by memory bandwidth,
/// which a few cores saturate.
const MAX_ZERO_THREADS: usize = 8;

/// A pointer into the range of a [`zero_bytes`] call, sent to its threads.
#[derive(Clone, Copy)]
struct SendPtr(*mut u8);

// SAFETY: a `SendPtr` is only sent to the scoped threads of one
// `zero_bytes` call, which write disjoint parts of a range the caller
// guarantees writable and are joined before the call returns.
unsafe impl Send for SendPtr {}

/// Zeroes `bytes` bytes at `ptr` with volatile writes that the compiler
/// cannot remove: the zeroed memory is not read again before it is freed,
/// so plain writes to it could be removed as dead stores.
///
/// Large ranges are split over scoped threads, all joined before the return.
/// A part whose thread cannot be spawned is zeroed on the calling thread.
///
/// This does not use the rayon pool: it runs in `Drop`, where the caller may
/// hold a lock. A pool worker waiting on pool tasks could steal a task that
/// takes the same lock, or wait on workers blocked on it.
///
/// # Safety
/// `ptr` must be valid for writes of `bytes` bytes.
pub(crate) unsafe fn zero_bytes(ptr: *mut u8, bytes: usize) {
    let threads = zero_threads(bytes);
    if threads > 1 {
        // The last part may be shorter.
        let per_thread = bytes.div_ceil(threads).div_ceil(ZERO_TASK_BYTES) * ZERO_TASK_BYTES;
        let base = SendPtr(ptr);
        std::thread::scope(|scope| {
            let mut own = Vec::new();
            for part in 1..threads {
                let start = part * per_thread;
                if start >= bytes {
                    break;
                }
                let len = per_thread.min(bytes - start);
                let spawned = spawn_allowed()
                    && std::thread::Builder::new()
                        .name("zero-bytes".into())
                        .stack_size(64 << 10)
                        .spawn_scoped(scope, move || {
                            let base = base;
                            // SAFETY: `start + len <= bytes`, so the part
                            // lies within the range the caller guarantees
                            // writable, and no other thread writes it.
                            unsafe { zero_bytes_here(base.0.add(start), len) };
                        })
                        .is_ok();
                if !spawned {
                    own.push((start, len));
                }
            }
            // SAFETY: `per_thread.min(bytes)` bytes from the start of the
            // range, written by no other thread.
            unsafe { zero_bytes_here(ptr, per_thread.min(bytes)) };
            for (start, len) in own {
                // SAFETY: a part within the range whose thread was not
                // spawned, written by no other thread.
                unsafe { zero_bytes_here(ptr.add(start), len) };
            }
        });
    } else {
        // SAFETY: as guaranteed by the caller.
        unsafe { zero_bytes_here(ptr, bytes) };
    }
    compiler_fence(Ordering::SeqCst);
}

/// Threads for zeroing `bytes` bytes, the calling one included.
fn zero_threads(bytes: usize) -> usize {
    if bytes < PAR_ZERO_BYTES {
        return 1;
    }
    static AVAILABLE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    let available =
        *AVAILABLE.get_or_init(|| std::thread::available_parallelism().map_or(1, |n| n.get()));
    (bytes / PAR_ZERO_BYTES).clamp(1, available.min(MAX_ZERO_THREADS))
}

#[cfg(test)]
thread_local! {
    /// Simulates a failed spawn in [`zero_bytes`].
    static NO_SPAWN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

fn spawn_allowed() -> bool {
    #[cfg(test)]
    return !NO_SPAWN.with(|n| n.get());
    #[cfg(not(test))]
    true
}

/// [`zero_bytes`] on the calling thread.
///
/// # Safety
/// `ptr` must be valid for writes of `bytes` bytes.
unsafe fn zero_bytes_here(ptr: *mut u8, bytes: usize) {
    let head = ptr.align_offset(std::mem::align_of::<u64>()).min(bytes);
    let words = (bytes - head) / std::mem::size_of::<u64>();
    let tail = head + words * std::mem::size_of::<u64>();
    // SAFETY (all three loops): every address written is in
    // `ptr..ptr + bytes`, which the caller guarantees writable; the word
    // writes start at the aligned address `ptr + head`.
    for i in 0..head {
        unsafe { write_volatile(ptr.add(i), 0u8) };
    }
    let word_ptr = unsafe { ptr.add(head) } as *mut u64;
    for i in 0..words {
        unsafe { write_volatile(word_ptr.add(i), 0u64) };
    }
    for i in tail..bytes {
        unsafe { write_volatile(ptr.add(i), 0u8) };
    }
    compiler_fence(Ordering::SeqCst);
}

/// Zeroes the whole capacity of a stock `Vec` of field elements, with
/// the volatile writes and compiler fence of an [`ErasingVec`] drop,
/// without freeing it: the `Vec` keeps its length and capacity and is
/// freed by its stock owner afterwards, holding only zeros. For stock
/// owners, such as a stock polynomial, that must receive an erasing
/// buffer's allocation by hand-over and whose release the caller
/// controls. In tests the erasure is recorded like an [`ErasingVec`]
/// drop (see [`take_drop_records`]).
pub(crate) fn zero_vec<F: PrimeField>(v: &mut Vec<F>) {
    #[cfg(test)]
    let len = v.len();
    let cap = v.capacity();
    let bytes = cap * std::mem::size_of::<F>();
    #[cfg(test)]
    let nonzero_before = len > 0 && {
        // SAFETY: the first `len` elements are initialised (the spare
        // capacity may not be, so it is not read before the zeroing).
        let raw = unsafe {
            std::slice::from_raw_parts(v.as_ptr() as *const u8, len * std::mem::size_of::<F>())
        };
        raw.iter().any(|b| *b != 0)
    };
    if bytes > 0 {
        // SAFETY: the allocation of `v` holds `cap` elements, hence
        // `bytes` writable bytes at its pointer. Zero bytes are the
        // representation of the zero field element, so the elements
        // stay valid values for the stock drop that follows.
        unsafe { zero_bytes(v.as_mut_ptr() as *mut u8, bytes) };
    }
    #[cfg(test)]
    {
        // SAFETY: as above, still before any free.
        let all_zero_after = bytes == 0 || {
            let raw = unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, bytes) };
            raw.iter().all(|b| *b == 0)
        };
        DROP_RECORDS.lock().unwrap_or_else(|e| e.into_inner()).push(DropRecord {
            len,
            cap,
            nonzero_before,
            all_zero_after,
            thread: std::thread::current().id(),
        });
    }
}

/// A fixed-capacity buffer of field elements that zeroes its whole
/// allocation on drop and never reallocates. See the module docs.
pub struct ErasingVec<F> {
    ptr: NonNull<F>,
    len: usize,
    cap: usize,
    // `false` only for the test-only constructor over caller-owned
    // storage: the drop then zeroes the storage but does not free it.
    owned: bool,
    _marker: PhantomData<F>,
}

// SAFETY: as for `Vec<F>`, an `ErasingVec<F>` owns its elements.
unsafe impl<F: Send> Send for ErasingVec<F> {}
// SAFETY: as for `Vec<F>`.
unsafe impl<F: Sync> Sync for ErasingVec<F> {}

/// What a drop of an [`ErasingVec`] observed, recorded in tests only: the
/// bytes of the whole capacity were checked before and after zeroing.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct DropRecord {
    /// The length at drop.
    pub len: usize,
    /// The capacity at drop.
    pub cap: usize,
    /// Some byte of the capacity was non-zero before zeroing.
    pub nonzero_before: bool,
    /// Every byte of the capacity was zero after zeroing.
    pub all_zero_after: bool,
    /// The thread that released the buffer: tests that prove share the
    /// record list, so a test counts only its own thread's records.
    pub thread: std::thread::ThreadId,
}

#[cfg(test)]
static DROP_RECORDS: std::sync::Mutex<Vec<DropRecord>> = std::sync::Mutex::new(Vec::new());

/// The drop records since the last call, clearing them (tests only).
#[cfg(test)]
pub(crate) fn take_drop_records() -> Vec<DropRecord> {
    std::mem::take(&mut *DROP_RECORDS.lock().unwrap_or_else(|e| e.into_inner()))
}

impl<F: PrimeField> ErasingVec<F> {
    /// A buffer of `len` zero elements with capacity `len`.
    pub fn zeroed(len: usize) -> Self {
        Self::with_capacity_zeroed(len, len)
    }

    /// A buffer of `len` zero elements with the fixed capacity `cap`
    /// (`len <= cap`). The allocation size never changes afterwards.
    pub fn with_capacity_zeroed(cap: usize, len: usize) -> Self {
        assert!(len <= cap, "length past the fixed capacity");
        let ptr = if cap == 0 {
            NonNull::dangling()
        } else {
            let layout = Layout::array::<F>(cap).expect("capacity overflow");
            // SAFETY: the layout has non-zero size (`cap > 0` and a field
            // element is not zero-sized).
            let raw = unsafe { alloc(layout) } as *mut F;
            let Some(ptr) = NonNull::new(raw) else {
                handle_alloc_error(layout);
            };
            // SAFETY: the allocation holds `cap` elements; the first `len`
            // are initialised here and the rest stays uninitialised spare
            // capacity, as in a `Vec`.
            unsafe {
                for i in 0..len {
                    ptr.as_ptr().add(i).write(F::ZERO);
                }
            }
            ptr
        };
        ErasingVec {
            ptr,
            len,
            cap,
            owned: true,
            _marker: PhantomData,
        }
    }
}

impl<F> ErasingVec<F> {
    /// Adopts the allocation of `v` without copying or reallocating it.
    /// The whole capacity of `v` is zeroed when the result is dropped.
    pub fn from_vec(v: Vec<F>) -> Self {
        let mut v = std::mem::ManuallyDrop::new(v);
        ErasingVec {
            // SAFETY: a `Vec` pointer is never null.
            ptr: unsafe { NonNull::new_unchecked(v.as_mut_ptr()) },
            len: v.len(),
            cap: v.capacity(),
            owned: true,
            _marker: PhantomData,
        }
    }

    /// Hands the allocation back as a stock `Vec`, without copying,
    /// reallocating or zeroing it: the late hand-over to stock code that
    /// takes a `Vec`. The stock owner controls the allocation from here.
    pub fn into_vec(self) -> Vec<F> {
        assert!(self.owned, "caller-owned storage cannot become a Vec");
        let this = std::mem::ManuallyDrop::new(self);
        // SAFETY: the parts came from one live allocation of `cap`
        // elements with `len` initialised ones, which is not dropped here
        // (`ManuallyDrop`), so the allocation is neither zeroed nor freed.
        unsafe { Vec::from_raw_parts(this.ptr.as_ptr(), this.len, this.cap) }
    }

    /// Builds an owner over caller-owned storage (tests only): drop zeroes
    /// the whole `cap` elements at `ptr` but does not free them, so the
    /// caller can read the storage afterwards and free it itself.
    ///
    /// # Safety
    /// `ptr` must point to a live allocation of at least `cap` elements
    /// with the first `len` initialised, which stays live until the owner
    /// is dropped and is not freed through any other owner meanwhile.
    #[cfg(test)]
    pub unsafe fn from_raw_parts_in_caller_storage(ptr: *mut F, len: usize, cap: usize) -> Self {
        assert!(len <= cap, "length past the fixed capacity");
        ErasingVec {
            // SAFETY: the caller guarantees a live allocation.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            len,
            cap,
            owned: false,
            _marker: PhantomData,
        }
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the buffer holds no element.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The fixed capacity fixed at construction. It never changes.
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// A pointer to the first element. It never changes.
    pub fn as_ptr(&self) -> *const F {
        self.ptr.as_ptr()
    }

    /// The elements as a slice.
    pub fn as_slice(&self) -> &[F] {
        // SAFETY: `len` initialised elements at `ptr`.
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }

    /// The elements as a mutable slice.
    pub fn as_mut_slice(&mut self) -> &mut [F] {
        // SAFETY: `len` initialised elements at `ptr`, uniquely borrowed.
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }

    /// Shortens the buffer to `new_len` elements (no-op when not shorter).
    /// The removed elements are dropped and their bytes zeroed at once;
    /// the capacity and the address do not change.
    pub fn truncate(&mut self, new_len: usize) {
        if new_len >= self.len {
            return;
        }
        let old_len = self.len;
        self.len = new_len;
        // SAFETY: the elements in `new_len..old_len` were initialised and
        // are out of the buffer now, so they are dropped exactly once and
        // then their bytes are zeroed within the allocation.
        unsafe {
            let tail = self.ptr.as_ptr().add(new_len);
            std::ptr::drop_in_place(std::slice::from_raw_parts_mut(tail, old_len - new_len));
            zero_bytes(
                tail as *mut u8,
                (old_len - new_len) * std::mem::size_of::<F>(),
            );
        }
    }

    /// Appends one element within the fixed capacity. The address and the
    /// capacity do not change.
    ///
    /// # Panics
    /// When the buffer is already at its fixed capacity: appending never
    /// reallocates.
    pub fn push_fixed(&mut self, value: F) {
        assert!(
            self.len < self.cap,
            "push past the fixed capacity: an erasing buffer never reallocates"
        );
        // SAFETY: `len < cap`, so the slot at `len` is spare capacity of
        // the allocation and is initialised by this write.
        unsafe { self.ptr.as_ptr().add(self.len).write(value) };
        self.len += 1;
    }
}

impl<F> Deref for ErasingVec<F> {
    type Target = [F];

    fn deref(&self) -> &[F] {
        self.as_slice()
    }
}

impl<F> DerefMut for ErasingVec<F> {
    fn deref_mut(&mut self) -> &mut [F] {
        self.as_mut_slice()
    }
}

impl<F> From<Vec<F>> for ErasingVec<F> {
    fn from(v: Vec<F>) -> Self {
        Self::from_vec(v)
    }
}

impl<F: PartialEq> PartialEq<[F]> for ErasingVec<F> {
    fn eq(&self, other: &[F]) -> bool {
        self.as_slice() == other
    }
}

impl<F: PartialEq> PartialEq<Vec<F>> for ErasingVec<F> {
    fn eq(&self, other: &Vec<F>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<F: PartialEq> PartialEq<ErasingVec<F>> for ErasingVec<F> {
    fn eq(&self, other: &ErasingVec<F>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

/// Shapes only: the values are witness data and never reach a log.
impl<F> std::fmt::Debug for ErasingVec<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{} values>", self.len)
    }
}

impl<F> Drop for ErasingVec<F> {
    fn drop(&mut self) {
        let bytes = self.cap * std::mem::size_of::<F>();
        #[cfg(test)]
        let nonzero_before = self.len > 0 && {
            // SAFETY: the first `len` elements are initialised (the spare
            // capacity may not be, so it is not read before the zeroing).
            let raw = unsafe {
                std::slice::from_raw_parts(
                    self.ptr.as_ptr() as *const u8,
                    self.len * std::mem::size_of::<F>(),
                )
            };
            raw.iter().any(|b| *b != 0)
        };
        // SAFETY: the first `len` elements are initialised and dropped
        // exactly once here; afterwards the whole capacity (initialised
        // elements and spare capacity alike) is zeroed with volatile
        // writes before the allocation is freed.
        unsafe {
            std::ptr::drop_in_place(std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len));
            if bytes > 0 {
                zero_bytes(self.ptr.as_ptr() as *mut u8, bytes);
            }
        }
        #[cfg(test)]
        {
            // SAFETY: as above, still before the free.
            let all_zero_after = bytes == 0 || {
                let raw =
                    unsafe { std::slice::from_raw_parts(self.ptr.as_ptr() as *const u8, bytes) };
                raw.iter().all(|b| *b == 0)
            };
            DROP_RECORDS.lock().unwrap_or_else(|e| e.into_inner()).push(DropRecord {
                len: self.len,
                cap: self.cap,
                nonzero_before,
                all_zero_after,
                thread: std::thread::current().id(),
            });
        }
        if self.owned && self.cap > 0 {
            let layout = Layout::array::<F>(self.cap).expect("capacity overflow");
            // SAFETY: this allocation was made with this layout (by this
            // type or by the `Vec` it adopted, whose layout is the same).
            unsafe { dealloc(self.ptr.as_ptr() as *mut u8, layout) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::zero_bytes;

    /// At every alignment, below and above the parallel size, and when no
    /// thread can be spawned (the calling thread zeroes every part).
    #[test]
    fn zero_bytes_zeroes_exactly_the_range() {
        use super::{NO_SPAWN, PAR_ZERO_BYTES as PAR, ZERO_TASK_BYTES as TASK};

        let cases = [0, 1, 9, 63, PAR - 1, PAR, 3 * TASK + PAR + 5]
            .map(|bytes| (bytes, false))
            .into_iter()
            .chain([(9 * PAR + TASK + 7, true)]);
        for (bytes, no_spawn) in cases {
            for offset in 0..9 {
                let mut buf: Vec<u8> = (0..bytes + 32).map(|i| (i % 251) as u8 | 1).collect();
                let mut expected = buf.clone();
                expected[offset..offset + bytes].fill(0);
                NO_SPAWN.with(|n| n.set(no_spawn));
                // SAFETY: `offset + bytes <= buf.len()`.
                unsafe { zero_bytes(buf.as_mut_ptr().add(offset), bytes) };
                NO_SPAWN.with(|n| n.set(false));
                assert!(buf == expected, "bytes {bytes} offset {offset}");
            }
        }
    }

    /// The only worker of a pool, holding a lock that a queued pool task
    /// takes, zeroes without waiting on the pool.
    #[test]
    fn zero_bytes_on_a_pool_worker_holding_a_lock() {
        use std::sync::{Mutex, mpsc};

        static LOCK: Mutex<()> = Mutex::new(());
        let bytes = 4 * super::PAR_ZERO_BYTES + 5;
        let mut buf = vec![0xffu8; bytes];
        let (done_tx, done_rx) = mpsc::channel();
        let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
        pool.install(|| {
            let guard = LOCK.lock().unwrap();
            rayon::spawn(move || {
                let _guard = LOCK.lock().unwrap();
                done_tx.send(()).unwrap();
            });
            // SAFETY: the whole buffer.
            unsafe { zero_bytes(buf.as_mut_ptr(), bytes) };
            drop(guard);
        });
        done_rx.recv().unwrap();
        assert!(buf.iter().all(|b| *b == 0));
    }
}
