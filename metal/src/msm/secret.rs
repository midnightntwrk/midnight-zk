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

//! Host values derived from the scalars: guards that zero them when dropped,
//! and the stack scrub.

use std::{
    mem::size_of,
    ops::{Deref, DerefMut},
    sync::atomic::{Ordering::SeqCst, compiler_fence},
};

/// Zeroes `len` bytes at `p` with volatile writes and a compiler fence, so the
/// zeroing is never elided, even right before the memory is freed.
///
/// # Safety
/// `p` is valid for writes of `len` bytes.
unsafe fn zero_volatile(p: *mut u8, len: usize) {
    // SAFETY: every write is within `[p, p + len)` (the caller's contract);
    // the word writes start at an 8-byte aligned address.
    unsafe {
        let head = p.align_offset(8).min(len);
        for i in 0..head {
            std::ptr::write_volatile(p.add(i), 0u8);
        }
        let words = (len - head) / 8;
        let w = p.add(head).cast::<u64>();
        for i in 0..words {
            std::ptr::write_volatile(w.add(i), 0u64);
        }
        for i in head + 8 * words..len {
            std::ptr::write_volatile(p.add(i), 0u8);
        }
    }
    compiler_fence(SeqCst);
}

/// Writes zero over `v` (a local derived from the scalars), volatile.
pub(super) fn wipe<T: Copy>(v: &mut T) {
    // SAFETY: `v` is valid for writes of `size_of::<T>()` bytes.
    unsafe { zero_volatile((v as *mut T).cast::<u8>(), size_of::<T>()) };
}

/// One value derived from the scalars, zeroed when dropped (unwinding
/// included).
pub(super) struct Secret<T: Copy>(pub(super) T);

impl<T: Copy> Deref for Secret<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Copy> DerefMut for Secret<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: Copy> Drop for Secret<T> {
    fn drop(&mut self) {
        wipe(&mut self.0);
        #[cfg(test)]
        tests::observe_wipe((&self.0 as *const T).cast(), size_of::<T>());
    }
}

/// A vector of values derived from the scalars; its whole allocation is
/// zeroed when dropped. It never grows past its initial capacity, because a
/// reallocation would leave the old block unzeroed.
pub(super) struct SecretVec<T: Copy>(Vec<T>);

impl<T: Copy> SecretVec<T> {
    pub(super) fn with_capacity(n: usize) -> Self {
        SecretVec(Vec::with_capacity(n))
    }

    /// Appends `s` if it fits in the capacity; `false` otherwise.
    pub(super) fn extend_within(&mut self, s: &[T]) -> bool {
        if self.0.capacity() - self.0.len() < s.len() {
            return false;
        }
        self.0.extend_from_slice(s);
        true
    }

    /// Appends `v` if it fits in the capacity.
    pub(super) fn push_within(&mut self, v: T) -> bool {
        self.extend_within(std::slice::from_ref(&v))
    }
}

impl<T: Copy> Deref for SecretVec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T: Copy> Drop for SecretVec<T> {
    fn drop(&mut self) {
        let p = self.0.as_mut_ptr().cast::<u8>();
        let bytes = self.0.capacity() * size_of::<T>();
        // SAFETY: the vector's allocation is `capacity` elements long (no
        // allocation, and `bytes` 0, for a zero capacity).
        unsafe { zero_volatile(p, bytes) };
        #[cfg(test)]
        tests::observe_wipe(p, bytes);
    }
}

/// Bytes of stack [`scrub_stack`] zeroes (the CUDA patch's `SCRUB_BYTES`).
pub(super) const SCRUB_BYTES: usize = 64 * 1024;

/// Zeroes [`SCRUB_BYTES`] of the calling thread's stack below the caller's
/// frame, where the host collection, `blst` or the CPU share left temporaries
/// derived from the scalars. The writes are volatile and the buffer escapes
/// through `black_box`; the function is out of line so the buffer lies below
/// the caller's frame.
#[inline(never)]
pub(super) fn scrub_stack() {
    let mut buf = std::mem::MaybeUninit::<[u64; SCRUB_BYTES / 8]>::uninit();
    let p = buf.as_mut_ptr().cast::<u64>();
    for i in 0..SCRUB_BYTES / 8 {
        // SAFETY: within `buf`.
        unsafe { std::ptr::write_volatile(p.add(i), 0) };
    }
    std::hint::black_box(p);
    compiler_fence(SeqCst);
}

/// Runs [`scrub_stack`] when dropped, on every exit including unwinding.
pub(super) struct ScrubOnExit;

impl Drop for ScrubOnExit {
    fn drop(&mut self) {
        scrub_stack();
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use blst::blst_p1;

    use super::*;
    use crate::msm::Xyzz;

    thread_local! {
        /// (bytes, whether all were zero) of each guard dropped on this
        /// thread, read just before the memory is released.
        static WIPES: RefCell<Vec<(usize, bool)>> = const { RefCell::new(Vec::new()) };
    }

    /// Called by the guards' `Drop` after their zeroing.
    pub(super) fn observe_wipe(p: *const u8, len: usize) {
        // SAFETY: the guard's memory, still allocated (called before it is
        // released).
        let zero = (0..len).all(|i| unsafe { std::ptr::read_volatile(p.add(i)) } == 0);
        WIPES.with(|w| w.borrow_mut().push((len, zero)));
    }

    fn wipes() -> Vec<(usize, bool)> {
        WIPES.with(|w| std::mem::take(&mut *w.borrow_mut()))
    }

    #[test]
    fn guards_zero_on_drop() {
        let _ = wipes();
        let mut v = SecretVec::<Xyzz>::with_capacity(5);
        assert!(v.extend_within(&[[7u64; 24]; 3]));
        assert!(!v.extend_within(&[[7u64; 24]; 3]), "past the capacity");
        assert!(v.push_within([9u64; 24]));
        drop(v);
        let s = Secret([5u64; 18]);
        drop(s);
        // the whole allocation (capacity, not length) of the vector
        assert_eq!(wipes(), vec![(5 * 192, true), (144, true)]);
    }

    #[test]
    fn guards_zero_on_unwind() {
        let _ = wipes();
        let r = std::panic::catch_unwind(|| {
            let mut v = SecretVec::<blst_p1>::with_capacity(4);
            let mut p = blst_p1::default();
            p.x.l = [3; 6];
            assert!(v.push_within(p));
            let _s = Secret([1u64; 18]);
            panic!("unwind with secrets held");
        });
        assert!(r.is_err());
        assert_eq!(wipes(), vec![(144, true), (4 * 144, true)]);
    }
}
