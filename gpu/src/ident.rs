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

//! Content identity of public data: a SHA-256 tree digest over the bytes of
//! an SRS base slice or a proving-key polynomial, computed when the data is
//! registered. It is never computed over witness data.
//!
//! The slice is cut into [`CHUNK`]-byte chunks, each chunk is hashed (in
//! parallel), and the digest is SHA-256 of the length and the chunk digests:
//! a fixed function of the bytes, independent of the thread count.

/// Bytes per hashed chunk.
pub const CHUNK: usize = 16 << 20;

fn sha256(b: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: valid input and output buffers.
    unsafe { blst::blst_sha256(out.as_mut_ptr(), b.as_ptr(), b.len()) };
    out
}

/// The digest of `b`.
pub fn digest(b: &[u8]) -> [u8; 32] {
    let chunks: Vec<&[u8]> = b.chunks(CHUNK).collect();
    let mut ds = vec![[0u8; 32]; chunks.len()];
    let threads = std::thread::available_parallelism().map_or(4, |t| t.get()).clamp(1, 8);
    if chunks.len() <= 1 || threads == 1 {
        for (d, c) in ds.iter_mut().zip(&chunks) {
            *d = sha256(c);
        }
    } else {
        let per = chunks.len().div_ceil(threads);
        std::thread::scope(|sc| {
            for (dpart, cpart) in ds.chunks_mut(per).zip(chunks.chunks(per)) {
                sc.spawn(move || {
                    for (d, c) in dpart.iter_mut().zip(cpart) {
                        *d = sha256(c);
                    }
                });
            }
        });
    }
    let mut top = Vec::with_capacity(8 + 32 * ds.len());
    top.extend_from_slice(&(b.len() as u64).to_le_bytes());
    for d in &ds {
        top.extend_from_slice(d);
    }
    sha256(&top)
}

/// The bytes of a slice of plain limb arrays.
pub(crate) fn bytes_of<T: Copy>(v: &[T]) -> &[u8] {
    // SAFETY: `T` is a plain array of integers (no padding).
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
}

/// Whether a registered copy `snap` may serve a call on `v` (the registered
/// slice or a prefix of it): every element of `v` equals the registered one
/// at its index. An exact check of the whole slice at every lookup, so a call
/// is never served from a copy that differs from the caller's data as it is
/// now. Public data only (SRS points, proving-key polynomials).
pub fn serves<T: PartialEq>(snap: &[T], v: &[T]) -> bool {
    v.len() <= snap.len() && snap[..v.len()] == *v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_is_chunked_and_length_bound() {
        let a = vec![1u8; CHUNK + 5];
        assert_eq!(digest(&a), digest(&a.clone()));
        assert_ne!(digest(&a), digest(&a[..CHUNK + 4]));
        let x = [[1u64; 4], [2; 4], [3; 4]];
        assert!(serves(&x, &x[..2]) && serves(&x, &x));
        assert!(!serves(&x[..2], &x), "longer than the registration");
        // a change at any index is seen, the interior included
        for at in 0..3 {
            let mut y = x;
            y[at][2] ^= 1;
            assert!(!serves(&x, &y), "a change at {at}");
        }
    }
}
