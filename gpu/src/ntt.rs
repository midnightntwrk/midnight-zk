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

//! Host-to-host transforms on the device: the NTT (sppark, natural order),
//! through one grow-only device scratch that is zeroed and freed at the end
//! of a request.
use std::{ffi::c_void, sync::Mutex};

use crate::{
    Scalar,
    fault::{Class, Point, hit},
    ffi::{self, DevBuf},
};

static SCRATCH: Mutex<Option<DevBuf>> = Mutex::new(None);

/// The scratch of at least `bytes` (on the actor thread).
fn scratch(bytes: usize) -> Option<std::sync::MutexGuard<'static, Option<DevBuf>>> {
    let mut s = SCRATCH.lock().unwrap_or_else(|e| e.into_inner());
    if s.as_ref().is_none_or(|b| b.bytes < bytes) {
        // the old buffer is zeroed and freed (or quarantined) first
        *s = None;
        *s = Some(DevBuf::new(bytes, true)?);
    }
    Some(s)
}

/// Zeroes and frees the scratch (on the actor thread).
pub(crate) fn release_scratch() {
    *SCRATCH.lock().unwrap_or_else(|e| e.into_inner()) = None;
}

/// The NTT of `a` (length `2^lg`) in place: forward at the standard root, or
/// inverse (with sppark's `1/n`) and then times `post`. `a` changes only
/// when the whole read-back succeeded. Runs as one exclusive request
/// on the device-owner actor.
pub(crate) fn ntt(
    a: &mut [Scalar],
    lg: u32,
    inverse: bool,
    post: Option<Scalar>,
) -> Result<bool, ffi::CallError> {
    ffi::call_result(|| {
        let bytes = std::mem::size_of_val(a);
        let Some(s) = scratch(bytes) else {
            return false;
        };
        let d = s.as_ref().unwrap();
        let mut ok = ffi::htod(d, 0, a) && !hit(Class::Ntt, Point::Upload);
        // SAFETY: the scratch holds `2^lg` elements.
        ok = ok && unsafe { ffi::mgpu_ntt_dev(d.ptr, lg, inverse as i32) } == 0;
        if let (true, Some(c)) = (ok, post) {
            // SAFETY: as above; `c` is one element.
            ok = unsafe { ffi::mgpu_scale_dev(d.ptr, a.len(), c.as_ptr() as *const c_void) } == 0;
        }
        ok = ok && ffi::sync() && !hit(Class::Ntt, Point::Launch);
        ok = ok && ffi::dtoh_commit(a, d.ptr, hit(Class::Ntt, Point::Readback));
        if !ok {
            crate::diag!("midnight-gpu: ntt: {}", ffi::last_error());
        }
        ok
    })
}
