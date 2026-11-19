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

//! The actor's memory budget: a capacity, the bytes currently reserved,
//! and the FIFO admission queue.
//!
//! Fairness rule: strict FIFO with no bypass. Only the head of the
//! queue can be admitted, and only when its whole reservation fits
//! beside what is already reserved. A small later request never
//! overtakes a large waiting head, so no request starves: the head is
//! admitted as soon as enough bytes have been returned. A reservation
//! is never refused for lack of room here; it waits. (A reservation
//! above the capacity can never fit and is refused by the protocol at
//! submit time, before it reaches this queue.)
//!
//! Bytes are returned with [`Budget::release`], which the protocol
//! calls only after a buffer's wipe was confirmed, or at a reset where
//! the buffer was counted lost unerased.

use std::collections::VecDeque;

/// A job identifier. Buffer identifiers equal job identifiers in this
/// round: one buffer per job.
pub type JobId = u32;

/// The device-memory budget held by the actor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Budget {
    capacity: u64,
    reserved: u64,
    queue: VecDeque<JobId>,
}

impl Budget {
    /// A budget of `capacity` bytes (abstract units in the model) with
    /// nothing reserved and an empty queue.
    pub fn new(capacity: u64) -> Budget {
        Budget {
            capacity,
            reserved: 0,
            queue: VecDeque::new(),
        }
    }

    /// The total capacity.
    pub fn capacity(&self) -> u64 {
        self.capacity
    }

    /// Bytes currently reserved by admitted jobs. Never above
    /// [`Budget::capacity`].
    pub fn reserved(&self) -> u64 {
        self.reserved
    }

    /// The admission queue, head first.
    pub fn queue(&self) -> Vec<JobId> {
        self.queue.iter().copied().collect()
    }

    /// Puts a job at the back of the admission queue.
    pub fn enqueue(&mut self, job: JobId) {
        self.queue.push_back(job);
    }

    /// The job at the head of the queue, if any.
    pub fn head(&self) -> Option<JobId> {
        self.queue.front().copied()
    }

    /// Whether a reservation of `size` fits beside the reserved bytes.
    pub fn fits(&self, size: u64) -> bool {
        self.reserved.saturating_add(size) <= self.capacity
    }

    /// Admits the head job with reservation `size`: removes it from the
    /// queue and reserves its bytes. The caller (the protocol) has
    /// checked that the head is the job named and that it fits.
    pub fn admit_head(&mut self, size: u64) -> Option<JobId> {
        let job = self.queue.pop_front()?;
        self.reserved += size;
        Some(job)
    }

    /// Returns `size` bytes to the budget. Called by the protocol only
    /// after a confirmed wipe, or at a reset for a buffer counted lost
    /// unerased.
    pub fn release(&mut self, size: u64) {
        self.reserved = self.reserved.saturating_sub(size);
    }

    /// Removes a job from wherever it sits in the queue (teardown
    /// answers queued jobs without admitting them).
    pub fn remove(&mut self, job: JobId) {
        self.queue.retain(|j| *j != job);
    }

    /// Sets the reserved count when a state is rebuilt by the JSON
    /// codec. Not part of the admission protocol: nothing else calls
    /// it, because bytes otherwise move only through admit/release.
    pub(crate) fn restore(&mut self, reserved: u64) {
        self.reserved = reserved;
    }

    /// Empties the queue (teardown finish).
    pub fn clear_queue(&mut self) {
        self.queue.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn head_only_and_never_over_capacity() {
        let mut b = Budget::new(4);
        b.enqueue(0);
        b.enqueue(1);
        assert_eq!(b.head(), Some(0));
        assert!(b.fits(3));
        assert_eq!(b.admit_head(3), Some(0));
        assert_eq!(b.reserved(), 3);
        assert!(!b.fits(2), "3 + 2 exceeds capacity 4");
        b.release(3);
        assert_eq!(b.reserved(), 0);
        assert!(b.fits(2));
        assert_eq!(b.admit_head(2), Some(1));
    }

    #[test]
    fn remove_and_clear() {
        let mut b = Budget::new(4);
        b.enqueue(0);
        b.enqueue(1);
        b.enqueue(2);
        b.remove(1);
        assert_eq!(b.queue(), vec![0, 2]);
        b.clear_queue();
        assert!(b.queue().is_empty());
        assert_eq!(b.head(), None);
    }
}
