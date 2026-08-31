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

//! Test-only comparison of the in-circuit and off-circuit Fiat-Shamir
//! transcripts.
//!
//! Both verifiers must absorb the same field elements in the same order and
//! squeeze at the same points. When they do not, the only symptom is an
//! unsatisfiable circuit at some unrelated row. Recording both event streams
//! and diffing them names the operation where they diverged.
//!
//! Off-circuit, use [`TracingTranscript`] in place of a [`CircuitTranscript`].
//! In-circuit, the gadget is out of a test's reach, so [`in_circuit`] collects
//! its events on a per-thread channel that is off by default.

use std::io;

use ff::PrimeField;
use midnight_proofs::{
    circuit::Value,
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
};

use crate::hash::poseidon::{PoseidonState, constants::PoseidonField};

/// One observable Fiat-Shamir event.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptEvent {
    /// A field element absorbed, in canonical byte representation.
    Absorbed(Vec<u8>),
    /// A field element absorbed whose in-circuit value was unknown.
    AbsorbedUnknown,
    /// A challenge squeezed.
    Squeezed,
}

impl TranscriptEvent {
    fn summary(&self) -> String {
        match self {
            TranscriptEvent::Absorbed(bytes) => {
                let hex: String = bytes.iter().rev().map(|b| format!("{b:02x}")).collect();
                format!("absorb 0x{hex}")
            }
            TranscriptEvent::AbsorbedUnknown => "absorb <unknown>".into(),
            TranscriptEvent::Squeezed => "squeeze".into(),
        }
    }
}

fn absorbed<F: PrimeField>(value: &F) -> TranscriptEvent {
    TranscriptEvent::Absorbed(value.to_repr().as_ref().to_vec())
}

/// A [`CircuitTranscript`] that also records what it absorbs and squeezes.
///
/// Drop-in replacement in any function generic over [`Transcript`], such as
/// `plonk::prepare`.
#[derive(Clone, Debug)]
pub struct TracingTranscript<F: PoseidonField> {
    inner: CircuitTranscript<PoseidonState<F>>,
    events: Vec<TranscriptEvent>,
}

impl<F: PoseidonField> TracingTranscript<F> {
    /// The events recorded so far.
    pub fn events(&self) -> &[TranscriptEvent] {
        &self.events
    }

    fn record<T: Hashable<PoseidonState<F>>>(&mut self, input: &T) {
        self.events.extend(input.to_input().iter().map(absorbed))
    }
}

impl<F: PoseidonField> Transcript for TracingTranscript<F> {
    type Hash = PoseidonState<F>;

    fn init() -> Self {
        Self {
            inner: CircuitTranscript::init(),
            events: Vec::new(),
        }
    }

    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            inner: CircuitTranscript::init_from_bytes(bytes),
            events: Vec::new(),
        }
    }

    fn squeeze_challenge<T: Sampleable<Self::Hash>>(&mut self) -> T {
        self.events.push(TranscriptEvent::Squeezed);
        self.inner.squeeze_challenge()
    }

    fn common<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()> {
        self.record(input);
        self.inner.common(input)
    }

    fn read<T: Hashable<Self::Hash>>(&mut self) -> io::Result<T> {
        let value: T = self.inner.read()?;
        self.record(&value);
        Ok(value)
    }

    fn write<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()> {
        self.record(input);
        self.inner.write(input)
    }

    fn finalize(self) -> Vec<u8> {
        self.inner.finalize()
    }

    fn assert_empty(&mut self) -> io::Result<()> {
        self.inner.assert_empty()
    }
}

/// Per-thread channel for the in-circuit verifier's events.
///
/// The gadget runs deep inside circuit synthesis, out of reach of the test that
/// wants its events, hence the channel rather than a return value.
pub mod in_circuit {
    use std::cell::RefCell;

    use super::*;

    #[derive(Default)]
    struct Channel {
        on: bool,
        events: Vec<TranscriptEvent>,
    }

    thread_local! {
        static CHANNEL: RefCell<Channel> = RefCell::new(Channel::default());
    }

    /// Starts recording, discarding anything recorded before.
    pub fn start() {
        CHANNEL.with(|c| {
            let mut c = c.borrow_mut();
            c.on = true;
            c.events.clear();
        })
    }

    /// Stops recording and returns the events.
    pub fn take() -> Vec<TranscriptEvent> {
        CHANNEL.with(|c| {
            let mut c = c.borrow_mut();
            c.on = false;
            std::mem::take(&mut c.events)
        })
    }

    /// Drops the events recorded so far, keeping only those of the run starting
    /// here.
    ///
    /// Synthesis runs more than once per proof (`MockProver` sizes the circuit
    /// before assigning it) and each pass replays the whole transcript.
    pub fn new_run() {
        CHANNEL.with(|c| {
            let mut c = c.borrow_mut();
            if c.on {
                c.events.clear()
            }
        })
    }

    /// Records absorbed field elements.
    pub fn absorbed<F: PrimeField>(values: &[Value<F>]) {
        push_many(values.iter().map(|value| {
            let mut event = TranscriptEvent::AbsorbedUnknown;
            value.map(|f| event = super::absorbed(&f));
            event
        }))
    }

    /// Records a squeezed challenge.
    pub fn squeezed() {
        push_many(std::iter::once(TranscriptEvent::Squeezed))
    }

    fn push_many(events: impl Iterator<Item = TranscriptEvent>) {
        CHANNEL.with(|c| {
            let mut c = c.borrow_mut();
            if c.on {
                c.events.extend(events)
            }
        })
    }
}

/// Panics if the two event streams differ, reporting the first divergence.
///
/// `AbsorbedUnknown` matches any absorbed element: an in-circuit value is
/// unknown exactly when the circuit is synthesized without a witness, where
/// there is nothing to compare.
pub fn assert_streams_match(off_circuit: &[TranscriptEvent], in_circuit: &[TranscriptEvent]) {
    let matches = |a: &TranscriptEvent, b: &TranscriptEvent| match (a, b) {
        (TranscriptEvent::Absorbed(_), TranscriptEvent::AbsorbedUnknown) => true,
        (TranscriptEvent::AbsorbedUnknown, TranscriptEvent::Absorbed(_)) => true,
        _ => a == b,
    };

    assert!(
        !off_circuit.is_empty(),
        "no off-circuit transcript events were recorded"
    );
    assert!(
        !in_circuit.is_empty(),
        "no in-circuit transcript events were recorded"
    );

    let divergence = (0..off_circuit.len().max(in_circuit.len())).find(|&i| {
        match (off_circuit.get(i), in_circuit.get(i)) {
            (Some(a), Some(b)) => !matches(a, b),
            _ => true,
        }
    });

    let Some(i) = divergence else { return };

    // Set TRANSCRIPT_TRACE_DUMP to print both streams in full.
    if std::env::var("TRANSCRIPT_TRACE_DUMP").is_ok() {
        for (n, e) in off_circuit.iter().enumerate() {
            eprintln!("off {n}: {}", e.summary());
        }
        for (n, e) in in_circuit.iter().enumerate() {
            eprintln!("in  {n}: {}", e.summary());
        }
    }

    // The challenge count localises the divergence to a protocol phase.
    let nb_squeezes = off_circuit[..i].iter().filter(|e| **e == TranscriptEvent::Squeezed).count();
    let context: Vec<String> =
        off_circuit[i.saturating_sub(4)..i].iter().map(|e| e.summary()).collect();
    let describe = |events: &[TranscriptEvent]| match events.get(i) {
        Some(e) => e.summary(),
        None => format!("<end of stream, {} events>", events.len()),
    };

    panic!(
        "in-circuit and off-circuit transcripts diverge at event {i} \
         (after {nb_squeezes} challenges)\n  \
         off-circuit: {}\n  in-circuit:  {}\n  preceding:   [{}]",
        describe(off_circuit),
        describe(in_circuit),
        context.join(", "),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn absorb(byte: u8) -> TranscriptEvent {
        TranscriptEvent::Absorbed(vec![byte])
    }

    #[test]
    fn identical_streams_match() {
        let events = [absorb(1), TranscriptEvent::Squeezed, absorb(2)];
        assert_streams_match(&events, &events);
    }

    #[test]
    fn unknown_absorptions_match_anything_absorbed() {
        assert_streams_match(
            &[absorb(1), TranscriptEvent::Squeezed],
            &[TranscriptEvent::AbsorbedUnknown, TranscriptEvent::Squeezed],
        );
    }

    #[test]
    #[should_panic(expected = "diverge at event 1")]
    fn differing_values_are_reported() {
        assert_streams_match(&[absorb(1), absorb(2)], &[absorb(1), absorb(3)]);
    }

    #[test]
    #[should_panic(expected = "diverge at event 2")]
    fn a_missing_squeeze_is_reported() {
        assert_streams_match(
            &[absorb(1), absorb(2), TranscriptEvent::Squeezed],
            &[absorb(1), absorb(2), absorb(3)],
        );
    }

    #[test]
    #[should_panic(expected = "diverge at event 2")]
    fn a_prefix_is_reported() {
        assert_streams_match(&[absorb(1), absorb(2), absorb(3)], &[absorb(1), absorb(2)]);
    }

    #[test]
    #[should_panic(expected = "no in-circuit transcript events")]
    fn an_empty_stream_is_reported() {
        assert_streams_match(&[absorb(1)], &[]);
    }
}
