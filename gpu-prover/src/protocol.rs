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

//! The daemon protocol: newline-delimited JSON over a local Unix socket.
//!
//! One connection carries one request line and one reply line; the daemon
//! closes the connection after the reply. A request line is at most
//! [`MAX_REQUEST`] bytes and must arrive within the read deadline.
//!
//! Requests (field `op`):
//!
//! - `{"op":"health"}`: state of the daemon. Answered at once, also while a
//!   proof runs; takes no queue place.
//! - `{"op":"prove","input":PATH,"output":PATH,"zero_check":false}`: proves the
//!   input file (owner-only, mode 600) and writes the verified proof owner-only
//!   to `output`. `zero_check` is optional.
//! - `{"op":"stats"}`: start record, requests served and device bytes held.
//! - `{"op":"evict","tables":false}`: frees the resident proving-key copies
//!   (and the MSM tables with `tables`).
//! - `{"op":"stop"}`: graceful stop. The request in progress and the waiting
//!   one are served, then the daemon exits.
//!
//! A `prove` request may carry the caller's locked lock-file descriptor as
//! `SCM_RIGHTS` ancillary data on the request bytes (see [`crate::lock`]).
//!
//! Replies are one JSON object: `{"ok":true, ...}` or
//! `{"ok":false,"error":{"kind":KIND,"message":TEXT}}`. `KIND` is one of
//! `busy`, `bad-request`, `refused`, `input`, `output`, `prove`, `verify`,
//! `degraded`, `retired`, `daemon-lost` (a queued request whose daemon
//! retired before it ran). An error reply to `prove` also holds `request`,
//! the request id, once the input decoded. A reply to `prove` holds `record` (a
//! [`crate::report::ProofRecord`]) and `queue` (`wait_s`, `start_unix`,
//! `end_unix`). Replies and logs never repeat a field of the request.
//!
//! Queue: one request is served and one waits. While both places are
//! taken, a new connection gets `busy` at once and nothing is read from it
//! (a `health` request then also gets `busy`, which shows the daemon is
//! alive).

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// Longest request line, bytes.
pub const MAX_REQUEST: usize = 64 << 10;

/// Requests served plus requests waiting: one served, one waiting.
pub const QUEUE_PLACES: usize = 2;

/// A request.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Request {
    /// State of the daemon.
    Health {},
    /// Start record and counters.
    Stats {},
    /// Free the resident copies.
    Evict {
        /// Free the MSM tables too.
        #[serde(default)]
        tables: bool,
    },
    /// Graceful stop.
    Stop {},
    /// Prove one input.
    Prove {
        /// Input file (witness data; owner-only).
        input: PathBuf,
        /// Output file of the verified proof.
        output: PathBuf,
        /// Read every wiped device region back.
        #[serde(default)]
        zero_check: bool,
    },
}

impl Request {
    /// The protocol name of the request.
    pub fn op(&self) -> &'static str {
        match self {
            Request::Health {} => "health",
            Request::Stats {} => "stats",
            Request::Evict { .. } => "evict",
            Request::Stop {} => "stop",
            Request::Prove { .. } => "prove",
        }
    }

    /// Whether the request takes a queue place.
    pub fn queued(&self) -> bool {
        matches!(
            self,
            Request::Prove { .. } | Request::Evict { .. } | Request::Stats {}
        )
    }
}

/// The error part of a reply.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ErrorReply {
    /// The error kind.
    pub kind: String,
    /// A fixed or generated text that never repeats request content.
    pub message: String,
}

/// Times of a queued request.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct QueueRecord {
    /// Seconds from accept to the start of service.
    pub wait_s: f64,
    /// Start of service, Unix seconds.
    pub start_unix: f64,
    /// End of service, Unix seconds.
    pub end_unix: f64,
}

/// An error reply as JSON.
pub fn error_reply(kind: &str, message: &str) -> serde_json::Value {
    serde_json::json!({"ok": false, "error": {"kind": kind, "message": message}})
}

/// The `busy` reply.
pub fn busy_reply() -> serde_json::Value {
    error_reply("busy", "one request is served and one waits; refused")
}

/// Reads the error of a reply, if it is one.
pub fn reply_error(reply: &serde_json::Value) -> Option<ErrorReply> {
    if reply.get("ok").and_then(|v| v.as_bool()) == Some(true) {
        return None;
    }
    Some(
        reply
            .get("error")
            .and_then(|e| serde_json::from_value(e.clone()).ok())
            .unwrap_or(ErrorReply {
                kind: "bad-reply".into(),
                message: "reply without ok".into(),
            }),
    )
}

/// Current Unix time, seconds.
pub fn unix_s() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs_f64())
        .unwrap_or(0.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_round_trip() {
        let cases = [
            (r#"{"op":"health"}"#, Request::Health {}),
            (r#"{"op":"stats"}"#, Request::Stats {}),
            (r#"{"op":"stop"}"#, Request::Stop {}),
            (r#"{"op":"evict"}"#, Request::Evict { tables: false }),
            (
                r#"{"op":"evict","tables":true}"#,
                Request::Evict { tables: true },
            ),
            (
                r#"{"op":"prove","input":"/a","output":"/b"}"#,
                Request::Prove {
                    input: "/a".into(),
                    output: "/b".into(),
                    zero_check: false,
                },
            ),
        ];
        for (text, want) in cases {
            let got: Request = serde_json::from_str(text).unwrap();
            assert_eq!(got, want);
            let back: Request =
                serde_json::from_str(&serde_json::to_string(&got).unwrap()).unwrap();
            assert_eq!(back, want);
        }
    }

    #[test]
    fn bad_requests_are_refused() {
        for text in [
            r#"{"op":"fly"}"#,
            r#"{"op":"prove","input":"/a"}"#,
            r#"{"op":"health","seed":1}"#,
            r#"[1,2]"#,
        ] {
            assert!(serde_json::from_str::<Request>(text).is_err(), "{text}");
        }
    }

    #[test]
    fn error_replies() {
        let b = busy_reply();
        assert_eq!(reply_error(&b).unwrap().kind, "busy");
        assert!(reply_error(&serde_json::json!({"ok": true})).is_none());
        assert_eq!(
            reply_error(&serde_json::json!({})).unwrap().kind,
            "bad-reply"
        );
    }
}
