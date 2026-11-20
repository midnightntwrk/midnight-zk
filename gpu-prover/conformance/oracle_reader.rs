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

//! Submit a complete prove request through the daemon reader on a socket pair.
use super::*;

fn shared(places: usize) -> Arc<Shared> {
    Arc::new(Shared {
        stop: AtomicBool::new(false),
        places: AtomicUsize::new(places),
        readers: AtomicUsize::new(1),
        proving: AtomicBool::new(false),
        served: AtomicU64::new(0),
        retired: Mutex::new(None),
        started: Instant::now(),
        health: Value::Null,
    })
}

pub(crate) fn reserve_place(places: &AtomicUsize) -> bool {
    let shared = shared(places.load(SeqCst));
    let (client, server) = UnixStream::pair().unwrap();
    let req = Request::Prove {
        input: "input".into(),
        output: "output".into(),
        zero_check: true,
    };
    let mut writer = std::fs::File::from(std::os::fd::OwnedFd::from(client));
    writeln!(writer, "{}", serde_json::to_string(&req).unwrap()).unwrap();
    let (tx, jobs) = mpsc::channel();
    reader(server, shared.clone(), tx, READ_DEADLINE);
    places.store(shared.places.load(SeqCst), SeqCst);
    jobs.try_recv().is_ok()
}

#[test]
#[ignore = "strict GPU-046 conformance probe"]
fn saturated_reader_before_request_bytes() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("saturated.sock");
    let listener =
        UnixListener::bind(&path).expect("bind conformance socket for the daemon acceptor");
    let shared = shared(QUEUE_PLACES);
    let (tx, _jobs) = mpsc::channel();
    std::thread::scope(|scope| {
        let state = shared.clone();
        scope.spawn(move || acceptor(listener, state, tx, Duration::from_secs(5)));
        let response = (|| -> std::io::Result<String> {
            let client = UnixStream::connect(&path)?;
            client.set_read_timeout(Some(Duration::from_secs(1)))?;
            let mut line = String::new();
            std::io::BufRead::read_line(&mut std::io::BufReader::new(client), &mut line)?;
            Ok(line)
        })();
        shared.stop.store(true, SeqCst);
        let line = response.expect("saturated acceptor must reply before reading a request");
        let reply: Value = serde_json::from_str(&line).expect("busy JSON reply");
        assert_eq!(protocol::reply_error(&reply).unwrap().kind, "busy");
    });
}
