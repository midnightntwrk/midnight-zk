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

//! Service and client configuration.
//!
//! Every value has a documented default. A value is taken, in increasing
//! order of precedence, from the default, from a JSON config file, and from an
//! environment variable. Command-line flags of the binaries override all three.
//!
//! The config file is a JSON object whose keys are the field names of
//! [`Config`] (for example `{"max_k": 22, "resident": "keep"}`). Unknown keys
//! are an error. Its path is given by `MIDNIGHT_GPU_PROVER_CONFIG` or by the
//! `--config` flag of the binaries.

use std::{
    env,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

use crate::Error;

/// Prefix of every environment variable of this crate.
pub const ENV_PREFIX: &str = "MIDNIGHT_GPU_PROVER_";

/// What the service does with the resident proving-key copies on the device
/// between requests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "kebab-case")]
pub enum ResidentPolicy {
    /// Free the proving-key copies and the MSM base tables before each reply
    /// and upload them again in the next request. Between requests the
    /// service holds no key data on the device. The default.
    #[default]
    Evict,
    /// Keep the copies and the tables between requests. For a device with no
    /// other user.
    /// Refused under the WSL2 profile.
    Keep,
}

/// What a fallback from the device to the CPU means for a request.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "kebab-case")]
pub enum RunMode {
    /// A fallback is served: the proof is returned and marked degraded with the
    /// phase and the reason. The default.
    #[default]
    Production,
    /// Bench and acceptance runs: any fallback or degraded admission fails the
    /// request, and no proof is written.
    Acceptance,
}

/// Whether the service uses a device.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "kebab-case")]
pub enum DeviceSelect {
    /// Use a device when the build has device support and the run-time
    /// detection finds one (`CUDA_VISIBLE_DEVICES` is respected by the CUDA
    /// runtime). The default.
    #[default]
    Auto,
    /// Prove on the CPU only.
    Off,
}

/// Whether the WSL2 profile applies.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "kebab-case")]
pub enum WslSelect {
    /// Detect WSL2 at start: `/dev/dxg` exists or `/proc/version` names
    /// Microsoft. The default.
    #[default]
    Auto,
    /// Apply the WSL2 profile.
    On,
    /// Do not apply the WSL2 profile.
    Off,
}

/// Configuration of a [`crate::ProverService`] and of the daemon.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct Config {
    /// Largest circuit size (log2 of the row count) the service accepts. A
    /// circuit above it is refused at start. Env `MIDNIGHT_GPU_PROVER_MAX_K`,
    /// default 25.
    pub max_k: u32,
    /// Expected SHA-256 of the verifying key (`VerifyingKey::write` with
    /// `SerdeFormat::RawBytes`), lower-case hex. When set, the service refuses
    /// to start on a mismatch. Env `MIDNIGHT_GPU_PROVER_VK_SHA256`, default
    /// unset.
    pub vk_sha256: Option<String>,
    /// Device selection. Env `MIDNIGHT_GPU_PROVER_DEVICE` (`auto` or `off`),
    /// default `auto`.
    pub device: DeviceSelect,
    /// Rayon threads of the prover. 0 means one per available CPU. Env
    /// `MIDNIGHT_GPU_PROVER_THREADS`, default 0.
    pub threads: usize,
    /// Resident policy. Env `MIDNIGHT_GPU_PROVER_RESIDENT` (`evict` or
    /// `keep`), default `evict`.
    pub resident: ResidentPolicy,
    /// Longest wait for another device user to free memory, in seconds (step
    /// `wait` of the admission ladder). Env `MIDNIGHT_GPU_PROVER_WAIT_S`,
    /// default 20.
    pub wait_s: f64,
    /// Reserve added to the computed device memory need, MiB. Env
    /// `MIDNIGHT_GPU_PROVER_MARGIN_MIB`, default 768.
    pub margin_mib: u64,
    /// Bound on the device peak of one request, MiB; 0 means none. A request
    /// above it is answered, then the daemon retires (exit 3) so that its
    /// supervisor starts a fresh process.
    pub max_device_peak_mib: u64,
    /// Bound on the host high-water mark of the process after a request,
    /// MiB; 0 means none. Handled as `max_device_peak_mib`.
    pub max_host_hwm_mib: u64,
    /// Lock file of the device. When set, a request may use the device only
    /// while its caller holds an exclusive `flock` on this file and passes
    /// the locked file descriptor with the request. The service never takes
    /// the lock itself. Env `MIDNIGHT_GPU_PROVER_LOCK`, default unset.
    pub lock_path: Option<PathBuf>,
    /// WSL2 profile. Env `MIDNIGHT_GPU_PROVER_WSL` (`auto`, `on`, `off`),
    /// default `auto`.
    pub wsl: WslSelect,
    /// Part of the device the WSL2 budget leaves out, MiB: the budget is the
    /// device total minus this reserve. Env
    /// `MIDNIGHT_GPU_PROVER_WSL_RESERVE_MIB`, default 4096.
    pub wsl_reserve_mib: u64,
    /// Run mode. Env `MIDNIGHT_GPU_PROVER_MODE` (`production` or
    /// `acceptance`), default `production`.
    pub mode: RunMode,
    /// Read every wiped device region back and compare it with zero before it
    /// is freed (slower). A request can ask for it too. Env
    /// `MIDNIGHT_GPU_PROVER_ZERO_CHECK` (`0` or `1`), default off.
    pub zero_check: bool,
    /// SRS file (`ParamsKZG::write_custom` with
    /// `SerdeFormat::RawBytesUnchecked`, the format of the Midnight and
    /// Filecoin SRS files). Used by the
    /// binaries. Env `MIDNIGHT_GPU_PROVER_SRS`, default unset.
    pub srs_path: Option<PathBuf>,
    /// Unix socket of the daemon. Env `MIDNIGHT_GPU_PROVER_SOCKET`, default
    /// `$XDG_RUNTIME_DIR/midnight-gpu-prover.sock`, or
    /// `/tmp/midnight-gpu-prover-$UID.sock` when `XDG_RUNTIME_DIR` is unset.
    pub socket: Option<PathBuf>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_k: 25,
            vk_sha256: None,
            device: DeviceSelect::Auto,
            threads: 0,
            resident: ResidentPolicy::Evict,
            wait_s: 20.0,
            margin_mib: 768,
            max_device_peak_mib: 0,
            max_host_hwm_mib: 0,
            lock_path: None,
            wsl: WslSelect::Auto,
            wsl_reserve_mib: 4096,
            mode: RunMode::Production,
            zero_check: false,
            srs_path: None,
            socket: None,
        }
    }
}

/// Configuration of a [`crate::client::Client`].
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct ClientConfig {
    /// Socket of the daemon. Env `MIDNIGHT_GPU_PROVER_SOCKET`, default as
    /// [`Config::socket`].
    pub socket: Option<PathBuf>,
    /// Prove on the CPU in-process when the daemon cannot serve the request.
    /// Env `MIDNIGHT_GPU_PROVER_CPU_FALLBACK` (`0` or `1`), default on.
    pub cpu_fallback: bool,
    /// Longest time to wait for a reply, seconds. Env
    /// `MIDNIGHT_GPU_PROVER_REPLY_TIMEOUT_S`, default 3600.
    pub reply_timeout_s: u64,
    /// Consecutive daemon failures that open the circuit breaker. Env
    /// `MIDNIGHT_GPU_PROVER_BREAKER_FAILURES`, default 3.
    pub breaker_failures: u32,
    /// Window in which those failures must fall, seconds. Env
    /// `MIDNIGHT_GPU_PROVER_BREAKER_WINDOW_S`, default 600.
    pub breaker_window_s: u64,
    /// Time the open breaker skips the daemon, seconds. Env
    /// `MIDNIGHT_GPU_PROVER_BREAKER_COOLDOWN_S`, default 600.
    pub breaker_cooldown_s: u64,
    /// State file of the breaker (created owner-only). Env
    /// `MIDNIGHT_GPU_PROVER_BREAKER_STATE`, default the socket path with the
    /// suffix `.breaker`.
    pub breaker_state: Option<PathBuf>,
    /// Program run once when the breaker opens, with the alert line as its
    /// only argument. Env `MIDNIGHT_GPU_PROVER_ALERT_CMD`, default unset (the
    /// alert goes to stderr only).
    pub alert_cmd: Option<PathBuf>,
}

impl Default for ClientConfig {
    fn default() -> Self {
        ClientConfig {
            socket: None,
            cpu_fallback: true,
            reply_timeout_s: 3600,
            breaker_failures: 3,
            breaker_window_s: 600,
            breaker_cooldown_s: 600,
            breaker_state: None,
            alert_cmd: None,
        }
    }
}

/// The default socket path: `$XDG_RUNTIME_DIR/midnight-gpu-prover.sock`, or
/// `/tmp/midnight-gpu-prover-$UID.sock`.
pub fn default_socket() -> PathBuf {
    match env::var_os("XDG_RUNTIME_DIR").filter(|v| !v.is_empty()) {
        Some(d) => PathBuf::from(d).join("midnight-gpu-prover.sock"),
        None => {
            // SAFETY: `geteuid` has no preconditions.
            let uid = unsafe { libc::geteuid() };
            PathBuf::from(format!("/tmp/midnight-gpu-prover-{uid}.sock"))
        }
    }
}

/// A source of environment values (the process environment, or a map in
/// tests).
pub type EnvFn<'a> = &'a dyn Fn(&str) -> Option<String>;

/// Reads the process environment.
pub fn process_env(name: &str) -> Option<String> {
    env::var(name).ok().filter(|v| !v.is_empty())
}

fn parse<T: std::str::FromStr>(name: &str, v: &str) -> Result<T, Error> {
    v.trim()
        .parse()
        .map_err(|_| Error::Config(format!("{ENV_PREFIX}{name}: not a valid value")))
}

fn parse_bool(name: &str, v: &str) -> Result<bool, Error> {
    match v.trim() {
        "1" | "true" | "on" => Ok(true),
        "0" | "false" | "off" => Ok(false),
        _ => Err(Error::Config(format!("{ENV_PREFIX}{name}: 0 or 1"))),
    }
}

fn parse_enum<T: for<'de> Deserialize<'de>>(name: &str, v: &str) -> Result<T, Error> {
    serde_json::from_value(serde_json::Value::String(v.trim().to_string()))
        .map_err(|_| Error::Config(format!("{ENV_PREFIX}{name}: not a valid value")))
}

/// A JSON error as its category and position: serde's message quotes the
/// input (a value, an unknown field name), which never goes into an error.
pub fn json_error(e: &serde_json::Error) -> String {
    use serde_json::error::Category;
    let what = match e.classify() {
        Category::Io => "cannot be read",
        Category::Syntax => "is not valid JSON",
        Category::Data => "has a field of the wrong name, type or value",
        Category::Eof => "ends early",
    };
    format!("{what} (line {}, column {})", e.line(), e.column())
}

fn read_file<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, Error> {
    // the path is not repeated: a client names its config file in its
    // own environment
    let text = std::fs::read_to_string(path)
        .map_err(|e| Error::Config(format!("the config file cannot be read: {}", e.kind())))?;
    serde_json::from_str(&text)
        .map_err(|e| Error::Config(format!("the config file {}", json_error(&e))))
}

impl Config {
    /// The configuration from the defaults, the config file named by
    /// `MIDNIGHT_GPU_PROVER_CONFIG` (or `file`, which wins) and the process
    /// environment.
    pub fn load(file: Option<&Path>) -> Result<Config, Error> {
        Config::load_with(file, &process_env)
    }

    /// As [`Config::load`] with an explicit environment source.
    pub fn load_with(file: Option<&Path>, env: EnvFn) -> Result<Config, Error> {
        let from_env = env(&format!("{ENV_PREFIX}CONFIG")).map(PathBuf::from);
        let mut c = match file.map(Path::to_path_buf).or(from_env) {
            Some(p) => read_file(&p)?,
            None => Config::default(),
        };
        c.apply_env(env)?;
        c.validate()?;
        Ok(c)
    }

    fn apply_env(&mut self, env: EnvFn) -> Result<(), Error> {
        let get = |n: &str| env(&format!("{ENV_PREFIX}{n}"));
        if let Some(v) = get("MAX_K") {
            self.max_k = parse("MAX_K", &v)?;
        }
        if let Some(v) = get("VK_SHA256") {
            self.vk_sha256 = Some(v.trim().to_ascii_lowercase());
        }
        if let Some(v) = get("DEVICE") {
            self.device = parse_enum("DEVICE", &v)?;
        }
        if let Some(v) = get("THREADS") {
            self.threads = parse("THREADS", &v)?;
        }
        if let Some(v) = get("RESIDENT") {
            self.resident = parse_enum("RESIDENT", &v)?;
        }
        if let Some(v) = get("WAIT_S") {
            self.wait_s = parse("WAIT_S", &v)?;
        }
        if let Some(v) = get("MARGIN_MIB") {
            self.margin_mib = parse("MARGIN_MIB", &v)?;
        }
        if let Some(v) = get("MAX_DEVICE_PEAK_MIB") {
            self.max_device_peak_mib = parse("MAX_DEVICE_PEAK_MIB", &v)?;
        }
        if let Some(v) = get("MAX_HOST_HWM_MIB") {
            self.max_host_hwm_mib = parse("MAX_HOST_HWM_MIB", &v)?;
        }
        if let Some(v) = get("LOCK") {
            self.lock_path = Some(PathBuf::from(v));
        }
        if let Some(v) = get("WSL") {
            self.wsl = parse_enum("WSL", &v)?;
        }
        if let Some(v) = get("WSL_RESERVE_MIB") {
            self.wsl_reserve_mib = parse("WSL_RESERVE_MIB", &v)?;
        }
        if let Some(v) = get("MODE") {
            self.mode = parse_enum("MODE", &v)?;
        }
        if let Some(v) = get("ZERO_CHECK") {
            self.zero_check = parse_bool("ZERO_CHECK", &v)?;
        }
        if let Some(v) = get("SRS") {
            self.srs_path = Some(PathBuf::from(v));
        }
        if let Some(v) = get("SOCKET") {
            self.socket = Some(PathBuf::from(v));
        }
        Ok(())
    }

    /// Checks the values that do not depend on the circuit or the device.
    pub fn validate(&self) -> Result<(), Error> {
        if self.max_k == 0 || self.max_k > 32 {
            return Err(Error::Config(format!("max_k = {}: 1 to 32", self.max_k)));
        }
        if !(self.wait_s.is_finite() && self.wait_s >= 0.0) {
            return Err(Error::Config(format!(
                "wait_s = {}: a non-negative number",
                self.wait_s
            )));
        }
        if let Some(h) = &self.vk_sha256
            && (h.len() != 64 || !h.bytes().all(|b| b.is_ascii_hexdigit()))
        {
            return Err(Error::Config("vk_sha256: 64 hex digits".into()));
        }
        Ok(())
    }

    /// The socket path: [`Config::socket`] or [`default_socket`].
    pub fn socket_path(&self) -> PathBuf {
        self.socket.clone().unwrap_or_else(default_socket)
    }

    /// The rayon thread count the prover uses.
    pub fn thread_count(&self) -> usize {
        if self.threads > 0 {
            self.threads
        } else {
            std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
        }
    }

    /// Whether the WSL2 profile applies, from the setting and the run-time
    /// detection.
    pub fn wsl_active(&self) -> bool {
        match self.wsl {
            WslSelect::On => true,
            WslSelect::Off => false,
            WslSelect::Auto => is_wsl(
                Path::new("/dev/dxg").exists(),
                &std::fs::read_to_string("/proc/version").unwrap_or_default(),
            ),
        }
    }
}

/// WSL2 detection: `/dev/dxg` exists, or the kernel version string names
/// Microsoft.
pub fn is_wsl(dev_dxg: bool, proc_version: &str) -> bool {
    dev_dxg || proc_version.to_ascii_lowercase().contains("microsoft")
}

impl ClientConfig {
    /// The configuration from the defaults, the config file named by
    /// `MIDNIGHT_GPU_PROVER_CLIENT_CONFIG` (or `file`, which wins) and the
    /// process environment.
    pub fn load(file: Option<&Path>) -> Result<ClientConfig, Error> {
        ClientConfig::load_with(file, &process_env)
    }

    /// As [`ClientConfig::load`] with an explicit environment source.
    pub fn load_with(file: Option<&Path>, env: EnvFn) -> Result<ClientConfig, Error> {
        let from_env = env(&format!("{ENV_PREFIX}CLIENT_CONFIG")).map(PathBuf::from);
        let mut c = match file.map(Path::to_path_buf).or(from_env) {
            Some(p) => read_file(&p)?,
            None => ClientConfig::default(),
        };
        let get = |n: &str| env(&format!("{ENV_PREFIX}{n}"));
        if let Some(v) = get("SOCKET") {
            c.socket = Some(PathBuf::from(v));
        }
        if let Some(v) = get("CPU_FALLBACK") {
            c.cpu_fallback = parse_bool("CPU_FALLBACK", &v)?;
        }
        if let Some(v) = get("REPLY_TIMEOUT_S") {
            c.reply_timeout_s = parse("REPLY_TIMEOUT_S", &v)?;
        }
        if let Some(v) = get("BREAKER_FAILURES") {
            c.breaker_failures = parse("BREAKER_FAILURES", &v)?;
        }
        if let Some(v) = get("BREAKER_WINDOW_S") {
            c.breaker_window_s = parse("BREAKER_WINDOW_S", &v)?;
        }
        if let Some(v) = get("BREAKER_COOLDOWN_S") {
            c.breaker_cooldown_s = parse("BREAKER_COOLDOWN_S", &v)?;
        }
        if let Some(v) = get("BREAKER_STATE") {
            c.breaker_state = Some(PathBuf::from(v));
        }
        if let Some(v) = get("ALERT_CMD") {
            c.alert_cmd = Some(PathBuf::from(v));
        }
        if c.breaker_failures == 0 {
            return Err(Error::Config("breaker_failures: at least 1".into()));
        }
        Ok(c)
    }

    /// The socket path: [`ClientConfig::socket`] or [`default_socket`].
    pub fn socket_path(&self) -> PathBuf {
        self.socket.clone().unwrap_or_else(default_socket)
    }

    /// The breaker state path: [`ClientConfig::breaker_state`] or the socket
    /// path with the suffix `.breaker`.
    pub fn breaker_path(&self) -> PathBuf {
        self.breaker_state.clone().unwrap_or_else(|| {
            let mut s = self.socket_path().into_os_string();
            s.push(".breaker");
            PathBuf::from(s)
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    fn env_of(pairs: &[(&str, &str)]) -> impl Fn(&str) -> Option<String> {
        let m: HashMap<String, String> =
            pairs.iter().map(|(k, v)| (format!("{ENV_PREFIX}{k}"), v.to_string())).collect();
        move |k| m.get(k).cloned()
    }

    #[test]
    fn defaults() {
        let c = Config::load_with(None, &env_of(&[])).unwrap();
        assert_eq!(c, Config::default());
        assert_eq!(c.max_k, 25);
        assert_eq!(c.resident, ResidentPolicy::Evict);
        assert_eq!(c.wait_s, 20.0);
        assert_eq!(c.margin_mib, 768);
        assert_eq!(c.wsl_reserve_mib, 4096);
        assert_eq!(c.mode, RunMode::Production);
        let cc = ClientConfig::load_with(None, &env_of(&[])).unwrap();
        assert_eq!(
            (
                cc.breaker_failures,
                cc.breaker_window_s,
                cc.breaker_cooldown_s
            ),
            (3, 600, 600)
        );
        assert!(cc.cpu_fallback);
    }

    #[test]
    fn env_overrides_file() {
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("c.json");
        std::fs::write(
            &f,
            r#"{"max_k": 20, "resident": "keep", "mode": "acceptance"}"#,
        )
        .unwrap();
        let c = Config::load_with(Some(&f), &env_of(&[("MAX_K", "22")])).unwrap();
        assert_eq!(c.max_k, 22);
        assert_eq!(c.resident, ResidentPolicy::Keep);
        assert_eq!(c.mode, RunMode::Acceptance);
    }

    #[test]
    fn bad_values_are_refused() {
        assert!(Config::load_with(None, &env_of(&[("RESIDENT", "sometimes")])).is_err());
        assert!(Config::load_with(None, &env_of(&[("MAX_K", "x")])).is_err());
        assert!(Config::load_with(None, &env_of(&[("MAX_K", "40")])).is_err());
        assert!(Config::load_with(None, &env_of(&[("VK_SHA256", "abc")])).is_err());
        assert!(Config::load_with(None, &env_of(&[("ZERO_CHECK", "yes")])).is_err());
        assert!(ClientConfig::load_with(None, &env_of(&[("BREAKER_FAILURES", "0")])).is_err());
        let dir = tempfile::tempdir().unwrap();
        let f = dir.path().join("c.json");
        std::fs::write(&f, r#"{"no_such_key": 1}"#).unwrap();
        assert!(Config::load_with(Some(&f), &env_of(&[])).is_err());
    }

    #[test]
    fn wsl_detection() {
        assert!(is_wsl(true, ""));
        assert!(is_wsl(
            false,
            "Linux version 6.6.87.2-microsoft-standard-WSL2"
        ));
        assert!(!is_wsl(false, "Linux version 6.12.0-generic"));
        let c = Config {
            wsl: WslSelect::On,
            ..Config::default()
        };
        assert!(c.wsl_active());
        let c = Config {
            wsl: WslSelect::Off,
            ..Config::default()
        };
        assert!(!c.wsl_active());
    }

    #[test]
    fn breaker_path_follows_socket() {
        let c = ClientConfig {
            socket: Some("/run/x/p.sock".into()),
            ..ClientConfig::default()
        };
        assert_eq!(c.breaker_path(), PathBuf::from("/run/x/p.sock.breaker"));
    }
}
