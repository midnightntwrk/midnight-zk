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

//! Build of the CUDA core.
//!
//! With the feature `cuda` and `nvcc` found, `cuda/midnight_gpu.cu` (the
//! sppark templates of `third_party/sppark`, the blst headers of the `blst`
//! crate) is compiled into a static library, cudart is linked and the cfg
//! `midnight_gpu_cuda` is set. Otherwise the crate is a stub whose device
//! calls all decline.
//!
//! Environment:
//! - `CUDA_PATH`, else `CUDA_HOME`, else the toolkit of `nvcc` on `PATH`: the
//!   CUDA toolkit.
//! - `MIDNIGHT_GPU_ARCHS`: a comma list of SM numbers (`80,86,120`), each
//!   compiled to SASS, plus PTX of the highest; `native` compiles for the
//!   devices of the build machine. An explicit SM number that this `nvcc` does
//!   not support fails the build. Default: [`DEFAULT_ARCHS`], keeping those
//!   this `nvcc` supports, with a warning for each one left out.
//! - `MIDNIGHT_GPU_REQUIRE_CUDA=1`: a missing `nvcc` or a failed compile is a
//!   build error instead of a warning and a stub.
//! - `MIDNIGHT_GPU_LINEINFO=1`: include CUDA source locations for sanitizer
//!   runs.
use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

/// The default SASS targets: Ampere (A100, RTX 30), Ada (RTX 40), Hopper,
/// Blackwell data center and Blackwell (RTX 50, GB10). PTX of the highest
/// one is embedded too, so a newer device can compile it at load time.
const DEFAULT_ARCHS: [&str; 6] = ["80", "86", "89", "90", "100", "120"];

fn main() {
    println!("cargo:rerun-if-changed=cuda");
    println!("cargo:rerun-if-changed=third_party/sppark");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(midnight_gpu_cuda)");
    for v in [
        "CUDA_PATH",
        "CUDA_HOME",
        "PATH",
        "MIDNIGHT_GPU_ARCHS",
        "MIDNIGHT_GPU_REQUIRE_CUDA",
        "MIDNIGHT_GPU_LINEINFO",
    ] {
        println!("cargo:rerun-if-env-changed={v}");
    }
    if env::var_os("CARGO_FEATURE_CUDA").is_none() {
        return;
    }
    let require = env::var("MIDNIGHT_GPU_REQUIRE_CUDA").as_deref() == Ok("1");
    let stub = |why: String| {
        if require {
            panic!("midnight-gpu: {why} (MIDNIGHT_GPU_REQUIRE_CUDA=1)");
        }
        println!(
            "cargo:warning=midnight-gpu: {why}; building the stub that declines every device call"
        );
    };
    let Some(cuda) = cuda_root() else {
        return stub("nvcc not found (set CUDA_PATH or CUDA_HOME, or put nvcc on PATH)".into());
    };
    let nvcc = cuda.join("bin").join("nvcc");
    let gencode = match gencode(&nvcc) {
        Ok(g) => g,
        Err(e) => return stub(e),
    };
    let Ok(blst_src) = env::var("DEP_BLST_C_SRC") else {
        return stub("DEP_BLST_C_SRC is not set by the blst crate".into());
    };
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());

    // blst on x86_64 exports only its mulx entry points when it builds with
    // ADX; its headers remap the names under __ADX__. Define it for nvcc as
    // blst decides, or the host code links against missing symbols.
    let mut adx = Vec::new();
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("x86_64") {
        let tf = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
        #[cfg(target_arch = "x86_64")]
        let host_adx = std::is_x86_feature_detected!("adx");
        #[cfg(not(target_arch = "x86_64"))]
        let host_adx = false;
        if tf.split(',').any(|f| f == "adx") || host_adx {
            adx.push("-D__ADX__");
        }
    }

    let obj = out.join("midnight_gpu.o");
    let mut compile = Command::new(&nvcc);
    if env::var("MIDNIGHT_GPU_LINEINFO").as_deref() == Ok("1") {
        compile.arg("-lineinfo");
    }
    let status = compile
        .args(&adx)
        .args([
            "-O3",
            "-std=c++17",
            "-Xcompiler",
            "-fPIC",
            "-Xcompiler",
            "-Wno-unused-function",
        ])
        .args([
            "-DFEATURE_BLS12_381",
            "-DTAKE_RESPONSIBILITY_FOR_ERROR_MESSAGE",
        ])
        // the test switches of the core exist only in a `test-fault` build
        .args(env::var_os("CARGO_FEATURE_TEST_FAULT").map(|_| "-DMGPU_TEST_FAULT"))
        .args(&gencode)
        .arg(format!(
            "-I{}",
            manifest.join("third_party/sppark").display()
        ))
        .arg(format!("-I{blst_src}"))
        .arg("-c")
        .arg(manifest.join("cuda/midnight_gpu.cu"))
        .arg("-o")
        .arg(&obj)
        .status();
    if !status.as_ref().is_ok_and(|s| s.success()) {
        return stub(format!("nvcc failed ({status:?})"));
    }
    let lib = out.join("libmidnight_gpu_cuda.a");
    let _ = std::fs::remove_file(&lib);
    if !Command::new("ar")
        .arg("crs")
        .arg(&lib)
        .arg(&obj)
        .status()
        .is_ok_and(|s| s.success())
    {
        return stub("ar failed".into());
    }
    println!("cargo:rustc-cfg=midnight_gpu_cuda");
    let gencode = gencode.join(" ");
    println!("cargo:rustc-env=MIDNIGHT_GPU_BUILD_ARCHS={gencode}");
    println!("cargo:rustc-link-search=native={}", out.display());
    for dir in [cuda.join("lib64"), cuda.join("lib"), cuda_target_lib(&cuda)] {
        if dir.exists() {
            println!("cargo:rustc-link-search=native={}", dir.display());
            println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir.display());
        }
    }
    println!("cargo:rustc-link-lib=static=midnight_gpu_cuda");
    println!("cargo:rustc-link-lib=dylib=cudart");
    println!("cargo:rustc-link-lib=dylib=stdc++");
}

/// The CUDA toolkit: `CUDA_PATH`, `CUDA_HOME`, else the toolkit of `nvcc` on
/// `PATH`. `None` when none of them has `bin/nvcc`.
fn cuda_root() -> Option<PathBuf> {
    let has_nvcc = |p: &Path| p.join("bin").join("nvcc").is_file();
    for v in ["CUDA_PATH", "CUDA_HOME"] {
        if let Some(p) = env::var_os(v).map(PathBuf::from)
            && has_nvcc(&p)
        {
            return Some(p);
        }
    }
    env::split_paths(&env::var_os("PATH")?)
        .map(|d| d.join("nvcc"))
        .find(|p| p.is_file())
        .and_then(|p| p.canonicalize().ok())
        .and_then(|p| Some(p.parent()?.parent()?.to_path_buf()))
        .filter(|p| has_nvcc(p))
}

/// The `-gencode` arguments (see the module text).
fn gencode(nvcc: &Path) -> Result<Vec<String>, String> {
    let list = env::var("MIDNIGHT_GPU_ARCHS").unwrap_or_default();
    if list.trim() == "native" {
        return Ok(vec!["-arch=native".into()]);
    }
    let supported: Vec<String> = Command::new(nvcc)
        .arg("--list-gpu-arch")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .filter_map(|l| l.trim().strip_prefix("compute_").map(str::to_string))
                .collect()
        })
        .ok_or_else(|| format!("{} --list-gpu-arch failed", nvcc.display()))?;
    let explicit = !list.trim().is_empty();
    let wanted: Vec<String> = if !explicit {
        DEFAULT_ARCHS.iter().map(|a| a.to_string()).collect()
    } else {
        let v: Vec<String> = list
            .split(',')
            .map(|a| a.trim().trim_start_matches("sm_").to_string())
            .filter(|a| !a.is_empty())
            .collect();
        if v.is_empty() || !v.iter().all(|a| a.bytes().all(|b| b.is_ascii_digit())) {
            panic!("MIDNIGHT_GPU_ARCHS={list:?}: need `native` or SM numbers, e.g. 80,86,120");
        }
        v
    };
    let mut archs: Vec<String> = Vec::new();
    for a in wanted {
        if !supported.contains(&a) {
            // an architecture the builder asked for is never dropped
            if explicit {
                panic!(
                    "midnight-gpu: MIDNIGHT_GPU_ARCHS asks for sm_{a}, which {} does not support",
                    nvcc.display()
                );
            }
            println!(
                "cargo:warning=midnight-gpu: this nvcc does not support the default sm_{a}; \
                 it is left out of the build"
            );
        } else if !archs.contains(&a) {
            archs.push(a);
        }
    }
    let top = archs
        .iter()
        .max_by_key(|a| a.parse::<u32>().unwrap_or(0))
        .ok_or("no requested GPU architecture is supported by this nvcc")?
        .clone();
    let mut g = Vec::new();
    for a in &archs {
        g.push("-gencode".to_string());
        g.push(format!("arch=compute_{a},code=sm_{a}"));
    }
    g.push("-gencode".to_string());
    g.push(format!("arch=compute_{top},code=compute_{top}"));
    Ok(g)
}

/// CUDA's per-target library directory for the target being built.
fn cuda_target_lib(cuda: &Path) -> PathBuf {
    let t = match env::var("CARGO_CFG_TARGET_ARCH").as_deref() {
        Ok("aarch64") => "sbsa-linux",
        _ => "x86_64-linux",
    };
    cuda.join("targets").join(t).join("lib")
}
