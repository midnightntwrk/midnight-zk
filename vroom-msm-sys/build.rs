use std::path::PathBuf;

fn find_gmp_include() -> Option<PathBuf> {
    for path in &["/opt/homebrew/include", "/usr/local/include", "/usr/include"] {
        let p = PathBuf::from(path);
        if p.join("gmp.h").exists() {
            return Some(p);
        }
    }
    None
}

fn main() {
    let vroom_dir = PathBuf::from("vroom");
    let blst_dir = vroom_dir.join("blst");
    let src_dir = vroom_dir.join("src");
    let cpu_dir = vroom_dir.join("cpu");

    // Common include paths
    let includes: Vec<PathBuf> = vec![
        src_dir.clone(),
        vroom_dir.clone(),
        cpu_dir.join("precompute"),
    ];

    // Find GMP
    let gmp_include = find_gmp_include();

    // NOTE: BLST C code and assembly are NOT compiled here.
    // The `blst` Rust crate (depended on by midnight-curves) already provides
    // these symbols. We only need the BLST headers for type declarations.

    // Use clang++ if available (better SIMD codegen than g++)
    let cxx = if std::process::Command::new("clang++")
        .arg("--version")
        .output()
        .is_ok()
    {
        "clang++"
    } else {
        "c++"
    };

    // Shared compiler settings for both TUs
    let mut base_flags = |build: &mut cc::Build| {
        build
            .compiler(cxx)
            .cpp(true)
            .std("c++20")
            .flag("-O3")
            .flag("-march=native")
            .flag("-mavx512ifma")
            .define("__ADX__", None)
            .flag("-Wno-unused-function")
            .flag("-Wno-ignored-attributes")
            .flag("-Wno-sign-conversion")
            .flag("-Wno-unknown-pragmas");
        for inc in &includes {
            build.include(inc);
        }
        build.include(&blst_dir);
        if let Some(ref gmp_inc) = gmp_include {
            build.include(gmp_inc);
        }
    };

    // --- TU 1: MSM computation (isolated for optimal template optimization) ---
    // CRITICAL: Disable -ffunction-sections/-fdata-sections (cc::Build defaults).
    // These flags scatter template instantiations across ELF sections, causing
    // catastrophic instruction cache fragmentation for VROOM's deeply-nested
    // AVX-512 template code (12x slowdown: 6.7s → 557ms without them).
    let mut msm_build = cc::Build::new();
    base_flags(&mut msm_build);
    msm_build
        .file("src/wrapper_msm.cpp")
        .flag("-fno-function-sections")
        .flag("-fno-data-sections");
    msm_build.compile("vroom_msm");

    // --- TU 2: Context management and data generation ---
    let mut gen_build = cc::Build::new();
    base_flags(&mut gen_build);
    gen_build.file("src/wrapper.cpp");
    gen_build.compile("vroom_gen");

    // Add GMP library search paths
    for path in &["/opt/homebrew/lib", "/usr/local/lib"] {
        if std::path::Path::new(path).exists() {
            println!("cargo:rustc-link-search=native={path}");
        }
    }

    // Link libraries
    println!("cargo:rustc-link-lib=gmp");
    println!("cargo:rustc-link-lib=gmpxx");
    println!("cargo:rustc-link-lib=stdc++");

    // Rerun triggers
    println!("cargo:rerun-if-changed=src/wrapper.cpp");
    println!("cargo:rerun-if-changed=src/wrapper_msm.cpp");
    println!("cargo:rerun-if-changed=src/wrapper_types.hpp");
    println!("cargo:rerun-if-changed=vroom/");
}
