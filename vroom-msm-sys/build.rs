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

    // --- Compile BLST C code ---
    let mut c_build = cc::Build::new();
    c_build
        .file(blst_dir.join("server_small.c"))
        .flag("-O2")
        .flag("-fPIC")
        .define("__x86_64__", None)
        .define("__ADX__", None)
        .warnings(false);
    // Add BLST include path so nested #includes resolve
    c_build.include(&blst_dir);
    c_build.compile("blst_c");

    // --- Compile BLST assembly ---
    let mut asm_build = cc::Build::new();
    asm_build
        .file(blst_dir.join("assembly_small.S"))
        .define("__x86_64__", None)
        .define("__ADX__", None)
        .warnings(false);
    asm_build.include(&blst_dir);
    asm_build.compile("blst_asm");

    // --- Compile C++ wrapper ---
    let mut cpp_build = cc::Build::new();
    cpp_build
        .cpp(true)
        .file("src/wrapper.cpp")
        .std("c++20")
        .flag("-O3")
        .flag("-mavx512ifma")
        .define("__ADX__", None)
        .define("INLINE", Some("inline"))
        .flag("-Wno-unused-function")
        .flag("-Wno-ignored-attributes")
        .flag("-Wno-sign-conversion");

    for inc in &includes {
        cpp_build.include(inc);
    }
    cpp_build.include(&blst_dir);
    if let Some(ref gmp_inc) = gmp_include {
        cpp_build.include(gmp_inc);
    }

    cpp_build.compile("vroom_wrapper");

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
    println!("cargo:rerun-if-changed=vroom/");
}
