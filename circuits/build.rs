use std::{env, fs, path::Path};

fn main() {
    let val: usize = env::var("T")
        .unwrap_or_else(|_| "10".to_string())
        .parse()
        .expect("T must be a valid usize");

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest = Path::new(&out_dir).join("consts.rs");

    fs::write(&dest, format!("pub const T: usize = {};", val)).unwrap();
    println!("cargo:rerun-if-env-changed=T");
}
