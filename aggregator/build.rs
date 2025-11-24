fn main() {
    #[cfg(feature = "truncated-challenges")]
    {
        println!("cargo:warning=┌─────────────────────────────────────────────────────────────┐");
        println!("cargo:warning=│  Aggregator does not support 'truncated-challenges'         │");
        println!("cargo:warning=│  Skipping compilation of aggregator modules                 │");
        println!("cargo:warning=└─────────────────────────────────────────────────────────────┘");
    }
}
