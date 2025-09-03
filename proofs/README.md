# midnight_proofs

Implementation of Plonk proof system with KZG commitments. This repo initially started 
as a fork of [`halo2`](https://github.com/privacy-scaling-explorations/halo2) v0.3.0 – 
by the Privacy Scaling Explorations (PSE) team, itself originally derived from the 
[Zcash Sapling proving system](https://github.com/zcash/halo2). 

## Minimum Supported Rust Version

Requires Rust **1.65.0** or higher.

Minimum supported Rust version can be changed in the future, but it will be done with a
minor version bump.

## Controlling parallelism

`midnight_proofs` currently uses [rayon](https://github.com/rayon-rs/rayon) for parallel
computation. The `RAYON_NUM_THREADS` environment variable can be used to set the number of
threads.

When compiling to WASM-targets, notice that since version `1.7`, `rayon` will fallback automatically (with no need to handle features) to require `getrandom` in order to be able to work. For more info related to WASM-compilation.

See: [Rayon: Usage with WebAssembly](https://github.com/rayon-rs/rayon#usage-with-webassembly) for more 

## License

See root directory for Licensing. We have copied the license files of the original [Zcash Sapling proving system](https://github.com/zcash/halo2).

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
