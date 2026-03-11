use std::ffi::c_void;

extern "C" {
    pub fn vroom_ctx_new() -> *mut c_void;
    pub fn vroom_ctx_free(ctx: *mut c_void);
    pub fn vroom_generate_points(ctx: *mut c_void, npoints: usize, seed: u64) -> *mut c_void;
    pub fn vroom_free_points(points: *mut c_void);
    pub fn vroom_generate_scalars(npoints: usize, seed: u64) -> *mut c_void;
    pub fn vroom_free_scalars(scalars: *mut c_void);
    pub fn vroom_g1_msm(
        ctx: *mut c_void,
        points: *const c_void,
        scalars: *const c_void,
        npoints: usize,
    ) -> u64;
    pub fn vroom_g1_msm_parallel(
        ctx: *mut c_void,
        points: *const c_void,
        scalars: *const c_void,
        npoints: usize,
        num_threads: usize,
    ) -> u64;
}
