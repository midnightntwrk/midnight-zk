mod cache;
mod circuit;
mod metrics;

use std::{
    env,
    io::{self, Write},
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use circuit::Chain;
#[cfg(not(rc1_device))]
use metrics::Metrics;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    plonk::{ProvingKey, VerifyingKey, create_proof, prepare},
    poly::{
        commitment::Guard,
        kzg::{KZGCommitmentScheme, params::ParamsVerifierKZG},
    },
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use serde::{Deserialize, Serialize};

type Scheme = KZGCommitmentScheme<Bls12>;
type Key = ProvingKey<Fq, Scheme>;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
type Blake = CircuitTranscript<blake2b_simd::State>;
const HEADER: &str = "mode\trep\tk\tthreads\tstart_load1\tproof\tstate\tprove_s\tverify_s\tverified\tmsm_calls\tntt_calls\tquotient_calls\tdevice_errors\tfallbacks\tdeclines\thook_declines\th2d_copies\th2d_bytes\td2h_copies\td2h_bytes\tmsm_d2h_copies\tmsm_d2h_bytes\tstage\tpeak_device_bytes\tgpu_model\tdevice_total_bytes";

fn number(name: &str, default: u32) -> Result<u32> {
    match env::var(name) {
        Ok(s) => Ok(s.parse()?),
        Err(env::VarError::NotPresent) => Ok(default),
        Err(e) => Err(e.into()),
    }
}

/// The one-minute load average, from `/proc/loadavg`.
#[cfg(target_os = "linux")]
fn one_minute_load() -> Result<f64> {
    let line = std::fs::read_to_string("/proc/loadavg")?;
    Ok(line.split_whitespace().next().ok_or("missing load average")?.parse::<f64>()?)
}

/// The one-minute load average, from `getloadavg` (no `/proc` on macOS).
#[cfg(not(target_os = "linux"))]
fn one_minute_load() -> Result<f64> {
    let mut avg = [0f64; 1];
    // SAFETY: `avg` has room for the one sample requested.
    if unsafe { libc::getloadavg(avg.as_mut_ptr(), 1) } != 1 {
        return Err("the load average is unavailable".into());
    }
    Ok(avg[0])
}

// Setup and key deserialization can raise load. Sample after both, adjacent to
// proof 0.
/// Waits for a one-minute load below `RC1_MAX_LOAD` (default 2).
fn await_quiet() -> Result<f64> {
    let max = match env::var("RC1_MAX_LOAD") {
        Ok(v) => v.parse::<f64>().map_err(|_| "RC1_MAX_LOAD must be a number")?,
        Err(_) => 2.0,
    };
    loop {
        let load = one_minute_load()?;
        if load < max {
            return Ok(load);
        }
        thread::sleep(Duration::from_secs(5));
    }
}

#[derive(Serialize, Deserialize)]
struct Batch {
    params: Vec<u8>,
    vk: Vec<u8>,
    proofs: Vec<String>,
}

fn verify(batch: &Batch, chain: &Chain) -> Result<Vec<f64>> {
    let params = ParamsVerifierKZG::read(&mut &batch.params[..], SerdeFormat::Processed)?;
    let vk =
        VerifyingKey::<Fq, Scheme>::from_bytes::<Chain>(&batch.vk, SerdeFormat::Processed, ())?;
    let public = chain.instance();
    let mut times = Vec::new();
    for bytes in &batch.proofs {
        let proof = hex::decode(bytes)?;
        let start = Instant::now();
        let mut transcript = Blake::init_from_bytes(&proof);
        prepare::<Fq, Scheme, _>(&vk, &[], &[&public], &mut transcript)?
            .verify(&params)
            .map_err(|e| format!("stock verification failed: {e:?}"))?;
        times.push(start.elapsed().as_secs_f64());
    }
    Ok(times)
}

fn stock_verify(batch: &Batch) -> Result<Vec<f64>> {
    #[cfg(rc1_device)]
    let verifier = env::var_os("RC1_STOCK_BIN").ok_or("set RC1_STOCK_BIN")?;
    #[cfg(not(rc1_device))]
    let verifier = env::current_exe()?;
    let mut child = Command::new(verifier)
        .arg("verify")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    // The stock process reads until EOF and then writes one short list of timings.
    serde_json::to_writer(child.stdin.take().unwrap(), batch)?;
    let output = child.wait_with_output()?;
    if !output.status.success() {
        return Err("stock verifier failed".into());
    }
    let times: Vec<f64> = serde_json::from_slice(&output.stdout)?;
    if times.len() != batch.proofs.len() {
        return Err("stock verifier returned the wrong row count".into());
    }
    Ok(times)
}

fn run(chain: &Chain, smoke: bool) -> Result<()> {
    let warm = number("RC1_WARM", 1)?;
    let rep = number("RC1_REP", 1)?;
    if warm == 0 || !(1..=3).contains(&rep) {
        return Err("need RC1_WARM >= 1 and RC1_REP in 1..=3".into());
    }
    let (params, pk) = cache::load(chain)?;
    let public = chain.instance();
    let threads = rayon::current_num_threads();
    let mut batch = Batch {
        params: Vec::new(),
        vk: pk.get_vk().to_bytes(SerdeFormat::Processed),
        proofs: Vec::new(),
    };
    params.verifier_params().write(&mut batch.params, SerdeFormat::Processed)?;
    #[cfg(rc1_device)]
    let handles = metrics::device::install(&params, &pk)?;
    #[cfg(rc1_device)]
    let (gpu_model, total_bytes) = metrics::device::info()?;
    #[cfg(not(rc1_device))]
    let (gpu_model, total_bytes) = ("NA".to_string(), 0u64);
    let mode = if cfg!(rc1_device) { "gpu" } else { "cpu" };
    let load = if smoke {
        "NA".into()
    } else {
        format!("{:.2}", await_quiet()?)
    };
    let mut rows = Vec::new();
    for _ in 0..=warm {
        #[cfg(rc1_device)]
        let baseline = metrics::device::begin();
        let start = Instant::now();
        let mut transcript = Blake::init();
        let result = create_proof::<Fq, Scheme, _, _>(
            &params,
            &pk,
            chain,
            0,
            &[&public],
            &mut transcript,
            rand::rngs::OsRng,
        );
        let proof = transcript.finalize();
        let prove_s = start.elapsed().as_secs_f64();
        #[cfg(rc1_device)]
        let metrics = metrics::device::finish(baseline)?;
        #[cfg(not(rc1_device))]
        let metrics = Metrics::default();
        result?;
        batch.proofs.push(hex::encode(proof));
        rows.push((prove_s, metrics));
    }
    #[cfg(rc1_device)]
    drop(handles);
    drop(pk);
    drop(params);
    let verified = stock_verify(&batch)?;
    println!("{HEADER}");
    for (index, ((prove_s, m), verify_s)) in rows.into_iter().zip(verified).enumerate() {
        let state = if index == 0 { "cold" } else { "warm" };
        println!(
            "{mode}\t{rep}\t{}\t{threads}\t{load}\t{index}\t{state}\t{prove_s:.9}\t{verify_s:.9}\ttrue\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{gpu_model}\t{total_bytes}",
            chain.k,
            m.msm,
            m.ntt,
            m.quotient,
            m.device_errors,
            m.fallbacks,
            serde_json::to_string(&m.declines)?,
            serde_json::to_string(&m.hook_declines)?,
            m.h2d_copies,
            m.h2d_bytes,
            m.d2h_copies,
            m.d2h_bytes,
            m.msm_d2h_copies,
            m.msm_d2h_bytes,
            serde_json::to_string(&m.stage)?,
            m.peak_bytes
        );
    }
    Ok(())
}

fn main() -> Result<()> {
    let chain = Chain {
        k: number("RC1_K", 21)?,
    };
    if !(5..=21).contains(&chain.k) {
        return Err("supported k is 5..=21".into());
    }
    match env::args().nth(1).as_deref() {
        Some("prepare") if !cfg!(rc1_device) => cache::prepare(&chain),
        Some("verify") if !cfg!(rc1_device) => {
            let batch = serde_json::from_reader(io::stdin().lock())?;
            serde_json::to_writer(io::stdout().lock(), &verify(&batch, &chain)?)?;
            io::stdout().flush()?;
            Ok(())
        }
        Some("run") => run(&chain, false),
        Some("smoke") if !cfg!(rc1_device) && chain.k < 21 => run(&chain, true),
        _ => Err("expected prepare, run, verify, or a small-k CPU smoke".into()),
    }
}
