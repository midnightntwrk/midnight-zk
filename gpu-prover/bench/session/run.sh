#!/usr/bin/env bash
# One measurement session on one machine: stock CPU and GPU single proofs by
# circuit size, a sequential run, batch proving, and alternating (ABAB)
# comparisons of accepted changes. It waits for an idle, cool host first and
# records clocks and temperatures through the whole session. Sensors are read
# only; the script never changes clocks, power limits or fan settings.
#
# Usage: gpu-prover/bench/session/run.sh   (configuration from the environment)
#
#   SESSION_OUT   output directory (raw/, RESULTS.md, session.json)   [../session-results]
#   BIN_DIR       directory with rc1-cpu and rc1-gpu of the measured tree (required)
#   RC1_CACHE     key cache shared by every rc1 process   [$SESSION_OUT/key-cache]
#   KS            circuit sizes for single proofs   ["14 15 16 17 18 19 20 21"]
#   WARM          warm proofs per process   [3]
#   THREADS       RAYON_NUM_THREADS for every process   [all cores]
#   SEQ_K, SEQ_N  sequential run: k and warm proofs (SEQ_N=0 skips it)   [16, 64]
#   BATCH_BIN     batch executable, `batch N k` (empty skips batch)
#   BATCH_K       batch circuit size   [16]
#   BATCH_SIZES   batch sizes   ["1 2 4 8"]
#   ABAB_FILE     tab-separated rows: change, what, kind (rc1-gpu|rc1-cpu|lookup), k, warm,
#                 pairs, dir A (without the change), dir B (with it). Empty skips ABAB.
#   IDLE_S        idle time before the first timed proof, seconds   [600]
#   IDLE_LOAD     highest one-minute load counted as idle   [1.0]
#   TEMP_MAX_C    highest CPU package temperature at the start   [60]
#   GATE_MAX_S    give up when the gate has not opened after this long   [3600]
#   GPU_LOCK      optional lock file shared with other device jobs
#   LOCK_SCOPE    session (hold GPU_LOCK from start to end) or run (per process)   [session]
#   RC1_MAX_LOAD  load bound of the rc1 bench's own gate before each cold proof   [2]
#   TREE, BASE    commit labels written to the results
#   DEVICE        device label for the results   [from nvidia-smi]
set -uo pipefail
[[ -f gpu-prover/bench/rc1/main.rs ]] || { echo "run from the repository root" >&2; exit 2; }
: "${BIN_DIR:?set BIN_DIR}"
OUT=${SESSION_OUT:-"$PWD/../session-results"}
export RC1_CACHE=${RC1_CACHE:-"$OUT/key-cache"}
export RAYON_NUM_THREADS=${THREADS:-$(nproc)}
KS=${KS:-"14 15 16 17 18 19 20 21"} WARM=${WARM:-3}
SEQ_K=${SEQ_K:-16} SEQ_N=${SEQ_N:-64}
BATCH_BIN=${BATCH_BIN:-} BATCH_K=${BATCH_K:-16} BATCH_SIZES=${BATCH_SIZES:-"1 2 4 8"}
ABAB_FILE=${ABAB_FILE:-}
IDLE_S=${IDLE_S:-600} IDLE_LOAD=${IDLE_LOAD:-1.0} TEMP_MAX_C=${TEMP_MAX_C:-60} GATE_MAX_S=${GATE_MAX_S:-3600}
RAW=$OUT/raw; mkdir -p "$RAW" "$RC1_CACHE"
LOG=$RAW/session.log
log() { echo "$(date -Is) $*" | tee -a "$LOG"; }
for b in rc1-cpu rc1-gpu; do [[ -x $BIN_DIR/$b ]] || { echo "missing $BIN_DIR/$b" >&2; exit 2; }; done

LOCK_SCOPE=${LOCK_SCOPE:-session}
# lk CMD...: run CMD under GPU_LOCK when the lock is taken per process.
lk() { if [[ -n ${GPU_LOCK:-} && $LOCK_SCOPE == run ]]; then flock "$GPU_LOCK" "$@"; else "$@"; fi; }
if [[ -n ${GPU_LOCK:-} && $LOCK_SCOPE == session ]]; then
    exec 8>"$GPU_LOCK"
    log "waiting for $GPU_LOCK"
    flock 8
fi

# Sensors, read only. CPU package temperature from hwmon (coretemp or k10temp),
# CPU clock as the mean of the per-core current frequencies.
cpu_temp() {
    local h
    for h in /sys/class/hwmon/hwmon*; do
        case $(cat "$h/name" 2>/dev/null) in
            coretemp) for l in "$h"/temp*_label; do
                    [[ $(cat "$l") == Package* ]] && { awk '{printf "%.1f", $1/1000}' "${l%_label}_input"; return; }
                done ;;
            k10temp) awk '{printf "%.1f", $1/1000}' "$h/temp1_input"; return ;;
        esac
    done
    echo NA
}
cpu_mhz() { awk '/^cpu MHz/ {s+=$4; n++} END {if (n) printf "%.0f", s/n; else print "NA"}' /proc/cpuinfo; }
load1() { cut -d' ' -f1 /proc/loadavg; }
gpu_apps() { nvidia-smi --query-compute-apps=pid --format=csv,noheader 2>/dev/null | grep -c .; }

# Whole-session sensor log: one row a second.
sensors_loop() {
    echo -e "time\tphase\tload1\tcpu_temp_c\tcpu_mhz\tgpu_temp_c\tgpu_sm_mhz\tgpu_mem_mhz\tgpu_util\tgpu_power_w"
    while :; do
        local g
        g=$(nvidia-smi --query-gpu=temperature.gpu,clocks.sm,clocks.mem,utilization.gpu,power.draw \
            --format=csv,noheader,nounits 2>/dev/null | head -1 | tr -d ' ' | tr ',' '\t')
        echo -e "$(date +%s.%N)\t$(cat "$RAW/.phase" 2>/dev/null)\t$(load1)\t$(cpu_temp)\t$(cpu_mhz)\t${g:-NA}"
        sleep 1
    done
}
phase() { echo "$1" > "$RAW/.phase"; log "phase $1"; }

# Keys for every size, before the gate: preparation is CPU work.
phase prepare
for k in $(echo "$KS $SEQ_K" | tr ' ' '\n' | sort -nu); do
    RC1_K=$k "$BIN_DIR/rc1-cpu" prepare >> "$RAW/prepare.log" 2>&1 || { log "prepare k=$k failed"; exit 1; }
done

# Gate: IDLE_S seconds with load below IDLE_LOAD and no GPU compute process,
# then the CPU package below TEMP_MAX_C (skipped when the sensor is not readable).
phase gate
start=$(date +%s) idle_since=$start
while :; do
    now=$(date +%s); l=$(load1); t=$(cpu_temp); apps=$(gpu_apps)
    if awk -v l="$l" -v m="$IDLE_LOAD" 'BEGIN {exit !(l < m)}' && [[ $apps == 0 ]]; then :; else idle_since=$now; fi
    cool=1; [[ $t != NA ]] && ! awk -v t="$t" -v m="$TEMP_MAX_C" 'BEGIN {exit !(t < m)}' && cool=0
    if (( now - idle_since >= IDLE_S && cool )); then break; fi
    if (( now - start >= GATE_MAX_S )); then
        log "gate did not open: idle $((now - idle_since)) s, load $l, CPU $t C, GPU processes $apps"; exit 3
    fi
    sleep 10
done
log "gate open: load $(load1), CPU $(cpu_temp) C, GPU processes $(gpu_apps)"
sensors_loop > "$RAW/sensors.tsv" 2>/dev/null &
SENSORS=$!
trap 'kill $SENSORS 2>/dev/null' EXIT
{
    echo "date=$(date -Is)"
    echo "tree=${TREE:-NA} base=${BASE:-NA} threads=$RAYON_NUM_THREADS warm=$WARM"
    echo "cpu=$(awk -F': ' '/^model name/ {print $2; exit}' /proc/cpuinfo) cores=$(nproc)"
    nvidia-smi --query-gpu=name,memory.total,driver_version,clocks.max.sm,clocks.max.mem,power.limit --format=csv,noheader 2>/dev/null | sed 's/^/gpu=/'
} > "$RAW/box.txt"

# One rc1 process: mode k warm out-file. Rows are appended without the header.
rc1() {
    local mode=$1 k=$2 warm=$3 f=$4 tmp rc
    tmp=$(mktemp "$RAW/.rc1.XXXXXX")
    RC1_K=$k RC1_WARM=$warm RC1_REP=1 RC1_STOCK_BIN=$BIN_DIR/rc1-cpu \
        lk timeout --kill-after=3s 2400s "$BIN_DIR/rc1-$mode" run > "$tmp" 2>> "$RAW/err.log"
    rc=$?
    [[ -s $f ]] || head -1 "$tmp" > "$f"
    tail -n +2 "$tmp" >> "$f"; rm -f "$tmp"
    log "rc1 $mode k=$k warm=$warm rc=$rc"
    return $rc
}

# 1. Single proofs by size, CPU and GPU alternating which goes first.
phase h2h
i=0
for k in $KS; do
    if (( i++ % 2 == 0 )); then order="cpu gpu"; else order="gpu cpu"; fi
    for m in $order; do rc1 $m $k $WARM "$RAW/h2h-$m.tsv" || exit 1; done
done

# 2. Sequential run: one process per path, SEQ_N warm proofs.
if (( SEQ_N > 0 )); then
    phase seq
    rc1 gpu $SEQ_K $SEQ_N "$RAW/seq-gpu.tsv" || exit 1
    rc1 cpu $SEQ_K $SEQ_N "$RAW/seq-cpu.tsv" || exit 1
fi

# 3. Batch proving, with a 100 ms GPU utilization sampler around each GPU batch.
if [[ -n $BATCH_BIN ]]; then
    phase batch
    : > "$RAW/batch.txt"
    for n in $BATCH_SIZES; do
        for m in gpu cpu; do
            u=$RAW/batch-util-$m-$n.csv
            nvidia-smi --query-gpu=timestamp,utilization.gpu,clocks.sm --format=csv,noheader,nounits -lms 100 > "$u" 2>/dev/null &
            s=$!
            t0=$(date +%s.%N)
            if [[ $m == cpu ]]; then
                out=$(CUDA_VISIBLE_DEVICES= timeout 2400s "$BATCH_BIN" "$n" "$BATCH_K" 2>> "$RAW/err.log"); rc=$?
            else
                out=$(lk timeout 2400s "$BATCH_BIN" "$n" "$BATCH_K" 2>> "$RAW/err.log"); rc=$?
            fi
            t1=$(date +%s.%N)
            kill $s 2>/dev/null; wait $s 2>/dev/null
            echo -e "$m\t$n\t$BATCH_K\t$rc\t$t0\t$t1\t$out" >> "$RAW/batch.txt"
            log "batch $m n=$n rc=$rc"
            (( rc == 0 )) || exit 1
        done
    done
fi

# 4. Alternating comparisons: A, B, A, B, one process per run.
if [[ -n $ABAB_FILE ]]; then
    phase abab
    cp "$ABAB_FILE" "$RAW/abab-plan.tsv"
    while IFS=$'\t' read -r change what kind k warm pairs a b; do
        [[ -z $change || $change == \#* ]] && continue
        f=$RAW/abab-$change.tsv; : > "$f"
        for p in $(seq 1 "$pairs"); do
            for arm in A B; do
                d=$a; [[ $arm == B ]] && d=$b
                tmp=$(mktemp "$RAW/.ab.XXXXXX")
                case $kind in
                    rc1-gpu|rc1-cpu)
                        RC1_K=$k RC1_WARM=$warm RC1_REP=1 RC1_STOCK_BIN=$d/rc1-cpu \
                            lk timeout --kill-after=3s 2400s "$d/${kind}" run > "$tmp" 2>> "$RAW/err.log"; rc=$?
                        # state and prove_s are columns 7 and 8 of the rc1 row.
                        awk -v a=$arm -v p=$p 'BEGIN {OFS="\t"} NR > 1 {print a, p, $7, $8}' "$tmp" >> "$f" ;;
                    lookup)
                        LB_K=$k LB_WARM=$warm lk timeout 2400s "$d/lookup_bench" > "$tmp" 2>> "$RAW/err.log"; rc=$?
                        awk -v a=$arm -v p=$p 'BEGIN {OFS="\t"} {print a, p, $5, $6}' "$tmp" >> "$f" ;;
                    *) log "unknown kind $kind"; exit 2 ;;
                esac
                rm -f "$tmp"
                log "abab $change $arm pair $p rc=$rc"
                (( rc == 0 )) || exit 1
            done
        done
    done < "$ABAB_FILE"
fi
phase done
kill $SENSORS 2>/dev/null; wait $SENSORS 2>/dev/null
python3 gpu-prover/bench/session/summarize.py "$OUT" && log "session done: $OUT/session.json"
