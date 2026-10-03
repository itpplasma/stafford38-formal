#!/usr/bin/env bash
# Resource guard for the shared local Lean execution slot on macOS.
#
#   guard.sh check
#   guard.sh run --timeout SECONDS --log FILE -- COMMAND [ARGS...]
#
# `run` refuses to start when another lake/lean process is alive, when free
# memory or disk is low, or when swap is already heavily used. While the
# command runs, a watchdog kills its whole process group if free memory, disk
# or swap cross the kill thresholds, or if the wall-clock timeout expires.
# The last line of FILE is always a one-line GUARD summary.
#
# Memory, disk and swap thresholds are in GiB and can be overridden by env.
#
# Exit codes: command's own code, or
#   90 preflight refused, 91 memory kill, 92 disk kill, 93 timeout kill,
#   94 swap kill, 95 sustained CPU oversubscription.
set -uo pipefail

# Truly free RAM (vm_stat free + speculative pages). The macOS "free
# percentage" also counts reclaimable pages, including the model server's
# cached weights, so it stays high until the LLM is already being evicted.
# During a build macOS also fills free pages with file cache (memory-mapped
# .olean files), so low free RAM alone is not a kill reason. The primary
# limit is the build's own resident size; kernel memory pressure, swap and a
# low free-RAM floor are the backstops that protect the model server.
START_FREE_GB=${START_FREE_GB:-12}
KILL_FREE_GB=${KILL_FREE_GB:-4}
RSS_CAP_GB=${RSS_CAP_GB:-8}
START_DISK_GB=${START_DISK_GB:-100}
KILL_DISK_GB=${KILL_DISK_GB:-50}
KILL_SWAP_GB=${KILL_SWAP_GB:-12}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=$LEAN_NUM_THREADS
export OPENBLAS_NUM_THREADS=$LEAN_NUM_THREADS
export MKL_NUM_THREADS=$LEAN_NUM_THREADS
export VECLIB_MAXIMUM_THREADS=$LEAN_NUM_THREADS
CPU_CAP=${CPU_CAP:-$LEAN_NUM_THREADS}
POLL_SECONDS=${POLL_SECONDS:-1}
LOCK_DIR=/tmp/stafford38-lean-guard-$(id -u).lock
DATA_VOLUME=/System/Volumes/Data

for name in START_FREE_GB KILL_FREE_GB RSS_CAP_GB START_DISK_GB KILL_DISK_GB KILL_SWAP_GB LEAN_NUM_THREADS CPU_CAP POLL_SECONDS; do
  value=${!name}
  [[ "$value" =~ ^[1-9][0-9]*$ ]] || { echo "guard: invalid $name" >&2; exit 2; }
done
(( LEAN_NUM_THREADS <= CPU_CAP )) || { echo "guard: threads exceed CPU budget" >&2; exit 2; }

free_gb() { vm_stat | awk '/page size of/ {ps=$8} /Pages free/ {f=$3} /Pages speculative/ {sp=$3} END {gsub("\\.","",f); gsub("\\.","",sp); printf "%d\n", (f+sp)*ps/1073741824}'; }
disk_gb() { df -g "$DATA_VOLUME" | awk 'NR==2 {print $4}'; }
swap_gb() { sysctl -n vm.swapusage | awk '{for(i=1;i<=NF;i++) if($i=="used") {v=$(i+2); sub("M","",v); printf "%d\n", v/1024}}'; }
pressure() { sysctl -n kern.memorystatus_vm_pressure_level; }  # 1 normal, 2 warn, 4 critical
others() { pgrep -u "$(id -u)" -x lake; pgrep -u "$(id -u)" -x lean; }

report() {
  echo "free_mem_gb=$(free_gb) disk_free_gb=$(disk_gb) swap_used_gb=$(swap_gb) pressure_level=$(pressure) lean_threads=$LEAN_NUM_THREADS rss_cap_gb=$RSS_CAP_GB cpu_cap=$CPU_CAP"
  local o; o=$(others | tr '\n' ' ')
  echo "running_lake_or_lean_pids=${o:-none}"
}

preflight() {
  local o f d s
  o=$(others | tr '\n' ' ')
  [[ -z "$o" ]] || { echo "GUARD REFUSED: lake/lean already running (pids $o); local slot occupied"; return 1; }
  f=$(free_gb); d=$(disk_gb); s=$(swap_gb)
  (( f >= START_FREE_GB )) || { echo "GUARD REFUSED: free memory ${f}G < ${START_FREE_GB}G"; return 1; }
  (( d >= START_DISK_GB )) || { echo "GUARD REFUSED: free disk ${d}G < ${START_DISK_GB}G"; return 1; }
  (( s < KILL_SWAP_GB )) || { echo "GUARD REFUSED: swap used ${s}G >= ${KILL_SWAP_GB}G"; return 1; }
  (( $(pressure) == 1 )) || { echo "GUARD REFUSED: kernel memory pressure level $(pressure)"; return 1; }
  return 0
}

case "${1:-}" in
  check)
    report
    [[ ! -d "$LOCK_DIR" ]] || { echo "GUARD REFUSED: local slot locked ($LOCK_DIR)"; exit 90; }
    preflight && echo "GUARD OK"; exit $? ;;
  run) shift ;;
  *) sed -n 2,14p "$0"; exit 2 ;;
esac

timeout= log=
while [[ $# -gt 0 ]]; do
  case "$1" in
    --timeout) timeout=$2; shift 2 ;;
    --log) log=$2; shift 2 ;;
    --) shift; break ;;
    *) echo "guard: unknown option $1" >&2; exit 2 ;;
  esac
done
[[ -n "$timeout" && -n "$log" && $# -gt 0 ]] || { echo "guard: need --timeout, --log and a command" >&2; exit 2; }
mkdir -p "$(dirname "$log")"

if ! mkdir "$LOCK_DIR" 2>/dev/null; then
  echo "GUARD REFUSED: local slot locked ($LOCK_DIR)" | tee -a "$log"; exit 90
fi
echo "$$" > "$LOCK_DIR/owner"
group_alive() { pgrep -g "$pid" >/dev/null 2>&1; }
release_lock() {
  if [[ -n "${pid:-}" ]] && group_alive; then
    echo "GUARD: retaining lock for surviving owned process group $pid" >&2
    return
  fi
  rm -f "$LOCK_DIR/owner"; rmdir "$LOCK_DIR"
}
trap release_lock EXIT

if ! msg=$(preflight); then echo "$msg" | tee -a "$log"; exit 90; fi

start=$(date +%s)
perl -e 'setpgrp(0,0); exec @ARGV or die "exec: $!"' -- "$@" >>"$log" 2>&1 &
pid=$!
peak_kb=0 peak_cpu=0 cpu_over=0 reason= code=

kill_group() {
  kill -TERM -- "-$pid" 2>/dev/null; sleep 1; kill -KILL -- "-$pid" 2>/dev/null
  for attempt in 1 2 3; do group_alive || return; sleep 1; done
}
trap 'kill_group; exit 130' INT TERM

while kill -0 "$pid" 2>/dev/null || group_alive; do
  sleep "$POLL_SECONDS"
  rss=0
  cpu=0
  for p in $(pgrep -g "$pid" 2>/dev/null); do
    r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' '); rss=$(( rss + ${r:-0} ))
    # macOS ps reports a decaying CPU average; this is a watchdog signal,
    # not an instantaneous CPU quota. Retain hundredths while summing.
    c=$(ps -o %cpu= -p "$p" 2>/dev/null | awk '{printf "%d", $1 * 100}'); cpu=$(( cpu + ${c:-0} ))
  done
  (( rss > peak_kb )) && peak_kb=$rss
  (( cpu / 100 > peak_cpu )) && peak_cpu=$((cpu / 100))
  if (( cpu > CPU_CAP * 10000 + 1000 )); then cpu_over=$((cpu_over + 1)); else cpu_over=0; fi
  now=$(date +%s)
  if (( rss > RSS_CAP_GB * 1048576 )); then reason=rss-cap; code=91
  elif (( $(pressure) >= 2 )); then reason=memory-pressure; code=91
  elif (( $(free_gb) < KILL_FREE_GB )); then reason=memory; code=91
  elif (( $(disk_gb) < KILL_DISK_GB )); then reason=disk; code=92
  elif (( $(swap_gb) >= KILL_SWAP_GB )); then reason=swap; code=94
  elif (( cpu_over >= 3 )); then reason=cpu-cap; code=95
  elif (( now - start > timeout )); then reason=timeout; code=93
  fi
  if [[ -n "$reason" ]]; then kill_group; break; fi
done
wait "$pid" 2>/dev/null; rc=$?
[[ -n "$code" ]] && rc=$code
echo "GUARD exit=$rc reason=${reason:-finished} wall_s=$(( $(date +%s) - start )) peak_rss_gb=$(( peak_kb / 1048576 )) peak_rss_mb=$(( peak_kb / 1024 )) peak_cpu_percent=$peak_cpu rss_cap_gb=$RSS_CAP_GB cpu_cap=$CPU_CAP lean_threads=$LEAN_NUM_THREADS free_mem_gb=$(free_gb) disk_free_gb=$(disk_gb) swap_used_gb=$(swap_gb)" | tee -a "$log"
exit "$rc"
