#!/usr/bin/env bash
# Resource guard for the serial Qwen campaign on faepmac1.
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
#   94 swap kill.
set -uo pipefail

# Truly free RAM (vm_stat free + speculative pages). The macOS "free
# percentage" also counts reclaimable pages, including the model server's
# cached weights, so it stays high until the LLM is already being evicted.
# During a build macOS also fills free pages with file cache (memory-mapped
# .olean files), so low free RAM alone is not a kill reason. The primary
# limit is the build's own resident size; kernel memory pressure, swap and a
# low free-RAM floor are the backstops that protect the model server.
START_FREE_GB=${START_FREE_GB:-60}
KILL_FREE_GB=${KILL_FREE_GB:-8}
RSS_CAP_GB=${RSS_CAP_GB:-64}
START_DISK_GB=${START_DISK_GB:-100}
KILL_DISK_GB=${KILL_DISK_GB:-50}
KILL_SWAP_GB=${KILL_SWAP_GB:-12}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-8}
DATA_VOLUME=/System/Volumes/Data

free_gb() { vm_stat | awk '/page size of/ {ps=$8} /Pages free/ {f=$3} /Pages speculative/ {sp=$3} END {gsub("\\.","",f); gsub("\\.","",sp); printf "%d\n", (f+sp)*ps/1073741824}'; }
disk_gb() { df -g "$DATA_VOLUME" | awk 'NR==2 {print $4}'; }
swap_gb() { sysctl -n vm.swapusage | awk '{for(i=1;i<=NF;i++) if($i=="used") {v=$(i+2); sub("M","",v); printf "%d\n", v/1024}}'; }
pressure() { sysctl -n kern.memorystatus_vm_pressure_level; }  # 1 normal, 2 warn, 4 critical
others() { pgrep -u "$(id -u)" -x lake; pgrep -u "$(id -u)" -x lean; }

report() {
  echo "free_mem_gb=$(free_gb) disk_free_gb=$(disk_gb) swap_used_gb=$(swap_gb) pressure_level=$(pressure) lean_threads=$LEAN_NUM_THREADS"
  local o; o=$(others | tr '\n' ' ')
  echo "running_lake_or_lean_pids=${o:-none}"
}

preflight() {
  local o f d s
  o=$(others | tr '\n' ' ')
  [[ -z "$o" ]] || { echo "GUARD REFUSED: lake/lean already running (pids $o); campaign is serial"; return 1; }
  f=$(free_gb); d=$(disk_gb); s=$(swap_gb)
  (( f >= START_FREE_GB )) || { echo "GUARD REFUSED: free memory ${f}G < ${START_FREE_GB}G"; return 1; }
  (( d >= START_DISK_GB )) || { echo "GUARD REFUSED: free disk ${d}G < ${START_DISK_GB}G"; return 1; }
  (( s < KILL_SWAP_GB )) || { echo "GUARD REFUSED: swap used ${s}G >= ${KILL_SWAP_GB}G"; return 1; }
  (( $(pressure) == 1 )) || { echo "GUARD REFUSED: kernel memory pressure level $(pressure)"; return 1; }
  return 0
}

case "${1:-}" in
  check) report; preflight && echo "GUARD OK"; exit $? ;;
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

if ! msg=$(preflight); then echo "$msg" | tee -a "$log"; exit 90; fi

start=$(date +%s)
perl -e 'setpgrp(0,0); exec @ARGV or die "exec: $!"' -- "$@" >>"$log" 2>&1 &
pid=$!
peak_kb=0 reason= code=

kill_group() {
  kill -TERM -- "-$pid" 2>/dev/null; sleep 10; kill -KILL -- "-$pid" 2>/dev/null
}

while kill -0 "$pid" 2>/dev/null; do
  sleep 10
  rss=0
  for p in $(pgrep -g "$pid" 2>/dev/null); do
    r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' '); rss=$(( rss + ${r:-0} ))
  done
  (( rss > peak_kb )) && peak_kb=$rss
  now=$(date +%s)
  if (( rss > RSS_CAP_GB * 1048576 )); then reason=rss-cap; code=91
  elif (( $(pressure) >= 2 )); then reason=memory-pressure; code=91
  elif (( $(free_gb) < KILL_FREE_GB )); then reason=memory; code=91
  elif (( $(disk_gb) < KILL_DISK_GB )); then reason=disk; code=92
  elif (( $(swap_gb) >= KILL_SWAP_GB )); then reason=swap; code=94
  elif (( now - start > timeout )); then reason=timeout; code=93
  fi
  if [[ -n "$reason" ]]; then kill_group; break; fi
done
wait "$pid" 2>/dev/null; rc=$?
[[ -n "$code" ]] && rc=$code
echo "GUARD exit=$rc reason=${reason:-finished} wall_s=$(( $(date +%s) - start )) peak_rss_gb=$(( peak_kb / 1048576 )) free_mem_gb=$(free_gb) disk_free_gb=$(disk_gb) swap_used_gb=$(swap_gb)" | tee -a "$log"
exit "$rc"
