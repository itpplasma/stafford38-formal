#!/usr/bin/env python3
"""Bound one process group by CPU, RSS, time, and live node memory pressure."""

import argparse
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time
from datetime import datetime, timezone

GIB = 1024**3
ACTIVE = None
SIGNAL_SEEN = 0
SIGNAL_CONTEXT = {}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def meminfo() -> dict[str, int]:
    return {line.partition(":")[0]: int(line.split()[1]) * 1024
            for line in Path("/proc/meminfo").read_text().splitlines()
            if line.endswith("kB")}


def node_sample() -> dict:
    mem = meminfo()
    psi = {"some": None, "full": None}
    try:
        for line in Path("/proc/pressure/memory").read_text().splitlines():
            fields = line.split()
            psi[fields[0]] = float(next(x.split("=", 1)[1] for x in fields if x.startswith("avg10=")))
    except (OSError, StopIteration, ValueError):
        pass
    total_swap = mem.get("SwapTotal")
    swap_used = total_swap - mem.get("SwapFree", total_swap) if total_swap is not None else None
    return {"mem_total_bytes": mem.get("MemTotal"), "mem_available_bytes": mem.get("MemAvailable"),
            "psi_some_avg10": psi["some"], "psi_full_avg10": psi["full"],
            "psi_status": "available" if all(v is not None for v in psi.values()) else "unknown",
            "swap_used_bytes": swap_used}


def node_reserve(total_bytes: int) -> int:
    return max(8 * GIB, math.ceil(0.05 * total_bytes))


def policy_causes(sample: dict, rss: int, cap: int, reserve: int,
                  startup_swap: int | None, *, preflight: bool = False) -> list[str]:
    causes = []
    available = sample.get("mem_available_bytes")
    if available is None:
        causes.append("node-memory-unknown")
    elif preflight and available < cap + reserve:
        causes.append("preflight-memory-reserve")
    elif not preflight and available < reserve:
        causes.append("node-memory-reserve")
    if rss > cap:
        causes.append("job-rss-cap")
    if sample.get("psi_full_avg10") is not None and sample["psi_full_avg10"] >= 1.0:
        causes.append("memory-psi-full")
    if sample.get("psi_some_avg10") is not None and sample["psi_some_avg10"] >= 10.0:
        causes.append("memory-psi-some")
    used = sample.get("swap_used_bytes")
    if used is not None and startup_swap is not None and used - startup_swap >= GIB:
        causes.append("node-swap-growth-1gib")
    return causes


def group_state(pgid: int) -> tuple[int, list[int]]:
    pages, live = 0, []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == pgid:
                pages += int((entry / "statm").read_text().split()[1])
                if fields[0] not in ("Z", "X"):
                    live.append(int(entry.name))
        except (OSError, ValueError, IndexError):
            continue
    return pages * os.sysconf("SC_PAGE_SIZE"), live


def stop_group(pgid: int) -> None:
    try:
        if not group_state(pgid)[1]:
            return
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 2
    while group_state(pgid)[1] and time.monotonic() < deadline:
        time.sleep(0.1)
    if group_state(pgid)[1]:
        try:
            os.killpg(pgid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".tmp.{os.getpid()}")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def task_cgroup() -> dict[str, str]:
    raw = Path("/proc/self/cgroup").read_text().strip()
    result = {"proc_self_cgroup": raw, "memory_enforcement": "unknown"}
    files = (("memory_max", "memory.max"), ("memory_current", "memory.current"),
             ("memory_limit_v1", "memory.limit_in_bytes"),
             ("memory_usage_v1", "memory.usage_in_bytes"),
             ("cpuset_cpus_effective", "cpuset.cpus.effective"))
    for line in raw.splitlines():
        _, controllers, relpath = line.split(":", 2)
        if controllers == "":
            bases = [Path("/sys/fs/cgroup") / relpath.lstrip("/")]
        elif "memory" in controllers.split(","):
            bases = [Path("/sys/fs/cgroup/memory") / relpath.lstrip("/")]
        else:
            continue
        for key, name in files:
            try:
                result[key] = (bases[0] / name).read_text().strip()
            except OSError:
                pass
    limits = [result.get(k) for k in ("memory_max", "memory_limit_v1") if result.get(k)]
    if any(value not in ("max", "9223372036854771712") for value in limits):
        result["memory_enforcement"] = "cgroup memory limit visible"
    return result


def progress_record(base: dict, sample: dict, current: int, peak: int,
                    min_available: int, peak_swap_growth: int, peak_psi: dict,
                    cause: list[str] | None = None) -> dict:
    return {**base, **sample, "timestamp_utc": now(), "node_mem_reserve_floor_bytes": base["node_mem_reserve_floor_bytes"],
            "job_current_rss_bytes": current, "job_peak_rss_bytes": peak,
            "node_mem_available_min_bytes": min_available,
            "node_swap_growth_peak_bytes": peak_swap_growth,
            "psi_some_avg10_peak": peak_psi["some"], "psi_full_avg10_peak": peak_psi["full"],
            "stop_cause": cause or []}


def on_signal(signum: int, _frame) -> None:
    global SIGNAL_SEEN
    SIGNAL_SEEN = signum
    signal.signal(signum, signal.SIG_IGN)
    if ACTIVE is not None:
        stop_group(ACTIVE.pid)
    ctx = SIGNAL_CONTEXT
    if ctx:
        ctx["terminal"].update(progress_record(ctx["base"], ctx["sample"], ctx["current"],
                                                ctx["peak"], ctx["min_available"],
                                                ctx["peak_swap_growth"], ctx["peak_psi"],
                                                [f"signal-{signum}"]))
        ctx["terminal"].update({"reason": f"signal-{signum}", "guard_exit_code": 128 + signum,
                                "command_exit_code": ACTIVE.returncode if ACTIVE else None,
                                "live_child_pids_at_exit": group_state(ACTIVE.pid)[1] if ACTIVE else []})
        atomic_json(ctx["summary"], ctx["terminal"])
        atomic_json(ctx["progress"], ctx["terminal"])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--progress", type=Path)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    parser.add_argument("--timeout", type=int, default=3500)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--rss-cap-gib", type=float, default=8.0)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("provide a command after --")
    global ACTIVE, SIGNAL_CONTEXT
    job_id = os.environ.get("SLURM_JOB_ID")
    if not job_id:
        raise SystemExit("refusing to run outside a Slurm job (SLURM_JOB_ID missing)")
    nodes = int(os.environ.get("SLURM_JOB_NUM_NODES", os.environ.get("SLURM_NNODES", "0")))
    ntasks = int(os.environ.get("SLURM_NTASKS", "0"))
    cpu_mask = sorted(os.sched_getaffinity(0))
    allocated = int(os.environ.get("SLURM_CPUS_ON_NODE", os.environ.get("SLURM_CPUS_PER_TASK", "0")))
    reserved = allocated * ntasks
    mem = meminfo()
    host_cpus = os.cpu_count() or 1
    mem_per_cpu = mem["MemTotal"] / GIB / host_cpus
    cap = int(args.rss_cap_gib * GIB)
    reserve = node_reserve(mem["MemTotal"])
    needed = max(args.threads, math.ceil((args.rss_cap_gib) / (0.9 * mem_per_cpu)))
    slurm_mem_mb = int(os.environ.get("SLURM_MEM_PER_NODE", "0"))
    sample = node_sample()
    initial_swap = sample.get("swap_used_bytes")
    progress = (args.progress or args.summary.with_name("progress.json")).resolve()
    summary = args.summary.resolve()
    base = {"job_id": job_id, "host": os.uname().nodename, "nodes": nodes, "tasks": ntasks,
            "reserved_cpus": reserved, "allocated_cpus_on_node": allocated,
            "cpu_affinity_before": cpu_mask, "threads": args.threads,
            "slurm_mem_per_node_mib": slurm_mem_mb, "rss_cap_bytes": cap,
            "node_mem_reserve_floor_bytes": reserve, "host_cpu_count": host_cpus,
            "memory_per_cpu_gib": mem_per_cpu, "minimum_reserved_cpus": needed,
            "task_cgroup": task_cgroup(), "command": command,
            "disk_path": str(args.cwd.resolve()), "disk_total_bytes": shutil.disk_usage(args.cwd).total,
            "disk_free_before_bytes": shutil.disk_usage(args.cwd).free,
            "startup_swap_used_bytes": initial_swap}
    mem_available = sample.get("mem_available_bytes")
    preflight_causes = policy_causes(sample, 0, cap, reserve, initial_swap, preflight=True)
    if nodes != 1 or ntasks != 1:
        preflight_causes.append("allocation-must-be-one-node-one-task")
    if args.threads < 1 or allocated < args.threads or len(cpu_mask) < args.threads:
        preflight_causes.append("cpu-affinity-insufficient")
    if reserved < needed:
        preflight_causes.append("cpu-reservation-below-ram-equivalent")
    if slurm_mem_mb * 1024**2 < cap:
        preflight_causes.append("slurm-memory-request-below-rss-cap")
    if preflight_causes:
        terminal = {**base, **sample, "started_utc": now(), "finished_utc": now(),
                    "reason": "+".join(preflight_causes), "stop_cause": preflight_causes,
                    "guard_exit_code": 96, "command_exit_code": None,
                    "node_mem_available_min_bytes": mem_available,
                    "node_swap_growth_peak_bytes": 0, "job_peak_rss_bytes": 0,
                    "progress_interval_seconds": 2}
        atomic_json(progress, terminal)
        atomic_json(summary, terminal)
        print(f"CLUSTER_GUARD REFUSED causes={','.join(preflight_causes)}", flush=True)
        return 96
    chosen = cpu_mask[:args.threads]
    os.sched_setaffinity(0, set(chosen))
    for key in ("LEAN_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
        os.environ[key] = str(args.threads)
    os.environ["OMP_DYNAMIC"] = "FALSE"
    base["cpu_affinity_child"] = chosen
    print(f"CLUSTER_GUARD job={job_id} cpus={reserved} affinity={chosen} threads={args.threads} rss_cap_gib={args.rss_cap_gib}", flush=True)
    start_time = now()
    started_mono = time.monotonic()
    disk = shutil.disk_usage(args.cwd)
    peak = min_available
    peak_rss = peak_swap_growth = 0
    peak_psi = {"some": sample.get("psi_some_avg10"), "full": sample.get("psi_full_avg10")}
    current = 0
    atomic_json(progress, progress_record(base, sample, current, peak_rss, peak, peak_swap_growth, peak_psi))
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, on_signal)
    proc = subprocess.Popen(command, cwd=args.cwd, env=os.environ.copy(), preexec_fn=os.setsid)
    ACTIVE = proc
    SIGNAL_CONTEXT = {"base": base, "summary": summary, "progress": progress, "sample": sample,
                      "current": current, "peak": peak_rss, "min_available": peak,
                      "peak_swap_growth": peak_swap_growth, "peak_psi": peak_psi,
                      "terminal": {"started_utc": start_time}}
    deadline = started_mono + args.timeout
    next_progress = time.monotonic() + 2
    stop_causes = []
    reason = "finished"
    while proc.poll() is None and not SIGNAL_SEEN:
        sample = node_sample()
        current, live = group_state(proc.pid)
        peak_rss = max(peak_rss, current)
        available = sample.get("mem_available_bytes")
        if available is not None:
            peak = min(peak, available)
        swap_used = sample.get("swap_used_bytes")
        swap_growth = max(0, swap_used - initial_swap) if swap_used is not None and initial_swap is not None else 0
        peak_swap_growth = max(peak_swap_growth, swap_growth)
        for key in ("some", "full"):
            val = sample.get(f"psi_{key}_avg10")
            if val is not None:
                peak_psi[key] = max(peak_psi[key] or val, val)
        stop_causes = policy_causes(sample, current, cap, reserve, initial_swap)
        if time.monotonic() >= deadline:
            stop_causes.append("timeout")
        SIGNAL_CONTEXT.update({"sample": sample, "current": current, "peak": peak_rss,
                               "min_available": peak, "peak_swap_growth": peak_swap_growth,
                               "peak_psi": peak_psi})
        if time.monotonic() >= next_progress:
            atomic_json(progress, progress_record(base, sample, current, peak_rss, peak,
                                                   peak_swap_growth, peak_psi, stop_causes))
            next_progress = time.monotonic() + 2
        if stop_causes:
            reason = "+".join(stop_causes)
            stop_group(proc.pid)
            break
        time.sleep(0.25)
    if proc.poll() is None:
        try:
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            stop_group(proc.pid)
            proc.wait()
    live_after = group_state(proc.pid)[1]
    if SIGNAL_SEEN:
        reason = f"signal-{SIGNAL_SEEN}"
        stop_causes = [reason]
    elif live_after:
        stop_group(proc.pid)
        live_after = group_state(proc.pid)[1]
        reason = "orphaned-descendant" if not live_after else "undrained-descendant"
        stop_causes = [reason]
    sample = node_sample()
    current, live_after = group_state(proc.pid)
    peak_rss = max(peak_rss, current)
    available = sample.get("mem_available_bytes")
    if available is not None:
        peak = min(peak, available)
    command_code = proc.returncode
    guard_code = (95 if live_after or reason in ("orphaned-descendant", "undrained-descendant") else
                  96 if reason.startswith("preflight") else 93 if "timeout" in reason else
                  91 if stop_causes else 128 + SIGNAL_SEEN if SIGNAL_SEEN else
                  command_code if command_code >= 0 else 128 - command_code)
    terminal = {**base, **sample, "started_utc": start_time, "finished_utc": now(),
                "elapsed_seconds": time.monotonic() - started_mono, "reason": reason,
                "stop_cause": stop_causes, "guard_exit_code": guard_code,
                "command_exit_code": command_code, "timeout_seconds": args.timeout,
                "node_mem_available_min_bytes": peak, "node_swap_growth_peak_bytes": peak_swap_growth,
                "job_current_rss_bytes": current, "job_peak_rss_bytes": peak_rss,
                "psi_some_avg10_peak": peak_psi["some"], "psi_full_avg10_peak": peak_psi["full"],
                "live_child_pids_at_exit": live_after, "progress_interval_seconds": 2,
                "disk_free_after_bytes": shutil.disk_usage(args.cwd).free}
    atomic_json(summary, terminal)
    atomic_json(progress, terminal)
    print(f"CLUSTER_GUARD exit={guard_code} command_exit={command_code} reason={reason} peak_rss_mib={peak_rss/GIB*1024:.1f}", flush=True)
    return guard_code


if __name__ == "__main__":
    raise SystemExit(main())
