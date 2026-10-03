#!/usr/bin/env python3
"""One-slot Linux resource guard for bounded local Lean work on mailuefterl."""
import argparse
import fcntl
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone

GIB = 1024**3
CAP = 8 * GIB
LOCK_PATH = Path("/tmp/stafford38-linux-guard.lock")


def foreign_lean():
    found = []
    for ent in Path("/proc").iterdir():
        if not ent.name.isdigit():
            continue
        try:
            name = ent.joinpath("comm").read_text().strip()
            if name in ("lean", "lake"):
                found.append(int(ent.name))
        except OSError:
            pass
    return found


def acquire_slot():
    lock = LOCK_PATH.open("a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        lock.close()
        return None
    return lock


class Interrupted(Exception):
    def __init__(self, signum):
        self.signum = signum


def interrupted(signum, frame):
    raise Interrupted(signum)


def now():
    return datetime.now(timezone.utc).isoformat()


def memory():
    return {x.partition(":")[0]: int(x.split()[1]) * 1024
            for x in Path("/proc/meminfo").read_text().splitlines() if x.endswith("kB")}


def pressure():
    result = {"some": None, "full": None}
    try:
        for line in Path("/proc/pressure/memory").read_text().splitlines():
            fields = line.split()
            result[fields[0]] = float(next(x[6:] for x in fields if x.startswith("avg10=")))
    except (OSError, StopIteration, ValueError):
        pass
    return result


def snapshot():
    m = memory()
    return {"mem_total_bytes": m.get("MemTotal"), "mem_available_bytes": m.get("MemAvailable"),
            "swap_used_bytes": m.get("SwapTotal", 0) - m.get("SwapFree", 0),
            "psi": pressure()}


def reserve(total):
    return max(8 * GIB, math.ceil(total * 0.05)) if total is not None else 8 * GIB


def causes(sample, rss, disk_free, startup_swap, *, preflight=False):
    result = []
    available, total = sample["mem_available_bytes"], sample["mem_total_bytes"]
    floor = reserve(total)
    if available is None or total is None:
        result.append("node-memory-unknown")
    elif (available < CAP + floor) if preflight else (available < floor):
        result.append("preflight-memory-reserve" if preflight else "node-memory-reserve")
    if rss > CAP:
        result.append("aggregate-rss-cap")
    psi = sample["psi"]
    if psi["full"] is not None and psi["full"] >= 1.0:
        result.append("memory-psi-full")
    if psi["some"] is not None and psi["some"] >= 10.0:
        result.append("memory-psi-some")
    if sample["swap_used_bytes"] - startup_swap >= GIB:
        result.append("node-swap-growth-1gib")
    if disk_free < (100 if preflight else 50) * GIB:
        result.append("preflight-disk-below-100gib" if preflight else "disk-free-below-50gib")
    return result


def group(pgid):
    pages, live = 0, []
    for ent in Path("/proc").iterdir():
        if not ent.name.isdigit():
            continue
        try:
            fields = ent.joinpath("stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == pgid:
                pages += int(ent.joinpath("statm").read_text().split()[1])
                if fields[0] not in ("Z", "X"):
                    live.append(int(ent.name))
        except (OSError, ValueError, IndexError):
            pass
    return pages * os.sysconf("SC_PAGE_SIZE"), live


def stop(pgid):
    try:
        if not group(pgid)[1]:
            return
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        return
    until = time.monotonic() + 2
    while group(pgid)[1] and time.monotonic() < until:
        time.sleep(.1)
    if group(pgid)[1]:
        try:
            os.killpg(pgid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    # Keep the slot until every live group member has actually disappeared.
    while group(pgid)[1]:
        time.sleep(.05)


def atomic(path, value):
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    t = p.with_name(p.name + f".tmp.{os.getpid()}")
    t.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(t, p)


def disk_sample(paths):
    values = {str(Path(p).resolve()): shutil.disk_usage(p).free for p in paths}
    return min(values.values()), values


def check():
    lock = acquire_slot()
    if lock is None:
        print("LINUX_GUARD REFUSED: local-slot-busy", file=sys.stderr)
        return 96
    try:
        return check_resources()
    finally:
        lock.close()


def check_resources():
    sample = snapshot()
    disk, disks = disk_sample((Path.cwd(), "/mnt/storage"))
    cpus = sorted(os.sched_getaffinity(0))
    why = causes(sample, 0, disk, sample["swap_used_bytes"], preflight=True)
    if foreign_lean():
        why.append("foreign-lean-or-lake")
    if len(cpus) < 2:
        why.append("cpu-affinity-below-2")
    if why:
        print("LINUX_GUARD REFUSED: " + ",".join(why), file=sys.stderr)
        return 96
    print(f"LINUX_GUARD OK host={os.uname().nodename} available_gib={sample['mem_available_bytes']/GIB:.1f} "
          f"swap_used_gib={sample['swap_used_bytes']/GIB:.1f} disk_free_gib={disk/GIB:.1f} "
          f"reserve_gib={reserve(sample['mem_total_bytes'])/GIB:.1f} affinity={cpus[:2]} cap_gib=8 threads=2")
    print("disk_free_gib=" + json.dumps({p: round(v/GIB, 1) for p, v in disks.items()}, sort_keys=True))
    return 0


def run(args):
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        raise SystemExit("provide a command after --")
    lock = acquire_slot()
    if lock is None:
        print("LINUX_GUARD REFUSED: local-slot-busy", file=sys.stderr)
        return 96
    sample = snapshot()
    snapshot_start_swap = sample["swap_used_bytes"]
    started = now()
    disk, disks = disk_sample((args.cwd, "/mnt/storage"))
    allowed = sorted(os.sched_getaffinity(0))
    why = causes(sample, 0, disk, sample["swap_used_bytes"], preflight=True)
    if foreign_lean():
        why.append("foreign-lean-or-lake")
    if len(allowed) < 2:
        why.append("cpu-affinity-below-2")
    if why:
        print("LINUX_GUARD REFUSED: " + ",".join(why), file=sys.stderr)
        return 96
    chosen = allowed[:2]
    env = os.environ.copy()
    for key in ("LEAN_NUM_THREADS", "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
        env[key] = "2"
    env["OMP_DYNAMIC"] = "FALSE"
    summary = str(Path(args.log).with_suffix(".json"))
    progress = str(Path(args.log).with_suffix(".progress.json"))
    start = time.monotonic()
    Path(args.log).parent.mkdir(parents=True, exist_ok=True)
    log_file = open(args.log, "w")
    watched = (signal.SIGTERM, signal.SIGINT)
    old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched)
    proc = subprocess.Popen(command, cwd=args.cwd, env=env, stdout=log_file,
                            stderr=subprocess.STDOUT, preexec_fn=lambda: (os.setsid(), os.sched_setaffinity(0, set(chosen)), signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)))
    peak, min_avail, peak_swap, stop_cause = 0, sample["mem_available_bytes"], 0, []
    deadline = start + args.timeout
    next_progress = start + 2
    reason = "finished"
    previous = {s: signal.signal(s, interrupted) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
      signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)
      while proc.poll() is None or group(proc.pid)[1]:
        sample = snapshot()
        rss, _ = group(proc.pid)
        peak = max(peak, rss)
        min_avail = min(min_avail, sample["mem_available_bytes"])
        swap_growth = max(0, sample["swap_used_bytes"] - snapshot_start_swap)
        peak_swap = max(peak_swap, swap_growth)
        disk, disks = disk_sample((args.cwd, "/mnt/storage"))
        stop_cause = causes(sample, rss, disk, snapshot_start_swap)
        if time.monotonic() >= deadline:
            stop_cause.append("timeout")
        if time.monotonic() >= next_progress:
            atomic(progress, {"timestamp_utc": now(), "current_rss_bytes": rss,
                              "peak_rss_bytes": peak, "mem_available_bytes": sample["mem_available_bytes"],
                              "minimum_available_bytes": min_avail,
                              "swap_growth_bytes": max(0, sample["swap_used_bytes"] - snapshot_start_swap),
                              "psi": sample["psi"], "stop_cause": stop_cause})
            next_progress = time.monotonic() + 2
        if stop_cause:
            reason = "+".join(stop_cause)
            stop(proc.pid)
            break
        time.sleep(.25)
    except Interrupted as exc:
        reason = "signal-" + str(exc.signum)
        stop_cause = [reason]
    except BaseException:
        stop(proc.pid)
        proc.wait()
        raise
    finally:
        for s in previous:
            signal.signal(s, signal.SIG_IGN)
        stop(proc.pid)
        proc.wait()
        for s, handler in previous.items():
            signal.signal(s, handler)
    if proc.poll() is None:
        try:
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            stop(proc.pid)
            proc.wait()
    rss, children = group(proc.pid)
    if children:
        stop(proc.pid)
        rss, children = group(proc.pid)
        if children:
            reason = "undrained-descendant"
            stop_cause = [reason]
    rec = {"host": os.uname().nodename, "started_utc": started, "finished_utc": now(),
           "command": command, "timeout_seconds": args.timeout, "threads": 2, "cpu_affinity": chosen,
           "rss_cap_bytes": CAP, "peak_rss_bytes": max(peak, rss), "minimum_available_bytes": min_avail,
           "peak_swap_growth_bytes": peak_swap, "node_reserve_bytes": reserve(snapshot()["mem_total_bytes"]),
           "reason": reason, "stop_cause": stop_cause, "command_exit_code": proc.returncode,
           "live_child_pids_at_exit": children,
           "disk_free_after_bytes": disk_sample((args.cwd, "/mnt/storage"))[1]}
    code = 95 if reason == "undrained-descendant" else 93 if "timeout" in reason else 91 if stop_cause else proc.returncode
    if reason.startswith("signal-"):
        code = 128 + int(reason.split("-")[1])
    rec["guard_exit_code"] = code
    atomic(summary, rec)
    log_file.close()
    lock.close()
    print(f"LINUX_GUARD exit={code} reason={reason} peak_rss_mib={rec['peak_rss_bytes']/2**20:.1f}")
    return code


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="action", required=True)
    sub.add_parser("check")
    r = sub.add_parser("run")
    r.add_argument("--timeout", type=int, required=True)
    r.add_argument("--log", required=True)
    r.add_argument("--cwd", default="/mnt/storage")
    r.add_argument("command", nargs=argparse.REMAINDER)
    a = p.parse_args()
    return check() if a.action == "check" else run(a)


if __name__ == "__main__":
    raise SystemExit(main())
