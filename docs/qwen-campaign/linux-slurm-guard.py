#!/usr/bin/env python3
"""Linux allocation-only adapter; launch inside srun --ntasks=1 --cpus-per-task=2."""
import ctypes
import importlib.util
import os
from pathlib import Path
import re
import signal
import sys
import time

spec = importlib.util.spec_from_file_location('local_guard', Path(__file__).with_name('linux-guard.py'))
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)


def placement(env=None, host=None, cgroup=None, affinity=None):
    env = os.environ if env is None else env
    host = os.uname().nodename.split('.')[0] if host is None else host
    cgroup = Path('/proc/self/cgroup').read_text() if cgroup is None else cgroup
    affinity = os.sched_getaffinity(0) if affinity is None else affinity
    cluster = env.get('SLURM_CLUSTER_NAME', '')
    job = env.get('SLURM_JOB_ID', '')
    limit = {'acluster': 34, 'scluster': 20}.get(cluster, 0)
    match = re.fullmatch(r'node([1-9][0-9]*)', host)
    errors = []
    if not limit or not match or int(match[1]) > limit:
        errors.append('unapproved-cluster-or-node')
    if not job.isdigit() or not re.search(r'(?:^|/)job[_-]' + re.escape(job) + r'(?:/|\.|$)', cgroup, re.M):
        errors.append('allocation-cgroup-mismatch')
    if env.get('SLURMD_NODENAME') != host:
        errors.append('allocation-node-mismatch')
    if env.get('SLURM_CPUS_PER_TASK') != '2' or len(affinity) != 2:
        errors.append('requires-srun-c2-and-two-cpu-affinity')
    if not env.get('SLURM_STEP_ID', '').isdigit() or not re.search(
            r'(?:/|^)step[_-]' + re.escape(env.get('SLURM_STEP_ID', '')) + r'(?:/|\.|$)', cgroup, re.M):
        errors.append('requires-srun-step')
    if env.get('SLURM_NTASKS') != '1' or env.get('SLURM_JOB_NUM_NODES') != '1':
        errors.append('requires-single-task-single-node')
    return errors


def foreign_lean():
    # Only a Lean process in this allocation blocks our slot.
    job = os.environ['SLURM_JOB_ID']
    found = []
    for ent in Path('/proc').iterdir():
        if not ent.name.isdigit():
            continue
        try:
            if ent.joinpath('comm').read_text().strip() in ('lean', 'lake') and re.search(
                    r'(?:^|/)job[_-]' + re.escape(job) + r'(?:/|\.|$)', ent.joinpath('cgroup').read_text(), re.M):
                found.append(int(ent.name))
        except OSError:
            pass
    return found


def descendants(unused_pgid):
    # PR_SET_CHILD_SUBREAPER keeps double-forked/session-escaped children owned.
    rows = {}
    for ent in Path('/proc').iterdir():
        if not ent.name.isdigit():
            continue
        try:
            fields = ent.joinpath('stat').read_text().rsplit(')', 1)[1].split()
            rows[int(ent.name)] = (int(fields[1]), fields[0], int(ent.joinpath('statm').read_text().split()[1]))
        except (OSError, ValueError, IndexError):
            pass
    owned = {os.getpid()}
    while True:
        more = {pid for pid, row in rows.items() if row[0] in owned}
        if more <= owned:
            break
        owned |= more
    owned.discard(os.getpid())
    return sum(rows[p][2] for p in owned) * os.sysconf('SC_PAGE_SIZE'), [p for p in owned if rows[p][1] not in ('Z', 'X')]


def stop(pgid):
    deadline = time.monotonic() + 2
    while True:
        pids = descendants(pgid)[1]
        if not pids:
            return
        sig = signal.SIGTERM if time.monotonic() < deadline else signal.SIGKILL
        for pid in pids:
            try:
                fd = os.pidfd_open(pid)
                try:
                    if pid in descendants(pgid)[1]:
                        signal.pidfd_send_signal(fd, sig)
                finally:
                    os.close(fd)
            except ProcessLookupError:
                pass
        time.sleep(.05)


def main():
    errors = placement()
    if errors:
        print('SLURM_GUARD REFUSED: ' + ','.join(errors), file=sys.stderr)
        return 96
    if ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), 'PR_SET_CHILD_SUBREAPER failed')
    cluster = os.environ['SLURM_CLUSTER_NAME']
    slot = Path.home() / '.stafford38-guard'
    slot.mkdir(mode=0o700, exist_ok=True)
    g.LOCK_PATH = slot / (cluster + '.lock')
    g.foreign_lean = foreign_lean
    g.group = descendants
    g.stop = stop
    original_disk = g.disk_sample
    storage = os.environ.get('STAFFORD_STORAGE', str(Path.home()))
    g.disk_sample = lambda paths: original_disk((paths[0], storage))
    original_atomic = g.atomic
    def atomic(path, record):
        record.update(cluster=cluster, slurm_job_id=os.environ['SLURM_JOB_ID'],
                      slurm_step_id=os.environ['SLURM_STEP_ID'], cgroup=Path('/proc/self/cgroup').read_text().strip())
        original_atomic(path, record)
    g.atomic = atomic
    return g.main()


if __name__ == '__main__':
    raise SystemExit(main())
