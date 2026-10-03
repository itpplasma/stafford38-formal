# Linux Slurm guard adapter review

2026-10-03. Bounded worker implementation; controller owns integration and launch.
No proof build, scheduler submission, SSH, package change, or protected-host access.
Existing `cluster-guard.py` was not modified.

The adapter imports the existing `linux-guard.py` resource watchdog. It requires
an exact approved cluster (`acluster` or `scluster`), node1–34 or node1–20
respectively, matching SLURMD_NODENAME, numeric job and step IDs present in the
current cgroup, one task/node, cpus-per-task=2, and exactly two affinity CPUs.
Thus a login node or batch shell cannot start work: enter an srun step first.
The inherited child affinity also restricts the command to those two CPUs.

A shared-home flock at `~/.stafford38-guard/<cluster>.lock` serializes campaign
allocations per cluster, independently on the two clusters. It stays held until
all owned live descendants drain. Linux subreaper adoption accounts for
session-escaped and double-forked descendants; pidfd signals avoid PID reuse.
The adapter signals owned descendants only. Foreign Lean/Lake processes block
only when their cgroup matches our allocation, so another allocation is ignored.

Inherited limits: aggregate RSS 8 GiB; node reserve max(8 GiB,5% total);
startup requires cap+reserve; PSI full>=1 or some>=10; swap growth>=1 GiB;
disk >=100 GiB startup and >=50 GiB during work, on cwd and STAFFORD_STORAGE
(default shared home). Polling is 250 ms, progress JSON every two seconds,
terminal command receipt includes allocation ID/cgroup and drained-child status.
As with the source local guard, startup refusal emits stderr/exit 96 rather than
a terminal JSON receipt. This adapter does not assert cgroup hard RAM enforcement.

Behavioral validation:
`python3 docs/qwen-campaign/notes/slurm-guard-tests.py`
passed seven tests in 7.377 seconds. Actual minimal subprocesses independently
confirmed two-CPU affinity, propagated exit 7, timeout drain of an escaped
session child, signal drain/exit143 with progress receipt, and actual cross-process
flock contention. Controlled external disk/pressure readings caused expected
startup refusal and runtime stops. Placement checks reject foreign job cgroups,
login/protected names, and excessive affinity. No Slurm runtime was available:
actual shared-filesystem flock support and site cgroup spelling must be confirmed
by a controller-owned minimal allocation before proof jobs. This receipt is not
a proof or manuscript correspondence receipt.

Frozen SHA256:
- linux-slurm-guard.py: ca59b4b7c067851dca28aaff59b3919ec9224bda16a324fa2233d29d1c898506
- notes/slurm-guard-tests.py: 9a8b36f515767478f806969f58934b0ff33082f7d83ded1bea1d5e2f006197c5

Inside an already approved one-node allocation reserving 8G and two CPUs:
```sh
srun --ntasks=1 --cpus-per-task=2 --cpu-bind=cores python3 "$CAMP/linux-slurm-guard.py" check
srun --ntasks=1 --cpus-per-task=2 --cpu-bind=cores python3 "$CAMP/linux-slurm-guard.py" run --timeout 120 --log "$SCR/guard-smoke.log" --cwd "$WT" -- python3 -c 'import os; print(sorted(os.sched_getaffinity(0)))'
```
Set STAFFORD_STORAGE to the allocated check storage mount if distinct from home.
Do not set a synthetic SLURM environment to bypass refusal in production.
