# sCluster Linux resume preflight

Read-only controller preflight, 2026-10-03. No allocation was submitted, no
toolchain or cache was installed, and Lean was not run. The current
workstation could not reach sCluster directly; this note combines that failed
live attempt with the earlier read-only resource snapshot in
`scluster-resource-preflight.md` and the job-3090343 record in
`scluster-check.md`.

## Live access attempt

`getent hosts scluster.tugraz.at` resolved `129.27.124.239`. The current SSH
configuration has no `scluster` host entry and `ssh -G scluster` resolves the
literal hostname `scluster` with no jump host. Direct read-only access was
attempted with:

```sh
timeout 12 ssh -vv -o BatchMode=yes -o ConnectTimeout=8 \
  -o ProxyJump=none scluster.tugraz.at 'hostname -f'
```

TCP connection to `129.27.124.239:22` timed out. This preflight did not use
`faepmac1` as a jump host. Current partition state, account limits, node
telemetry, toolchain/cache state, and scratch paths therefore remain
unverified for this resume.

## Prior scheduler and machine evidence

The earlier sCluster snapshot (2026-10-03 03:03 CEST, see
`scluster-resource-preflight.md`) reported the `compute` partition up with 20
nodes, 96 physical CPUs and 1,160,629 MB per node; no time limit; no
oversubscription; and node names `node1` through `node20`. It reported
Slurm 22.05.8, `select/cons_tres`, `task/cgroup,task/affinity`, and
`proctrack/cgroup`. The cgroup configuration did not establish hard memory
enforcement. The measured ratio was about 11.82 GiB per CPU, so two reserved
CPUs cover an 8 GiB job with 10% headroom while Lean uses two actual threads.
The association-cap query had failed, so account limits were not established.

That snapshot found no Lean 4.35.0-rc3 installation, no Mathlib cache, and no
matching toolchain/cache in the inspected `/home/ert` and `/home/ert/data`
paths. `/home` was BeeGFS with 124 TiB available; `/tmp` was the login-node
root filesystem with 648 GiB available. Compute-node temporary storage was
reported as 900,241 MB, but no compute-node filesystem was inspected. These
are historical observations, not a current availability guarantee.

Job 3090343 requested one node/task, two CPUs and 8 GiB. Its `srun` step had
only one CPU of effective affinity because `-c2` was omitted. The guarded job
refused before Lean/toolchain download. Every retry must pass the CPU count
explicitly to `srun` and verify a two-CPU effective affinity before any
command starts.

## Guard and placement requirements

The untracked `docs/qwen-campaign/cluster-guard.py` was inspected read-only.
It checks one node/task, Slurm memory request, CPU reservation and affinity;
uses two CPUs for the guarded process; caps aggregate RSS at 8 GiB; polls
node available RAM, PSI and swap; enforces an 8 GiB or 5%-of-node reserve;
and records disk free space. It does **not** enforce a disk free-space
threshold before or during the command. Do not treat its disk measurements as
a disk guard. The required disk guard must be supplied and reviewed by the
controller before submission; do not alter or stage this unrelated untracked
file as part of this task.

The prior node listing used generic names `node1`–`node20`, with no
`faepop*`/`faepcr*` names recorded, but the mapping is stale and does not prove
current placement eligibility. Before submission, a successful fresh
`scontrol show nodes -o` inspection must map actual Slurm node names to
hostnames. Exclude any node mapped to a protected `faepop*` or `faepcr*` host
using explicit Slurm node names. If mapping or exclusion cannot be verified,
do not submit. Inspecting the allocated hostname after scheduling is too
late to establish this restriction.

Once direct read-only access works, refresh at least:

```sh
ssh -o ProxyJump=none scluster.tugraz.at 'hostname -f; date -Is'
ssh -o ProxyJump=none scluster.tugraz.at 'sinfo -o "%P|%a|%l|%D|%c|%m|%f"; squeue -u ert'
ssh -o ProxyJump=none scluster.tugraz.at 'scontrol show config; scontrol show nodes -o'
ssh -o ProxyJump=none scluster.tugraz.at 'command -v lean lake || true; ls -ld ~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3 ~/.cache/mathlib /home/ert/data 2>/dev/null; df -h /home /tmp'
```

Recheck live partition/account limits, eligible-node RAM-per-CPU with 10%
headroom, RAM reserve, current node pressure/swap, scratch capacity, and
toolchain/cache availability. Never install on the login node. Keep source and
cache isolated in a unique job directory and freeze the exact source archive,
package pins and hashes before allocation.

## Bounded job recipe after controller preflight

Subject to fresh live evidence and the reviewed disk guard, the prior
two-thread/8-GiB budget translates to:

```sh
#SBATCH --partition=compute
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --time=01:00:00
#SBATCH --exclude=<explicit Slurm node names mapped to faepop*/faepcr*>

srun --ntasks=1 --cpus-per-task=2 --cpu-bind=cores \
  python3 /absolute/MAIN/docs/qwen-campaign/cluster-guard.py \
    --cwd /unique/job/source --timeout 3500 --threads 2 \
    --rss-cap-gib 8 --summary /unique/job/receipts/guard.json \
    --progress /unique/job/receipts/progress.json -- \
    <approved-check-command>
```

`--exclude` must contain only verified Slurm node names and must be omitted
only if the refreshed inventory establishes that there are no protected
hosts in the eligible partition. Keep `LEAN_NUM_THREADS`, `OMP_NUM_THREADS`,
`OPENBLAS_NUM_THREADS`, and `MKL_NUM_THREADS` at two (the guard sets these
for its child). Retain the separate disk-space guard, immutable source/cache
isolation, and live progress monitoring. Require two CPUs in both the batch
allocation and the `srun` step, 8 GiB requested memory, actual affinity of
two CPUs, RSS below 8 GiB, node RAM/PSI/swap checks, disk guard, and a complete
terminal receipt before accepting any check.

## Readiness

**Not ready for controller submission.** Direct SSH is currently unreachable;
fresh scheduler and protected-host mapping are missing; cgroup memory
enforcement remains unverified in the prior snapshot; and the inspected
untracked guard has no enforcing disk threshold. No job or Lean command was
run. After these points are resolved, the controller can authorize a bounded
check using the recipe above.
