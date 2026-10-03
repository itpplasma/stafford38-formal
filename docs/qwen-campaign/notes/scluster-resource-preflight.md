# sCluster resource preflight for Lean

Read-only preflight performed from the workstation on 2026-10-03 (CEST). No
job was submitted, and Lean was not run on a login node.

## Live scheduler and host evidence

`ssh scluster 'hostname -f; date -Is'` connected through the configured SSH
alias and returned `scluster.tugraz.at`, `2026-10-03T03:03:24+02:00`.
`ssh -G scluster` resolves the target to `scluster` with user `ert`; the
alias configuration supplies `ProxyJump faepmac1`. `faepmac1` is transit only.

`sinfo -o "%P|%a|%l|%D|%c|%m|%f"` showed one `compute` partition (default,
up): 20 nodes, 96 CPUs and 1,160,629 MB per node, unlimited wall time. The
Slurm node config reports 2 sockets × 48 cores and `ThreadsPerCore=1`, so
allocated CPUs are physical cores. `scontrol show nodes -o` listed
`node1`–`node20`; the records identify those as compute node hostnames. At
the snapshot, nodes 1–4 had 1, 1, 2, and 1 CPUs allocated respectively;
nodes 5–9 had none. A short listing showed the same node configuration across
the pool. `squeue -u ert` was empty.

The partition reports `MaxNodes=UNLIMITED`, `MaxCPUsPerNode=UNLIMITED`,
`MaxTime=UNLIMITED`, `OverSubscribe=NO`, and `DefMemPerNode=UNLIMITED` /
`MaxMemPerNode=UNLIMITED`. Physical capacity is 20 nodes × 96 CPUs and
1,160,629 MB per node. The visible QOS is `normal` with no displayed job,
submit, wall-time, or TRES caps. The association query using `sacctmgr
show assoc ... withassoc` failed because `withassoc` is not a valid field in
this Slurm installation, so no additional per-user association cap was
verified. The queue snapshot showed no current allocation for `ert`.

## RAM enforcement

`scontrol show config` reported Slurm 22.05.8 on the compute node records,
`SelectType=select/cons_tres`, `SelectTypeParameters=CR_CORE`,
`ProctrackType=proctrack/cgroup`, `TaskPlugin=task/cgroup,task/affinity`, and
`JobAcctGatherType=jobacct_gather/linux` with a 30-second sampling interval.
The active `/etc/slurm/slurm.conf` also sets `ProctrackType=proctrack/cgroup`
and `TaskPlugin=task/cgroup,task/affinity`. No `/etc/slurm/cgroup.conf` or
`slurm.d/*.conf` memory constraints were present at the inspected paths, and
the config query exposed no `ConstrainRAMSpace` setting. `jobacct_gather`
accounts for memory; this evidence does not establish a hard per-job RAM
limit. Since no job may be submitted during this preflight, enforcement
cannot be tested from a job cgroup. Treat the 8 GiB request as unproven for
hard enforcement and reserve CPU capacity accordingly.

The configured node ratio is 1,160,629 MB / 96 CPUs = about 11.82 GiB per
CPU (using 1 GiB = 1024 MiB). Thus `ceil(8 / 11.82) = 1` CPU-equivalent for
8 GiB. The minimum of two CPUs for Lean's two actual threads dominates, so
the bounded request is **2 CPUs total, with Lean restricted to 2 actual
threads, plus `--mem=8G` for Slurm accounting**. No ghost CPUs are needed at
this memory target. This stays within the user's instruction to reserve
`max(actual threads, ceil(8 GiB / usable GiB per CPU))`; it does not claim
that the memory request is enforced. Do not oversubscribe CPUs.

Recommended job request:

```bash
#SBATCH --partition=compute
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
```

Set Lean's worker/thread setting to 2 in the job. If a later verified
configuration establishes memory cgroup enforcement, retain this same
2-CPU/8-GiB request. If a usable per-CPU memory figure changes, recompute
`max(2, ceil(8 GiB / usable GiB per CPU))` before submitting.

## Toolchain, cache, and storage

The usual Lean installation path
`/home/ert/.elan/toolchains/leanprover--lean4---v4.35.0-rc3` and its `lean`
and `lake` executables were absent. `/home/ert/.cache/mathlib` was absent,
and a bounded search under `/home/ert/data` found no `lean-toolchain`,
`.lake/packages/mathlib`, or `Mathlib.olean` cache. Therefore neither Lean
v4.35.0-rc3 nor its Mathlib build cache is currently available in the
inspected sCluster user paths. No installation or download was attempted.

`df -h /home /tmp` reported the shared BeeGFS `/home` filesystem at 200 TiB
total, 76 TiB used, 124 TiB available (38% used). `/tmp` is on the login
node's 819 GiB root filesystem, with 648 GiB available. The compute node
configuration reports 900,241 MB temporary disk per node; no compute-node
filesystem was entered or modified during this preflight.

## Submission boundary

This is resource evidence only. Before any job, freeze the exact input tree
and its dependency/cache plan. Submit only the bounded two-thread job above
once the controller authorizes a concrete job; check live `squeue`, `sinfo`,
and node availability again immediately before submission.
