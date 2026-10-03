# aCluster resource preflight

Read-only preflight on 2026-10-03 (CEST), requested for the Stafford Lean campaign. SSH alias `acluster` resolves to `ert@acluster.tugraz.at`; remote `hostname -f` confirmed `acluster.tugraz.at`. No batch job was submitted and no Lean command was run.

## Scheduler and limits

The host runs Slurm 22.05.8. `sinfo` reported the `compute` partition up, 34 nodes, 2,176 CPUs total, with 1,008 idle, 1,104 allocated and 64 unavailable/other. `squeue -u ert` was empty. Nodes are `node1` through `node34`; responsive idle examples at the check were `node14`, `node15`, `node17`, `node19`, and `node20`. `node7`, `node8`, `node12` and other nodes were `UNKNOWN+NOT_RESPONDING`; do not count those as capacity.

The CPU nodes report 64 CPUs (64 physical cores, one hardware thread per core) and `RealMemory=967404` MiB each. The `compute` partition has `MaxCPUsPerNode=UNLIMITED`, `MaxNodes=UNLIMITED`, and `OverSubscribe=NO`. No finite per-job ceiling was exposed by the controller. `AccountingStorageEnforce=none`; `sacctmgr show assoc where user=ert` returned no association rows, and the visible `normal` QoS row had no populated maximum fields. Thus there is no account-level maximum established by this read-only query; the hardware ceiling for a single node is 64 CPUs and 967404 MiB, while the partition itself permits multi-node jobs.

## Memory control and filesystem

`SelectType=select/cons_tres` permits Slurm to account for requested memory when placing jobs. Slurm reports `ProctrackType=proctrack/cgroup`, `TaskPlugin=task/cgroup,task/affinity`, and cgroup automount enabled. However, `/etc/slurm/cgroup.conf` contains only `ConstrainCores=yes` and `ConstrainDevices=yes`; it does not enable `ConstrainRAMSpace`. `DefMemPerNode` and `MaxMemPerNode` are both `UNLIMITED`. Therefore `--mem=8G` is a scheduler reservation, but this configuration does not establish an 8 GiB job memory kill limit. No compute job was started to probe a live job cgroup.

Remote `/home` is BeeGFS: 182 TiB total, 27 TiB available (86% used). `/` had 171 GiB available. `/scratch` is absent; `/tmp` and `/var/tmp` exist on the login host, but no compute-node scratch capacity was checked.

## Lean and cache

The target worktree pins `leanprover/lean4:v4.35.0-rc3` (checked locally at `/Users/ert/proj/stafford38-qwen/lean-toolchain`). On aCluster, `elan`, `lean`, and `lake` were not found in `PATH`; `~/.elan` and its toolchain directory do not exist, and no Lean or Lake executable was found under the account home in the bounded search. `~/.cache/mathlib` exists and occupies 425 MiB of `.ltar` archives, but without the toolchain or project checkout its compatibility with the pinned Lean/Mathlib revisions cannot be established. No install, download, or cache mutation was attempted.

## Bounded initial allocation recommendation

For the first Lean job, request one task, two CPUs, and 8 GiB:

```bash
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
```

Run Lean with at most two actual threads. A node provides about 14.76 GiB per CPU (`967404 MiB / 64`); accounting for 8 GiB by the requested rule gives `ceil(8 / 14.76)=1` CPU. The two actual CPUs already exceed that reservation, so reserve exactly two, with no oversubscription. Because RAM is not shown as constrained by cgroups, the 8 GiB request controls placement only; the job must remain bounded to this small first run, and its actual peak memory should be observed before any larger allocation is considered.
