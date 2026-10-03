# aCluster Linux resume preflight

Read-only preflight on 2026-10-03 (CEST), following the owner's execution
policy: proof checks may run on local mailuefterl Linux and Linux acluster or
scluster only; never on Macs. This worker inspected only SSH alias `acluster`
(`ert@acluster.tugraz.at`, `hostname -f` = `acluster.tugraz.at`). No job was
submitted, no software was installed, and no Lean command was run. The
controller owns any later staging, submission, monitoring, and receipts.

## Scheduler and account

Read-only commands used:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 acluster 'hostname -f; sinfo -h -o "%P|%a|%l|%D|%C|%N"; scontrol show config; sacctmgr -n -P show assoc where user=ert format=Cluster,Account,User,Partition,QOS,MaxWall,MaxTRES,MaxTRESPerJob; sacctmgr -n -P show qos format=Name,MaxWall,MaxTRES,MaxTRESPerJob'
ssh -o BatchMode=yes -o ConnectTimeout=10 acluster 'scontrol show partition compute; sinfo -h -N -p compute -o "%N|%T|%c|%m|%e|%f"'
```

Slurm is 22.05.8. The `compute` partition is up with 34 nodes (`node1` to
`node34`), 2,176 CPUs, and unlimited partition time, nodes, and CPUs per node.
At inspection it showed 977 allocated, 1,135 idle, and 64 unavailable CPUs;
`node14` through `node20` were idle. Nodes `node7`, `node8`, `node12`,
`node25`, and `node29` were unknown or down and are not eligible. Every listed
node reports 64 CPUs and `RealMemory=967404` MiB, about 14.76 GiB per CPU.
The current `FreeMem` values vary, so the live RAM guard must make the final
start decision after allocation.

`compute` allows all accounts and QOS values; `MaxTime=UNLIMITED`, and the
partition has no configured memory maximum. The association query returned
no rows for `ert`; the visible `normal` QOS row had no maximum fields. No
account-specific ceiling was established by these read-only queries. The
partition is `OverSubscribe=NO`. `SelectType=select/cons_tres`,
`ProctrackType=proctrack/cgroup`, and `TaskPlugin=task/cgroup,task/affinity`.
The prior resource inspection found `/etc/slurm/cgroup.conf` does not enable
`ConstrainRAMSpace`; consequently `--mem=8G` reserves scheduler memory but
does not prove a hard cgroup kill limit. The job guard must enforce the
aggregate RSS cap itself.

## Hosts, filesystems, toolchain

The compute partition's complete configured host list is `node[1-34]`; none
are named `faepop*` or `faepcr*`. Keep that restriction explicit at
submission: refresh `sinfo -N -p compute`, validate the candidate hostnames
against `^node[0-9]+$`, and pass only those exact eligible hostnames using
`--nodelist`. Do not rely on a Slurm wildcard exclusion or a partition-wide
placement. This prevents an allocation on any protected host even if future
partition membership changes.

Read-only path/tool commands used:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 acluster 'for x in elan lean lake; do command -v "$x" || true; done; for p in "$HOME/.elan" "$HOME/.cache/mathlib" "$HOME/.cache" /scratch /tmp /var/tmp; do if test -e "$p"; then ls -ld "$p"; df -hP "$p" | tail -1; else printf "ABSENT %s\\n" "$p"; fi; done; du -sh "$HOME/.cache/mathlib" 2>/dev/null; df -hP "$HOME" / /tmp /var/tmp'
```

No `elan`, `lean`, or `lake` is in `PATH`; `/home/ert/.elan` and `/scratch`
are absent. `/home/ert/.cache/mathlib` exists (425 MiB of `.ltar` files), but
its compatibility with the pinned Lean v4.35.0-rc3 and manifest cannot be
established from filenames. Leave it untouched. `/home` is BeeGFS with 27
TiB available at inspection; `/` has 171 GiB free. `/tmp` and `/var/tmp`
exist on the login host, but compute-node temporary storage was not checked.
Use a fresh persistent run tree under `/home/ert/stafford38-campaign/<run-id>`
for the frozen source, per-run elan home, XDG and Mathlib caches, Lake package
sources/build output, logs, and receipts. Do not share writable trees between
allocations or use the existing home cache. Any toolchain/bootstrap work must
occur only inside the guarded allocation, after the controller approves the
inputs and guard.

## Bounded job shape for a later controller run

The current node ratio means two reserved CPUs cover the two actual threads
and the 8 GiB job budget with the plan's 10% headroom. Use one allocation,
one task, two CPUs, 8 GiB requested memory, and at most 120 minutes. Submit
only one acluster job at a time; the mailuefterl `/tmp` slot is host-local and
cannot serialize cluster jobs. Refresh and validate the node allowlist
immediately before submission; the idle list below is only the observation
from this preflight.

```bash
# In the future controller-owned sbatch script, after validating the live
# node allowlist and selecting only nodeN names:
#SBATCH --partition=compute
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --time=02:00:00
#SBATCH --nodelist=node14,node15,node16,node17,node18,node19,node20

RUN=/home/ert/stafford38-campaign/<run-id>
mkdir -p "$RUN/logs" "$RUN/progress" "$RUN/elan" "$RUN/xdg-cache" "$RUN/mathlib-cache"
df -PB1 "$RUN"   # require at least 100 GiB before work; maintain 50 GiB while running
srun --nodes=1 --ntasks=1 --cpus-per-task=2 --cpu-bind=cores \
  python3 "$RUN/cluster-guard.py" \
    --cwd "$RUN/project" --timeout 6900 --threads 2 --rss-cap-gib 8 \
    --summary "$RUN/logs/terminal.json" --progress "$RUN/progress/live.json" \
    -- <controller-reviewed command>
```

Set `ELAN_HOME`, `XDG_CACHE_HOME`, and the supported Mathlib cache directory
to the per-run directories in the reviewed launch script; keep `HOME` intact.
The `srun` step requests two bound CPUs so affinity is observed inside the
allocation. The cluster guard draft checks one node/task, two-CPU affinity,
the 8 GiB aggregate process-group RSS cap, node RAM reserve, PSI when
available, and no more than 1 GiB additional node swap; it polls every 250 ms
and records telemetry every two seconds. Its reservation check also requires
at least `max(2, ceil(8 / (0.9 * node GiB per CPU)))` CPUs.

## Submission readiness

The scheduler and protected-host checks support this small allocation shape,
but this preflight does **not** clear a Lean run for submission. The read-only
`docs/qwen-campaign/cluster-guard.py` draft has no 100 GiB startup or 50 GiB
live disk refusal/check, although the campaign plan requires both. It also
does not acquire a cross-job cluster slot; the controller must keep exactly
one acluster allocation pending/running. The login host has no pinned Lean
toolchain, and compute-node scratch/network/toolchain availability is not
established. Before a Lean submission, the controller should add or supply a
reviewed cluster disk guard, freeze the exact source/cache inputs under the
isolated run tree, and arrange any bootstrap only inside the guarded job.

This is resource evidence only. It does not verify Lean, the frozen source,
or any proof result. No file outside this assigned note was changed.
