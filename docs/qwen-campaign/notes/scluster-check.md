# T43 sCluster fixture check

Prepared and submitted 2026-10-03 against the frozen campaign snapshot. The
single submitted job failed its allocation-affinity precheck before any Lean
download or fixture execution. T43 remains incomplete.

## Frozen input and toolchain

- Snapshot commit: `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`.
- Snapshot archive:
  `/Users/ert/proj/stafford38-qwen/.lake/qwen/cluster-inputs/base-0340cf2.tar`
- Archive SHA-256:
  `de34d3676ee6d3f61c05c944fb20064382f302aebbd210c0a8d652f06c1335aa`.
- Official GitHub release asset: `lean-4.35.0-rc3-linux.tar.zst`; release
  API digest `sha256:1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997`.
  The job rechecks this digest and requires `lean --version` to report RC3
  commit prefix `470d5ce`.
- The fixture test uses Lean from the standard path
  `~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean`. The job
  creates that path only if absent and fails closed if a present toolchain
  does not meet the version check.

## Guard and job request

The MAIN guard is
[`cluster-guard.py`](/Users/ert/proj/stafford38-formal/docs/qwen-campaign/cluster-guard.py),
200 lines. It requires one node and one task in a Slurm job, checks allocated
CPUs against two actual threads and the memory-equivalent floor, binds the
guarded command to two CPUs from its inherited allocation affinity, sets
Lean/OMP/OpenBLAS/MKL thread variables to two, and monitors aggregate RSS for
the guarded process group every 250 ms. It stops its process group on an 8
GiB RSS cap, timeout, SIGTERM, or SIGINT; checks for live descendants before
writing the atomic terminal JSON. The receipt includes actual affinity,
Slurm memory request, available/total memory, disk space, and the cgroup
resolved from `/proc/self/cgroup`. An unresolved job cgroup is recorded as
`unknown`.

The Slurm request is one node, one task, two CPUs, 8 GiB, and 60 minutes in
partition `compute`. `srun --ntasks=1 --cpu-bind=cores` starts the guarded
step within the Slurm CPU binding. The guard's inner timeout is 3500 seconds.
Both curl's retry/time limits and Slurm's job limit bound the download/install sequence.
The guard wraps the full preparation, toolchain download and unpack, version
check, and fixture test, so affinity and RSS observation cover all of it.

## Exact staged files

Temporary staging directory:
`/Users/ert/proj/stafford38-qwen/.lake/qwen/scluster-t43-20261003/`.

| File | SHA-256 |
| --- | --- |
| `cluster-guard.py` (MAIN path above) | `a688f24756fd92523c6506b0cf30538ff0a3b696d76385a228b3c1e573fd704d` |
| `t43.sbatch` | `cb1f2caa3f4d632b380a4bd28207f7613da990f8cb7245cf3da456abe2d345b8` |
| `run-t43.sh` | `19b1b3d12c2ac82758906a7f255ae94724daaab4b695d8e8f43f875c78a2ca65` |
| `prepare.sh` | `15fad3dfe2c60bd1123173ebd75f8703f94beb03d970c2bd4c8628f5dfa92cf1` |

The intended remote work tree is
`/home/ert/stafford38-campaign/20261003-T43-0340cf2-de34d3676e`. On
`scluster.tugraz.at`, a read-only SSH check confirmed `$HOME=/home/ert`,
verified `/home` capacity, and found this destination absent. The prepare
script checked that the SSH account home is `/home/ert`, that the exact
destination does not already exist, and that the frozen archive hash matches;
it then copies only the archive and three scripts, and checks their remote
syntax and archive/script checksums. Remote `bash -n` passed for both job
scripts. A fresh queue check immediately before submission found no `ert`
jobs; `compute` was up with 1,893 of 1,920 CPUs idle. The remote tree has been
populated with the approved artifacts.

The approved bundle was submitted once with
`ssh scluster 'cd /home/ert/stafford38-campaign/20261003-T43-0340cf2-de34d3676e && sbatch t43.sbatch'`.
Slurm returned job ID **3090343**. The job runs exactly
`python3 tests/dependency-guard-fixtures/test_behavior.py` from the frozen
source extraction. The expected terminal evidence is `receipts/guard.json`,
`receipts/job-status.json`, the log, Lean version output, and the fixture's
`PASS:` line. The actual run stopped before those outputs could be produced.

## Job 3090343 result

The job failed immediately on `node12` with exit code `1:0`; it was not
requeued and has zero restarts. Slurm records one node, one task, two CPUs,
`CPU_IDs=0-1`, and `MinMemoryNode=8G`. The guard process inside the `srun`
step saw `SLURM_CPUS_ON_NODE=2` and reservation 2 but only one CPU in its
effective process affinity, and correctly failed closed:

```text
allocation too small: allocated=2, reserved=2, affinity=1, actual=2
srun: error: node12: task 0: Exited with exit code 1
```

The atomic `receipts/job-status.json` records job ID, host, and exit code.
There is no `receipts/guard.json` or preflight file because the allocation
check failed before launching the guarded command. The exact `.err` log and
all source/toolchain directories remain in the unique remote tree. No Lean
asset was downloaded, no Lean binary was installed or run, and the behavioral
fixtures did not execute. This job did not establish memory cgroup enforcement.
No retry or replacement job has been submitted.

Local preparation checks were limited to Python syntax compilation and
`bash -n`; they did not run Lean or the fixture test. Job `3090343` is terminal
failed; its files and logs are retained for review.
