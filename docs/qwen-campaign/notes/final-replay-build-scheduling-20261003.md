# Final replay build scheduling audit

## Finding

The pinned Lean 4.35.0-rc3 / Lake `5.0.0-src+470d5ce` installation exposes no supported switch to cap Lake build tasks at one. The `lake build --help` output has no job/parallel/thread option. Its general `-K` option passes declared configuration values; the pinned `Lake.Build.BuildConfig` has no job-count field. Searching the exact pinned Lake source for job-limit/max-job controls found only total-job accounting and a `failFast` flag, not a concurrency bound. Do not add a guessed `lake build -j1`, `LAKE_JOBS=1`, or `-K maxJobs=1` to the replay.

The source explains why a shell-level sequential command list is insufficient. `Lake.Build.Run` keeps an array of registered `OpaqueJob`s, drains it as jobs are added, and scans all running/waiting jobs; it has no one-job semaphore. `Lake.Build.Module.prepareLeanCommand` creates spawn arguments using the absolute executable from `getLeanInstall` (`leanInstall.binDir/lean`), so putting a wrapper named `lean` earlier on `PATH` does not intercept Lake's module builds. `scripts/verify.sh` submits the complete retained-module list, aggregates, and solution/challenge targets in one `lake build`, which lets Lake discover and schedule their dependency DAG together.

The approved Linux guard remains useful but does not provide this missing scheduling limit. It pins the process group to two CPUs and exports `LEAN_NUM_THREADS=2`; this caps CPU placement/runtime threads per Lean process, not the number of external Lean processes Lake may spawn. Its 8 GiB process-group RSS cap stops an over-budget run and drains descendants. It protects the host; it cannot establish in advance that the aggregate peak will fit. The reported T35 peak of 7406 MiB leaves only about 786 MiB below the nominal 8 GiB cap, so a heavier overlap is a material uncertainty.

## Evidence inspected

- Pinned toolchain help: `/home/ert/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake --help` and `lake build --help` (help only; no build executed). Version banner: Lake 5.0.0-src, Lean 4.35.0-rc3.
- `src/lean/lake/Lake/Build/Context.lean`: `BuildConfig` contains `failFast` and logging/cache fields but no job limit; `JobQueue` is an `IO.Ref (Array OpaqueJob)`.
- `src/lean/lake/Lake/Build/Run.lean`: `drainQueue`, `scanJobs`, and the monitor loop account for all scheduled jobs and continue while any are unfinished; no concurrency gate.
- `src/lean/lake/Lake/Build/Module.lean`: `prepareLeanCommand`'s `mkSpawnArgs` sets `cmd := (← getLean).toString`, using the resolved toolchain path rather than PATH lookup.
- `scripts/verify.sh` lines 22–41 passes all retained modules and aggregate/solution targets to one Lake invocation.
- `docs/qwen-campaign/linux-guard.py` lines 209–211 and 278–285 sets two runtime threads/CPU affinity and enforces a separate RSS cap with terminal child-drain accounting.
- `docs/qwen-campaign/notes/cluster-final-replay-20261003.sh` keeps each build command as a single bounded stage; it does not currently set an unsupported Lake scheduler knob.

## Scheduling decision

There is no evidence-backed way to force the accepted pinned Lake build to one concurrent module task while preserving two allocated CPUs and `LEAN_NUM_THREADS=2`. Keep the accepted Lake command and guard unchanged for controller review. If the full verifier cannot be shown to fit the existing cap, pause before launch and request a separately reviewed change: either implement and test a source-compatible serial build driver whose outputs and coverage match the current verifier, or use a separately authorized resource profile. Splitting `lake build` into multiple shell commands, setting `--fail-fast`, reducing Lean threads, or adding an assumed environment/config key is not a verified concurrency bound.

No Lean build/proof, SSH, Slurm scheduling, or source/guard modification was performed for this audit.
