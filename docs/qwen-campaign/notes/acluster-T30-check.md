# aCluster T30 resource check (final inputs prepared; launch held)

Current status: the final-input bundle described below is staged but held because the shared resource guard is being extended with node memory, pressure, and swap checks. It was not submitted and will remain preserved. A fresh unique remote tree will carry the final frozen guard once available.

Prepared on 2026-10-03 for the T30 module build and trust-zero consumer check. This is a cluster-only check; it does not promote the candidate or establish whole-proof correspondence. No source edits, package-pin changes, `lake update`, login-node compilation, or Slurm submission were made.

## Final frozen input

- Base source commit: `e2ba158be31b7819a7cdeff22d0ceb9f6bf72a30` (accepted T22 included).
- Archive: `/Users/ert/proj/stafford38-qwen/.lake/qwen/cluster-inputs/T30-e2ba158-final.tar`.
- Archive SHA-256: `bc3fa4ab358aaa25cc6168009050e3ae997c0f967364c1d61886f44b7035f1cb`.
- Candidate `Stafford38/Geometry/SameWitness/ChartSetup.lean`: `a8107782808a6839e9dcddf85e0b364cca92675a84d442220d4b68287a85323a`.
- Consumer `tests/SameWitness/ChartSetupConsumer.lean`: `dacfb08ad15a8b6cfa52760d4597d1ffc58226b822b3b862878cbd05e2b36f89`.
- `lake-manifest.json` SHA-256: `29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc`; `lean-toolchain` is `leanprover/lean4:v4.35.0-rc3`.

The frozen manifest contains these ten package revisions; the run script records and checks each fetched package HEAD before the target module build:

```text
algebraicAnalysis bbbbf3fc358ca8100b158cec4cf47f336ab70163
mathlib c55e6e786f49471c72fbddbec5415808896aec1e
plausible fb13df72ecefd8ddbf9291021d7f33a8673eb57b
LeanSearchClient 29ff470276c725ae01505d55b17148c18fc7dfd3
importGraph 7e81a29bda33a6b257bd37557a6aa6aebe175d96
proofwidgets c643bbb3c24f8a25f9c14e3a6b1ceb13d01f3de1
aesop a90fbf7b02ff06a0deebf74088dff9e5fe02c9ea
Qq 37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9
batteries 3b7c8101932390d60e92a3f3d917901d5b5a773b
Cli 843844fa601dd56767b1eb22b7ada5b64d5e567a
```

## Currently held final-input staging

The currently held aCluster tree is `/home/ert/stafford38-campaign/20261003-T30-e2ba158-bc3fa4ab`; its shared guard predates the requested node-pressure enhancement, so this tree is not the submission target. The previous prepared tree `20261003-T30-0340cf2-780bab5` remains intact as a superseded, never-submitted snapshot. The final tree contains the exact input archive, both launch scripts, and the unchanged controller-approved resource guard.

Local script directory: `/Users/ert/proj/stafford38-qwen/.lake/qwen/scripts/remote/20261003-T30-e2ba158-bc3fa4ab`.

- `run-t30.sh` SHA-256: `ef934398cc61e1189c6483d43e21ec148149247f6d29af926beebdc17bee0370`.
- `T30.sbatch` SHA-256: `1a33b283d25055c15ade131bfb8be8d97a8c3d7a7e9008661a5f22442d34b0f7`.
- `cluster-guard.py` SHA-256: `a688f24756fd92523c6506b0cf30538ff0a3b696d76385a228b3c1e573fd704d` (copied unchanged from `docs/qwen-campaign/cluster-guard.py`).

The request is one `compute` node, one task, two CPUs, 8 GiB, and 120 minutes. `srun --ntasks=1 --cpus-per-task=2 --cpu-bind=cores` starts the guard so its recorded affinity comes from the Slurm allocation. The guard allows 6,900 seconds, two actual threads, and 8 GiB aggregate process-group RSS. The run uses a unique persistent project, elan toolchain, XDG cache, Mathlib cache, Lake package sources, and build output under the final remote tree so Linux artifacts remain available after the job. It does not override `HOME`; the existing `~/.cache/mathlib` remains untouched. The run records the elan installer hash, `lean --version`, and SHA-256 of the installed Lean binary, requiring Lean commit prefix `470d5ce`. It verifies the archive, candidate and consumer hashes, exact toolchain pin, manifest hash, and every package HEAD; runs `lake exe cache get`, builds `Stafford38.Geometry.SameWitness.ChartSetup`, then runs `lake env lean --trust=0 -M 8000 tests/SameWitness/ChartSetupConsumer.lean`. It does not invoke `lake update` and rechecks the manifest hash before reporting PASS.

The command for this superseded staging tree is recorded for provenance only:

```bash
ssh acluster 'sbatch /home/ert/stafford38-campaign/20261003-T30-e2ba158-bc3fa4ab/T30.sbatch'
```

Submission remains held until a fresh tree has the controller-reviewed guard and matching hashes.
