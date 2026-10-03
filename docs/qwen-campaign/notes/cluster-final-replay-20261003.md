# Linux cluster final replay candidate

This candidate adapts the approved Linux resource guard for `acluster` or
`scluster` after repeated local PSI refusals. It does not authorize or launch a
job. The controller supplies the eventual full public T70 commit and owns
resource inspection, Slurm submission, monitoring, and acceptance. The archived
mailuefterl driver and JSON contract remain unchanged.

The driver accepts an existing completed bootstrap run root under
`/home/ert/stafford38-campaign` and a full lowercase 40-hex source commit. The
run root is resolved strictly to an existing directory and must be a proper
descendant of the canonical campaign directory before any write. Traversal
and symlink escapes are rejected. The run root must already contain the isolated Lean toolchain, `bootstrap/elan`, a
staged `bootstrap/curl-runtime`, and the per-run XDG and Mathlib caches. Do not
reuse an active cache writer. It creates a new `final-source` checkout and a
separate `final-receipts` directory. It rejects patches, reused source paths,
dirty source trees, wrong Lean executable/githash, manifest drift, or any of
the ten package HEADs resolving away from their lock pins.

Before launch, the controller should review the frozen source and this driver,
check available node RAM/PSI/swap/disk with the existing guard, and ensure one
node/one task/two CPUs/8 GiB are accepted. The staged curl wrapper is probed
before Git fetch. No package installation or system modification is part of
this route.

The controller should stage this driver and the adjacent
`linux-slurm-guard.py` / `linux-guard.py` pair from the reviewed frozen source
into `RUN_ROOT/control`, record all three SHA256 values, and use those staged
copies so a moving checkout is not a runtime dependency. Inside the reviewed
Slurm allocation, the controller can use the existing guard with the following
shape (replace the run root and commit only after the controller has frozen
them):

```sh
RUN_ROOT=/home/ert/stafford38-campaign/REVIEWED_COMPLETED_BOOTSTRAP
FULL_T70_COMMIT=FULL_LOWERCASE_40_HEX_COMMIT
STAFFORD_OUTER_GUARD_LOG="$RUN_ROOT/final-outer-guard.log"
STAFFORD_STORAGE=/home/ert/stafford38-campaign \
  STAFFORD_OUTER_GUARD_LOG="$STAFFORD_OUTER_GUARD_LOG" \
  python3 "$RUN_ROOT/control/linux-slurm-guard.py" run \
    --timeout 21600 --log "$STAFFORD_OUTER_GUARD_LOG" --cwd "$RUN_ROOT" -- \
    bash "$RUN_ROOT/control/cluster-final-replay-20261003.sh" \
      "$RUN_ROOT" "$FULL_T70_COMMIT"
```

The source gate order is recorded in the JSON contract and ends with all four
comparators: main, fixed-source, alternative, and alternative fixed-source.
`bash scripts/verify.sh` remains the actual project verifier for module/source
policy and dependency routes; no fixture-only check replaces it. Every driver
command has a bounded log, argv and status receipt. `final-receipts/terminal.json`
is the driver result; the outer guard writes separate sibling `.json` and
`.progress.json` records. Success requires both layers to finish with status
zero, source and lock identity to match before and after, all package pins to
match, and the outer guard to confirm the expected allocation and drained child
group. A timeout, refusal, mismatch, or missing drain evidence is a failed
replay.

Local preparation checks include shell syntax, contract pin/order assertions,
and `python3 docs/qwen-campaign/notes/cluster-final-replay-behavior-20261003.py`.
That harness runs a temporary copy of the actual driver with fake Git, Lean,
Lake, curl, and comparator tools. It checks wrong source commit and Lean commit
rejection, a failing cache command's terminal stage/status, tracked content and executable
mode addition/removal detection after verification even when Git status ignores
mode differences (core.filemode=false behavior), plus a clean full pass with
identical tree/file/mode manifests and all four comparators in order. Negative
argument/root cases fail before file creation. These checks do not stand in for
the guarded cluster replay or any Lean proof run.

The manifest compares actual `lstat` executable bits with each Git tree mode;
Git status is an additional integrity check, not the mode oracle. The harness
executes missing/extra/invalid commit arguments and missing, file, root-equal,
outside, traversal-escape and symlink-escape run roots and confirms no
receipt or checkout directory was created. These are real disposable filesystem
and shell executions with fake external tools; no Lean, SSH or scheduler runs.

After the Mathlib cache stage, one `lake build
Stafford38.Geometry.SameWitness.CommonOpenEtale` stage compiles the heavy
dependency before the authoritative full verifier. Accepted T35 peaked at
7406 MiB, leaving 786 MiB below the unchanged 8 GiB cap; the pinned Lake
audit found no supported job limit. The verifier can reuse this real build
trace. The full verifier, retained proof library and four comparators remain
in their existing order. Fake-tool behavioral checks assert the complete
external gate order and that a failing prebuild prevents every later gate.
