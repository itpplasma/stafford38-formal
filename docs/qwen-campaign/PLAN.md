# Qwen campaign: Stafford 3.8 paper-route correspondence

This file is the work order for a serial campaign carried out by Pi running
Qwen3.8-Flash-Next (`itpcp/local`). Claude (the controller) and the owner
steer it. Pi performs the tasks itself, one task per run.

Campaign folder (absolute): `/Users/ert/proj/stafford38-formal/docs/qwen-campaign`

| Name | Path |
| --- | --- |
| `MAIN` | `/Users/ert/proj/stafford38-formal` (controller checkout, branch `main`; do not edit Lean here) |
| `WT` | `/Users/ert/proj/stafford38-qwen` (campaign worktree, branch `qwen/paper-route`; all Lean edits go here) |
| `CAMP` | `$MAIN/docs/qwen-campaign` (this plan, `STATE.md`, `guard.sh`, notes) |
| `ARCH` | `$MAIN/docs/audits/paused-2026-10-02` (archived failed candidates; read-only) |
| `SCR` | `$WT/.lake/qwen` (scratch files, extracted archives and logs; never committed) |
| `GUARD` | `$CAMP/guard.sh` |

## 0. How every run works

1. Read sections 0–4 of this file completely. Then read `$CAMP/STATE.md`.
2. Pick the first task in `STATE.md` whose status is `todo` or `retry`.
   Never pick a later task, and never work on two tasks in one run.
3. Read that task's section in this file (sections 5–14) completely.
4. Do exactly what the task says, in its order. Read the files the task names
   before editing them.
5. Check the task's acceptance criteria yourself, with the commands given.
   Lean checking and build runs always go through `GUARD` (section 3).
6. Update `STATE.md` (section 4): status, attempt count, log path, one-line
   note. If the task is `done` and changed files in `WT`, commit them on the
   `qwen/paper-route` branch, staging explicit paths only (section 2.4).
7. End the run with the report block from section 4.3. Then stop. Do not start
   the next task.

If a task's **Stop if** condition fires, or the same error appears after three
different repair attempts, set the task to `blocked`, write what you tried and
the exact first error into `$CAMP/notes/<task-id>-blocked.md`, and stop. The
controller reads it and either changes the plan or gives a hint in `STATE.md`
under "Controller hints". Always read the hints for your task before you start.

Owner gates (tasks marked **OWNER GATE**) are never executed by Pi. When the
first open task is an owner gate, report `WAITING_FOR_OWNER` and stop.

## 1. Goal and end state

The terminal Lean theorem of Stafford Conjecture 3.8 is already proved, but
its geometric core uses an older route (generic-divisor/Laurent axis via
`exists_groundConormalAxis_of_prime_coordinate_avoidance`). Johanna's paper
argues through one retained witness: normalization chart, same-witness
ground point, étale coordinates, a tilted axis lift, common-open columns and
a tangent limit. Most of those parts are already proved as separate
theorems under explicit inputs. The campaign must:

1. prove the **same-witness affine-fibre closure** unconditionally (Phase 3);
2. prove the **original-prime wrapper** from it (Phase 4);
3. make the existing theorem
   `Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`
   use that route, **without changing its statement** (Phase 4);
4. pass the strict dependency guard, the full repository verifier, the Linux
   replay and the Palomar comparisons (Phases 5 and 7);
5. prepare the review bundle and release material (Phases 8 and 9; owner
   gates apply).

The mathematics is settled. The difficulty is Lean engineering: one proof
installed about forty local `Algebra`/`SMul` instances with `letI` on heavy
concrete types. Lean then found two different scalar actions of
`MvPolynomial (Fin m) k` on the common-open ring `U`, and elaboration timed
out (section 7 has the exact errors). The campaign replaces that monolith
with small top-level lemmas over abstract types.

## 2. Hard rules

### 2.1 Proof integrity

- Never write `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `@[irreducible] def` on challenge definitions, or
  `set_option debug.skipKernelTC`.
- Never change the statement of anything in `Challenge.lean`,
  `FixedSourceChallenge.lean`, `CorollaryChallenge.lean`,
  `PaperPairChallenge.lean`, `Solution.lean`, `FixedSourceSolution.lean`, or
  of any existing theorem the task does not explicitly allow you to change.
- Never weaken a target statement or add a hypothesis to it. If the target
  seems false or needs an extra hypothesis, that is a **Stop if** condition.
- Never add a hypothesis that assumes what the closure is supposed to prove
  (smoothness of the chart, column identities, numerator vanishing, closure
  membership, "f avoids M"). The archived frontier calls these forbidden
  inferences.
- `maxHeartbeats`: a file may keep the value already in its header. New files
  use at most `set_option maxHeartbeats 1600000`. Never raise a limit to get
  past a timeout. A timeout means the proof must be split (section 6.3).
- Every new theorem used by a later task gets a consumer in `WT/tests/`
  that restates the theorem's statement literally, proves it by applying the
  theorem, and runs `#print axioms`. The only allowed axioms are `propext`,
  `Classical.choice`, `Quot.sound`.

### 2.2 Files you may touch

- Each task lists its owned files. Edit only those. Creating a file counts as
  touching it.
- In `MAIN` you may edit only `$CAMP/STATE.md` and `$CAMP/notes/*`. Never
  edit `PLAN.md`, `guard.sh`, or anything else in `MAIN`.
- Never edit files under `.lake/packages/` (Mathlib, AlgebraicAnalysis).

### 2.3 Machines

- Run everything on this machine (faepmac1) unless a task names another host.
- Never connect to, run on, or schedule anything on `faepop*` or `faepcr*`.
- `mailuefterl` is used only in Phase 7, only by the tasks that name it.

### 2.4 Git

- Commit only in `WT` on branch `qwen/paper-route`, only after a task is
  `done`, staging explicit paths: `git -C $WT add <path> <path>`, then
  `git -C $WT commit -m "<task-id>: <what was proved>"`.
- Never push, tag, rebase, `reset --hard`, `clean`, `stash`, delete branches
  or remove worktrees. Never commit in `MAIN`.

### 2.5 Searching before writing (no duplication)

Before you define anything or prove a helper lemma:

1. Search Mathlib: `grep -rn "<key words>" $WT/.lake/packages/mathlib/Mathlib | head -20`,
   and in a scratch file try `exact?` / `apply?` on the goal.
2. Search AlgebraicAnalysis: `$WT/.lake/packages/algebraicAnalysis/AlgebraicAnalysis`.
3. Search the repository: `grep -rn "<name or key words>" $WT/Stafford38 | head -20`,
   and check `$WT/docs/definition-owners.md`.
4. If something equivalent exists, use it. Write in `STATE.md` which existing
   declaration you reused.
5. A new `def`, `structure` or `abbrev` needs a one-line entry in
   `$CAMP/notes/new-definitions.md`: name, file, why no existing owner fits.
   The controller moves accepted entries into `definition-owners.md` later.

### 2.6 Readable Lean

- Name by mathematical content, never by provenance. Forbidden in new names:
  `Actual`, `Canonical`, `Corrected`, `Repair`, `Option` (unless the type is
  `Option`), `Luna`, `Wave`, dates, task ids, `Adapter`, `Producer`,
  `Kernel`, `Helper`.
- New files for this campaign live in `Stafford38/Geometry/SameWitness/`.
- Every top-level theorem gets a docstring: one sentence of mathematics and
  the paper location if the task gives one.
- A proof longer than about 60 lines is split into named lemmas.
- No `letI`/`haveI` of `Algebra`, `SMul`, `Module` or `IsScalarTower` inside
  a proof about concrete heavy types. Follow the rules in section 6.
- Keep the existing file style: `module` header, `public import`,
  `@[expose] public section`, `set_option autoImplicit false`, a namespace
  matching the path, `universe u`.

## 3. Resources: RAM, disk, time

This machine (faepmac1: 256 GiB RAM, 28 cores, ~550 GiB free on the data
volume) also serves the Qwen model you are running on. The model server
holds a large share of the RAM permanently (about 110–120 GiB of RAM is truly
free when idle). A Lean build that eats memory evicts your own model's
weights and stalls you. The Lean budget is therefore **64 GiB resident at
most**, with 8 Lean threads. Therefore:

- **Serial only.** At most one `lake` or `lean` process at any time. Never
  start a command in the background, never use `&`, `nohup`, `screen` or
  `tmux`. `GUARD` refuses to start when another `lake`/`lean` is alive.
- **Every** `lake build`, `lake env lean`, `scripts/verify.sh` or other
  Lean-invoking command runs through `GUARD`:

  ```sh
  $GUARD check          # prints memory/disk/swap; exit 0 means OK to build
  $GUARD run --timeout <seconds> --log $SCR/logs/<task-id>-<n>.log -- <command>
  ```

  `GUARD` refuses to start unless at least 60 GiB RAM is truly free, the
  kernel memory-pressure level is normal, swap use is below 12 GiB and at
  least 100 GiB of disk is free. It sets `LEAN_NUM_THREADS=8` and kills the
  whole process group when the build's resident memory exceeds 64 GiB, the
  kernel reports memory pressure (warn or critical), truly free RAM falls
  below 8 GiB, swap use reaches 12 GiB, free disk falls below 50 GiB or the
  timeout expires. It appends a summary line `GUARD exit=… reason=…
  wall_s=… peak_rss_gb=…` to the log. Set your shell tool's own timeout to
  the guard timeout plus 120 seconds.
- Standard timeouts: scratch file 900 s; one module `lake build` 2700 s;
  full library build 14400 s; `scripts/verify.sh` 21600 s.
- Single-file checks add a Lean memory cap:
  `lake env lean -M 32000 <file>` (the value is in MB).
- Exit codes and what to do:

  | Code | Meaning | Action |
  | --- | --- | --- |
  | 90 | refused at start | Run `$GUARD check`. If another lake/lean runs, it is not yours: stop, report `blocked: foreign lean process`. If memory/disk is low, stop and report. Never kill processes you did not start. |
  | 91 / 94 | memory or swap kill (`reason=rss-cap`, `memory-pressure`, `memory` or `swap`) | Do not retry the same command. Split the file or the proof (section 6.3) and report. Two memory kills in one task: `blocked`. |
  | 92 | disk kill | Stop immediately, report `blocked: disk`. Never delete anything to make room. |
  | 93 | timeout | Look at the log for the last file compiled. Usually a proof is too heavy: split it. Do not raise the timeout yourself. |

- **Disk hygiene.** The only new worktree in the whole campaign is `WT`
  (task T01). Its `.lake` is an APFS clone of `MAIN/.lake` and costs almost
  no extra space. Never run `lake clean`, `lake update`, `lake exe cache get`,
  `rm -rf .lake`, or anything that downloads toolchains or dependencies,
  unless a task says so. Keep logs in `$SCR/logs`. Logs larger than 50 MB:
  compress with `gzip` after reading what you need.
- **Context hygiene (your memory).** Never print a whole log or a whole large
  file. Use `grep -n "error" <log> | head -20`, `tail -40 <log>`,
  `sed -n 'A,Bp' <file>`. Read Lean files in pieces of at most 150 lines.
  Keep each tool output under about 200 lines.

## 4. STATE.md and run reports

### 4.1 Status values

`todo` → `doing` → `done`, or `retry` (controller reopened it), `blocked`
(needs the controller), `owner` (owner gate). Set `doing` at the start of
a run and change it before you stop.

### 4.2 Ledger row

Each task row in `STATE.md` has: id, status, attempts (runs used), last log
path, one-line note (what was proved or the first error). The task may also
ask you to record numbers (build time, peak memory) under "Measurements".

### 4.3 Report block (last thing you print)

```
TASK: <id> <title>
RESULT: done | blocked | WAITING_FOR_OWNER
CHANGED: <explicit file list, or none>
CHECKS: <command → result, one line each, with GUARD summary lines>
COMMIT: <hash or none>
NEXT: <next task id>
NOTE: <first error or reused declarations, max 5 lines>
```

## 5. Phase 0: set-up and baseline

### T00 Resource and state check

Owned: `$CAMP/STATE.md`.

1. Run `$GUARD check` and `df -h /System/Volumes/Data`.
2. Run `git -C $MAIN status --short | head` and `git -C $MAIN log -1 --format=%H`.
3. Record free memory, free disk and the `MAIN` commit under "Measurements".

Accept: `GUARD OK` printed. Stop if: `GUARD check` fails, or `MAIN` has
uncommitted changes outside `docs/qwen-campaign/`.

### T01 Create the campaign worktree

Owned: `WT` (new), `STATE.md`.

1. `test ! -e /Users/ert/proj/stafford38-qwen` (stop if it exists).
2. `git -C $MAIN worktree add -b qwen/paper-route /Users/ert/proj/stafford38-qwen main`
3. Clone the build cache without copying bytes. **Use the rc3 cache of
   `stafford38-rc3-final-worker`, not `$MAIN/.lake`** (MAIN's `.lake` still
   holds the old Lean 4.33 Mathlib `db584cd…`; lake would switch revisions
   and invalidate every Mathlib `.olean`):
   `cp -cR /Users/ert/proj/stafford38-rc3-final-worker/.lake /Users/ert/proj/stafford38-qwen/.lake`
   then make every package's git remote equal the URL in `lake-manifest.json`
   (`git -C .lake/packages/<name> remote set-url origin <url>`) so lake does not fetch.
4. `df -g /System/Volumes/Data` before and after; the difference must be
   below 2 GiB. If more than 2 GiB was used, stop and report.
5. `diff $MAIN/lake-manifest.json $WT/lake-manifest.json` and
   `cat $WT/lean-toolchain` must show identical manifests and
   `leanprover/lean4:v4.35.0-rc3`.
6. `mkdir -p $WT/.lake/qwen/logs $WT/Stafford38/Geometry/SameWitness $CAMP/notes`

Accept: the worktree exists on branch `qwen/paper-route`; the pins are
identical. No commit is needed.

### T02 Baseline build of the prerequisites

Owned: `STATE.md`. In `WT`:

```sh
cd $WT && $GUARD run --timeout 14400 --log $SCR/logs/T02.log -- \
  lake build Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint \
    Stafford38.Geometry.ActualSameWitnessGroundPointCompletion \
    Stafford38.Geometry.ActualPointAxisLift \
    Stafford38.Geometry.ActualOptionColumnBinding \
    Stafford38.Geometry.ActualWitnessCommonOpenColumnGlue \
    Stafford38.Geometry.A0ChartFormalEtale \
    Stafford38.Geometry.A0NormalizedProjectiveCoordinates \
    Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness \
    Stafford38.Geometry.GenericSmoothOpen \
    Stafford38.Geometry.GeneralAsymptoticConormal \
    Stafford38.Geometry.GeneralCoisotropicExclusion
```

Record under "Measurements": wall time, `peak_rss_gb`, number of jobs Lake
reported. Accept: exit 0. Stop if: any error in a file you did not create;
that means the baseline is broken and the controller must look at it.

Then time one cheap single-file check so later tasks know the turnaround:

```sh
cd $WT && $GUARD run --timeout 900 --log $SCR/logs/T02-single.log -- \
  lake env lean -M 32000 tests/ActualSameWitnessGroundPointCompletionConsumer.lean
```

Record its wall time as "single-file check" under "Measurements".

## 6. Lean design rules for the closure

These rules exist because the previous attempts failed in exactly these ways.
Apply them in every task of Phases 2–4.

### 6.1 Why repair3 and repair4 failed

The archived `ActualSameWitnessAffineFibreClosure.lean` proves the closure
as one theorem of about 360 lines. Inside the proof it builds the rings
`F`, `V`, `κ`, `Q`, `B`, `R`, `Cq`, `U`, `A₀` and installs roughly forty
instances with `letI`, for example

```lean
letI : Algebra Q U := Algebra.compHom U (algebraMap Q Cq)
letI : Algebra k U := Algebra.compHom U (algebraMap k R)
letI : Algebra A₀ U := quotientAlgebra
letI : Algebra (MvPolynomial (Fin m) k) U := polynomialAlgebra
letI : SMul (MvPolynomial (Fin m) k) U := polynomialAlgebra.toSMul
```

Results:

- repair3, line 417: `failed to synthesize SMul (MvPolynomial (Fin m) k) U`
  with a typeclass timeout (600000 heartbeats), then a `whnf` timeout
  (4000000 heartbeats) for the whole declaration at line 77.
- the scalar-tower diagnostic: `IsScalarTower.of_algebraMap_eq'` produced an
  `IsScalarTower` for `Algebra.toSMul` instances, but the goal wanted
  `IsScalarTower k A₀ U` where `A₀`'s action came from
  `Submodule.Quotient.instSMul'`. Two different `SMul` paths to the same
  carrier: a **diamond**.
- `U` already has `Algebra k U` from its construction as a localization.
  `Algebra.compHom` installs a second, propositionally equal but not
  definitionally equal, instance. Every later unification has to unfold
  `U`, which is why `whnf` explodes.

### 6.2 Rules

1. **No instance installation on concrete heavy types inside a proof.** Never
   `letI`/`haveI` an `Algebra`, `SMul`, `Module`, `IsScalarTower` or
   `Algebra.FormallyEtale` on a concrete ring such as `U`, `B`, `Cq` or `A₀`
   inside a long proof.
2. **Use the instance the type already has.** If `U` is a localization of
   `Cq`, use the `Algebra Cq U` and `Algebra k U` that Mathlib gives it. When
   you need a second map `k → U` (for example through `A₀`), do not install
   it. Prove a **theorem** that the ring homomorphisms are equal:
   `(φ : A₀ →+* U).comp (algebraMap k A₀) = algebraMap k U`.
3. **Work with ring homs, not instances.** Pass `φ : A₀ →ₐ[k] U` or
   `φ : A₀ →+* U` plus an equation. Use `φ.comp`, `RingHom.ext`,
   `AlgHom.comp_algebraMap`, `IsScalarTower.algebraMap_eq`.
4. **When a library theorem demands instances, adapt over abstract types.**
   State an adapter lemma whose rings are *variables* (`{U : Type*}
   [CommRing U] [Algebra k U]`). Inside the adapter, `letI` the extra
   instances (for example `φ.toAlgebra`) and apply the library theorem. Over
   abstract types this elaborates in seconds. Then apply the adapter to the
   concrete `U` from outside. This is the pattern of task T22.
5. **Bundle data in a structure.** A step that produces several objects with
   properties returns one `structure` (a `Prop`-valued `∃` is fine only for
   one or two fields). Later steps take the structure as an argument, so
   their elaboration never re-unfolds earlier constructions.
6. **One mathematical step per top-level declaration.** No proof longer than
   about 60 lines. Use `obtain` on the previous step's structure, not
   copy-pasted construction code.
7. **Make heavy definitions opaque to unification.** If a `def` of a ring is
   unfolded during elaboration (a `whnf` timeout points there), give the
   needed facts as lemmas and use `irreducible_def` or a `structure` wrapper
   for the new definition. Never do this to existing challenge definitions.
8. **Never use `Algebra.compHom` on a type that already has an `Algebra`
   instance from the same base ring.** That is the exact source of the
   diamond.

### 6.3 What to do with a timeout or memory kill

1. Find the declaration from the log (`grep -n "timeout\|error" <log> | head`).
2. Write the declaration's goal at that point into a scratch file in `$SCR`
   that imports the same modules. Put `set_option profiler true in` and
   `set_option trace.Meta.synthInstance true in` on that one declaration and
   run it through `GUARD` with a 900 s timeout. Read only the first 80 lines
   of the trace (`head -80`).
3. If an instance search loops between two paths to the same `SMul` or
   `Algebra`, apply rule 2 or 4. If `whnf` unfolds a big definition, apply
   rule 7. Otherwise split the declaration into two lemmas (rule 6).
4. Raising heartbeats is not a fix (section 2.1).

### 6.4 Statement freeze

When a task gives a Lean statement, copy it character for character into
the file before writing any proof. After the proof compiles, check with
`diff` that the statement text in the file still equals the task text.
Copy the statement into `$SCR/<task-id>-statement.lean` first and diff
against that. Any difference is a failure, even an "equivalent" one.

## 7. Phase 1: port the archived helpers and diagnose

### T10 Extract the archived candidates (read-only)

Owned: `$SCR/archive/` (new), `STATE.md`.

```sh
mkdir -p $SCR/archive/repair4 $SCR/archive/assembly
tar -xzf $ARCH/closure/closure-repair4-sources.tar.gz -C $SCR/archive/repair4
gzip -dc $ARCH/assembly/assembly-wrapper.patch.gz > $SCR/archive/assembly/assembly-wrapper.patch
gzip -dc $ARCH/dependency-guard/dependency-guard-integration.patch.gz > $SCR/archive/dependency-guard-integration.patch
gzip -dc $ARCH/dependency-guard/literal-route-consumers.patch.gz > $SCR/archive/literal-route-consumers.patch
gzip -dc $ARCH/dependency-guard/palomar-verifier-guard-wiring.patch.gz > $SCR/archive/palomar-verifier-guard-wiring.patch
find $SCR/archive -type f | xargs wc -l
```

The repair4 tarball contains five files: `A0ChartFormalEtale.lean` (an
extended version), `ActualSameWitnessAffineFibreClosure.lean` (446 lines),
`AwayFactorToAtPrime.lean`, `GroundPointAxisLiftFromOutput.lean` and
`tests/ActualSameWitnessAffineFibreClosureConsumer.lean`. They are in the old
Lean 4.33 style (plain `import`, no `module` header). Read
`$ARCH/closure/closure-frontier.txt` (short) too.

Accept: files extracted; record the line counts in `STATE.md`.

### T11 Port `AwayFactorToAtPrime`

Owned: `$WT/Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean`,
`$WT/tests/SameWitness/AwayFactorToAtPrimeConsumer.lean`.

1. Read `$SCR/archive/repair4/Stafford38/Geometry/AwayFactorToAtPrime.lean`.
2. Create the new file with the rc3 header style (copy the first 12 lines
   of `$WT/Stafford38/Geometry/A0ChartFormalEtale.lean` as the pattern:
   `module`, `public import …`, `@[expose] public section`,
   `set_option autoImplicit false`). Namespace
   `Stafford38.Geometry.SameWitness`. Keep the mathematical statements
   unchanged. Rename declarations only if their names break rule 2.6, and
   record old → new names in `$CAMP/notes/renames.md`.
3. Search first (2.5): if Mathlib already has the lemma (look for
   `Localization.Away`, `IsLocalization.AtPrime`, `Localization.awayMap`,
   `IsLocalization.Away.mul`), use Mathlib instead and do not port it.
   Record the decision.
4. Add the module to `Stafford38.lean` only if the task list in later
   phases needs it imported from there. For now build it directly:
   `$GUARD run --timeout 2700 --log $SCR/logs/T11.log -- lake build Stafford38.Geometry.SameWitness.AwayFactorToAtPrime`
5. Write the consumer (section 2.1) and check it:
   `$GUARD run --timeout 900 --log $SCR/logs/T11-consumer.log -- lake env lean --trust=0 -M 32000 tests/SameWitness/AwayFactorToAtPrimeConsumer.lean`

Accept: build exit 0; consumer prints only the three allowed axioms.

### T12 Port `GroundPointAxisLiftFromOutput`

Owned: `$WT/Stafford38/Geometry/SameWitness/AxisLiftFromGroundPoint.lean`,
`$WT/tests/SameWitness/AxisLiftFromGroundPointConsumer.lean`.

Same procedure as T11 for
`$SCR/archive/repair4/Stafford38/Geometry/GroundPointAxisLiftFromOutput.lean`.
It uses `Stafford38.Geometry.ActualPointAxisLift.exists_actual_point_axis_lift`
and the ground-point output from `ActualSameWitnessGroundPointCompletion`.
Its import of `GroundPointAxisLiftFromOutput` in other archived files becomes
`Stafford38.Geometry.SameWitness.AxisLiftFromGroundPoint`.

Accept: as T11.

### T13 Port the ground-map lemma of `A0ChartFormalEtale`

Owned: `$WT/Stafford38/Geometry/SameWitness/ChartGroundMap.lean`,
`$WT/tests/SameWitness/ChartGroundMapConsumer.lean`.

The archived `A0ChartFormalEtale.lean` adds lines 278–329 (theorem
`originalAffineChartToCommonOpen_groundMap` and anything after it) to the
current file. Do **not** edit `$WT/Stafford38/Geometry/A0ChartFormalEtale.lean`.
Put the added declarations into the new file, importing
`Stafford38.Geometry.A0ChartFormalEtale`. Find the exact added lines with
`diff <(sed 's/^public import/import/' $WT/Stafford38/Geometry/A0ChartFormalEtale.lean) $SCR/archive/repair4/Stafford38/Geometry/A0ChartFormalEtale.lean`.
This lemma says that the original-affine chart map preserves the ground
field, `φ.comp (algebraMap k _) = algebraMap k _`. Phase 3 needs exactly this
(rule 6.2.2).

Accept: as T11. The archived assembly audit
(`$ARCH/assembly/repair3-groundmap-audit.json`) recorded that this helper
passed with only standard axioms on 4.33; it must pass again on rc3.

## 8. Phase 2: reproduce the diamond and build the adapter

### T20 Instance inventory (notes only, no Lean edits)

Owned: `$CAMP/notes/T20-instance-inventory.md`.

Read `$SCR/archive/repair4/Stafford38/Geometry/ActualSameWitnessAffineFibreClosure.lean`
in pieces of 120 lines. Write a table with one row per ring in the proof:
`F`, `V`, `κ`, `Q`, `B`, `R`, `Cq`, `U`, `A₀`. Columns:

1. how it is defined (the `let` line and the defining declaration);
2. which `Algebra X ring` instances exist **without** any `letI`, which you
   check by `#synth` in a scratch file importing the archived file's
   imports (one `#synth` per line; run once through `GUARD`, 900 s);
3. which instances the archived proof adds with `letI` (line numbers);
4. for each added instance: "duplicate" (an instance from the same base
   already exists), "new" or "needed by endpoint".

The endpoint theorem
`Stafford38.Geometry.ActualSameWitnessAffineFibreEndpoint.axis_mem_smoothConormalFibreProjection_closure_of_actual_columns`
(file `$WT/Stafford38/Geometry/ActualSameWitnessAffineFibreEndpoint.lean`,
lines 35–110) needs, for an abstract ring `E`: `Algebra k E`,
`Algebra (MvPolynomial (Fin n) k ⧸ I) E`, `Algebra (MvPolynomial (Fin n) k) E`,
`Algebra (MvPolynomial (Option (Fin d)) k) E`, four `IsScalarTower`
instances and two `Algebra.FormallyEtale` instances. List which of those
`U` already has.

Accept: the table exists, and the `#synth` results come from a real run (log
path in the note). Expected finding: `U` has `Algebra k U`, `Algebra Q U` and
`Algebra Cq U` from its construction; the archived proof re-installs
`Algebra k U` and `Algebra Q U` by `Algebra.compHom` (duplicates, rule 8).

### T21 Minimal reproducer

Owned: `$SCR/TowerRepro.lean` (scratch, not committed),
`$CAMP/notes/T21-repro.md`.

Write a scratch file importing only Mathlib modules
(`Mathlib.RingTheory.MvPolynomial.Basic`, `Mathlib.RingTheory.Ideal.Quotient.Operations`,
`Mathlib.RingTheory.Localization.Away.Basic`), with `variable {k : Type*} [Field k]
{m : ℕ} (P : Ideal (MvPolynomial (Fin m) k)) [P.IsPrime]`, and `A₀ := MvPolynomial (Fin m) k ⧸ P`.

1. `example : IsScalarTower k (MvPolynomial (Fin m) k) A₀ := inferInstance`
   must succeed with Mathlib's own instances.
2. Take any `E` with `[CommRing E] [Algebra k E]` and `φ : A₀ →ₐ[k] E`. Show
   that `letI := φ.toRingHom.toAlgebra` plus
   `IsScalarTower.of_algebraMap_eq'` gives `IsScalarTower k A₀ E`, proved over
   the abstract `E`.
3. Reproduce the failure: additionally install
   `letI : Algebra (MvPolynomial (Fin m) k) E := Algebra.compHom E (algebraMap _ A₀)`
   on top of an existing `[Algebra (MvPolynomial (Fin m) k) E]` and show that an
   `IsScalarTower` goal fails or needs unfolding.
4. Write in the note which variant works (expected: 1 and 2 work, 3
   reproduces the mismatch).

Accept: scratch compiles except for the deliberately failing part 3, which
you comment out after recording its error message. Single-file check through
`GUARD`, 900 s.

### T22 Ring-hom form of the endpoint (the key adapter)

Owned: `$WT/Stafford38/Geometry/SameWitness/EndpointOfAlgHoms.lean`,
`$WT/tests/SameWitness/EndpointOfAlgHomsConsumer.lean`.

Prove a theorem that has the same conclusion as the endpoint theorem but
takes the scalar structure as ring homomorphisms over an **abstract** ring
`E` that carries only `[CommRing E] [Algebra k E]`:

```lean
theorem axis_mem_smoothConormalFibreProjection_closure_of_algHoms
    {k E : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing E] [Algebra k E] {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) k)} [I.IsPrime]
    (φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] E)
    (ψ : MvPolynomial (Option (Fin d)) k →ₐ[k] E)
    (hφEtale : letI := φ.toRingHom.toAlgebra
      Algebra.FormallyEtale (MvPolynomial (Fin n) k ⧸ I) E)
    (hψEtale : letI := ψ.toRingHom.toAlgebra
      Algebra.FormallyEtale (MvPolynomial (Option (Fin d)) k) E)
    (rho : E →+* LaurentSeries k)
    (hground : rho.comp (algebraMap k E) = algebraMap k (LaurentSeries k))
    -- then every remaining argument of the endpoint, from `qC` to
    -- `hnumerator`, copied verbatim, except that each occurrence of
    -- `algebraMap (MvPolynomial (Fin n) k ⧸ I) E` becomes `φ`
    ... :
    (fun i : Fin n => if i = axis then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection I))
```

The `...` is a placeholder for you to fill. Copy the endpoint's binders
(lines 62–100 of the endpoint file) in their order. Keep the `letI` prelude
of the endpoint's statement (the `Algebra E (LaurentSeries k)` block) where
the endpoint has it.
`htransverse` and `hraw` mention `coordinateDerivation … (B := E)`, which
needs the `Algebra (MvPolynomial (Option (Fin d)) k) E` instance; put the
`letI := ψ.toRingHom.toAlgebra` in front of those binders exactly as the
endpoint's own `letI` prelude does.

Proof: inside the proof, over the abstract `E`, install
`φ.toRingHom.toAlgebra`, the polynomial algebra as
`(φ.toRingHom.comp (Ideal.Quotient.mk I)).toAlgebra`, `ψ.toRingHom.toAlgebra`,
the four towers by `IsScalarTower.of_algebraMap_eq'` using `φ.comp_algebraMap`
and `ψ.comp_algebraMap` (`AlgHom.comp_algebraMap`), and the two
`FormallyEtale` from the hypotheses. Then apply the endpoint. The
polynomial-to-quotient tower must hold by `rfl` or `RingHom.ext` with
`Ideal.Quotient.mk`.

Accept: compiles in under 120 s; the consumer, with literally the same
statement, prints only the three allowed axioms. This lemma is generic: no
concrete `U` appears.

Stop if: the endpoint's statement cannot be expressed this way without
adding a hypothesis that is not one of φ, ψ, hφEtale, hψEtale. Report which.

## 9. Phase 3: the same-witness closure in steps

Source of the mathematics: the archived proof
`$SCR/archive/repair4/Stafford38/Geometry/ActualSameWitnessAffineFibreClosure.lean`,
theorem `axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput`
(statement lines 82–95, proof lines 96–446). Its mathematics was audited as
correct twice. Its Lean form is what failed. Each task below moves one block
of that proof into its own file under rules 6.2.

Common rules for T30–T35:

- Files go in `$WT/Stafford38/Geometry/SameWitness/`, namespace
  `Stafford38.Geometry.SameWitness`. Each file imports the previous step's
  file and only the modules it needs (take them from the archived file's
  import list, lines 1–23, and its `open` list, lines 32–75).
- Objects that are already functions of `P` and `w` (for example
  `actualSelectedChartAlgebra P w`, `actualSelectedNormalization P w`,
  `actualSelectedNormalizationCoefficients P w`) are **not** copied into a
  structure; refer to them directly.
- Objects that are *chosen* (`obtain`) go into a step structure: chart
  index `j`, away element `f` and equivalence `e`, element `r`, rows, the
  maximal ideal `M` and its data, columns.
- To decide which fields a structure needs: `grep -n "<name>"` in the
  archived proof after the block; a chosen object or fact used later is a
  field, one never used later is not.
- After each task, run this check and paste its output into the report:

  ```sh
  grep -nE "letI|haveI" <new file> | grep -E "Algebra|SMul|Module|IsScalarTower|FormallyEtale"
  grep -nE "compHom" <new file>
  ```

  Both must print nothing, except inside the abstract adapter of T22.
- Build each new module alone:
  `$GUARD run --timeout 2700 --log $SCR/logs/<task>.log -- lake build Stafford38.Geometry.SameWitness.<File>`.
  If one declaration takes more than 300 s (see `set_option profiler true`),
  split it before going on.

### T30 Chart and away data (archived lines 96–166)

Owned: `SameWitness/ChartSetup.lean`, `tests/SameWitness/ChartSetupConsumer.lean`.

Content: the chart index `j` from `exists_succ_chart_index`, the selected
normalization `B`, the away presentation (`actual_selected_normalization_is_away_equiv`:
`f0`, `e0`), the element `r` from line 139, and the facts `f ≠ 0`, `r ≠ 0`,
injectivity of `qToB`, `fB * rB ≠ 0`. Produce
`structure ChartSetup (hm) (P) (w)` and
`theorem nonempty_chartSetup … : Nonempty (ChartSetup hm P w)`.

### T31 Coordinate presentation (archived lines 167–242)

Owned: `SameWitness/CoordinatePresentation.lean` and its consumer.

Content: the finite row set `t`, `τ`, `rows`, `qRow`, the presentation
`fOption`/`fFin : R →ₐ[k] B` with `R = MvPolynomial (Option (Fin d)) k`,
`hnone`, `hsome`, `hrows`, `hqchartB`, `hzero`, `haxis` and the
`GroundPointChartOutput` fact `hOutput`. Input: a `ChartSetup`. Output: a
structure `CoordinatePresentation` plus its existence theorem.

### T32 Maximal ideal and common open (archived lines 243–293)

Owned: `SameWitness/CommonOpen.lean` and its consumer.

Content: from `hOutput` and `bad = fB * rB` obtain `M`, `eM`, the units and
`u₀'`, `u₁'` (line 244); `hsel`, `qQ` and its facts; `Cq`, `g`, `U` (lines
259–261); `qU`, `qT`; `hqA`, `hqUPoint`; `φ := originalAffineChartToCommonOpen …`
and `hchartU`; `hq0B`, `hfactor`. `U` keeps the `Algebra` instances of its
construction (no new ones). Output: a structure `CommonOpenData` and its
existence theorem.

### T33 Arc into Laurent series (archived lines 294–320)

Owned: `SameWitness/CommonOpenArc.lean` and its consumer.

Content: `rhoA`, `hunitM`, `rhoU := genericArcToGenericOpenExtraAwayB …`,
`hcomp'`, `hgroundB'`, and `hgroundU : rhoU.comp (algebraMap k U) = algebraMap k (LaurentSeries k)`
(line 380). The ground equation must be proved for **the existing**
`algebraMap k U`.

### T34 Columns, derivatives and numerator (archived lines 321–395)

Owned: `SameWitness/CommonOpenColumns.lean` and its consumer.

Content: `hcols`, `qPre`, `hchartPre`, `hEvalB`, `hcoords`, `qL`,
`hpositionL`, `hbaseMap`, `hcolumnsL`, `hEval`, `hnumerator`, and the two
derivative identities needed as `htransverse` and `hraw` by the endpoint.
State the derivative identities using `ψ := (the T31 map R →ₐ[k] B)` composed
with the common-open map to `U` as an `AlgHom`, in the form T22 expects.
If this block needs more than 150 lines of Lean, split it in two files
(columns and positions; derivatives and numerator) and say so in the report.

### T35 Étale structure as ring homs (archived lines 396–411 and 319)

Owned: `SameWitness/CommonOpenEtale.lean` and its consumer.

1. `φ` as a `k`-algebra map: build `φk : A₀ →ₐ[k] U` from the ring hom `φ`
   and the ground-map equation proved in T13 (`originalAffineChartToCommonOpen_groundMap`),
   using `AlgHom.mk'` or `{ φ with commutes' := … }`.
2. `ψU : R →ₐ[k] U` as the composite of the T31 map with the common-open map.
3. The two `FormallyEtale` facts in exactly the form of T22's `hφEtale` and
   `hψEtale`. Use `formallyEtale_originalAffineChartToCommonOpen` (archived
   line 425) and the étale fact at archived line 319. The instance must be
   stated through `φk.toRingHom.toAlgebra`, which is definitionally the
   `φ.toAlgebra` used by the existing theorems; if `exact` fails because of
   that, prove the equality of the two `Algebra` structures with
   `Algebra.algebra_ext` and rewrite.

### T36 The closure theorem

Owned: `SameWitness/AffineFibreClosure.lean`,
`tests/SameWitness/AffineFibreClosureConsumer.lean`.

Statement (freeze per 6.4; copy exactly):

```lean
theorem axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hpoint : actualSameWitnessGroundPointOutput hm P w)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal))
```

Proof: at most 60 lines. `obtain` the structures of T30–T35, define `beta`,
`u₀`, `u₁` as in archived lines 427–435, and `exact
axis_mem_smoothConormalFibreProjection_closure_of_algHoms …` (T22) with
`E := U`.

Consumer: port `$SCR/archive/repair4/tests/ActualSameWitnessAffineFibreClosureConsumer.lean`
to `tests/SameWitness/AffineFibreClosureConsumer.lean` (rc3 header, new
namespace). Its statement has **no** `hpoint`/`hsmoothOpen`. It supplies them
from `exists_actual_same_witness_groundpoint_chart hm P w` and
`Stafford38.Geometry.exists_nonzero_smooth_away_quotient P.asIdeal`.
Run it with `lake env lean --trust=0 -M 32000`.

Accept: module builds; the consumer prints only the three allowed axioms
for both the consumer theorem and the closure theorem; statement diff empty.
This completes the first open bridge of `docs/paper-route-alignment.json`.

## 10. Phase 4: original-prime wrapper, terminal rewiring, dependency guard

### T40 Import-cycle check (no edits)

Owned: `$CAMP/notes/T40-imports.md`.

`GeneralAsymptoticConormal` will import the new closure. That is only legal
if the closure's import closure does not contain `GeneralAsymptoticConormal`
or `GeneralCoisotropicExclusion`. Compute the closure from the sources:

```sh
cd $WT && python3 - <<'PY'
import re, pathlib
def deps(mod):
    p = pathlib.Path(*mod.split('.')).with_suffix('.lean')
    if not p.exists(): return []
    return re.findall(r'^(?:public )?import (\S+)', p.read_text(), re.M)
seen, todo = set(), ['Stafford38.Geometry.SameWitness.AffineFibreClosure',
                     'Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness']
while todo:
    m = todo.pop()
    if m in seen or not m.startswith('Stafford38'): continue
    seen.add(m); todo += deps(m)
bad = [m for m in seen if m.endswith(('GeneralAsymptoticConormal', 'GeneralCoisotropicExclusion', 'GeneralAsymptoticLaurentAxis'))]
print(len(seen), 'modules; forbidden in closure:', bad)
PY
```

Accept: `forbidden in closure: []`. Stop if: not empty; the controller then
decides where the wrapper lives.

### T41 Original-prime wrapper

Owned: `SameWitness/OriginalPrimeAxis.lean`, `tests/SameWitness/OriginalPrimeAxisConsumer.lean`.

Statement (freeze per 6.4; it is the statement of the existing terminal
geometric theorem, copied from `GeneralAsymptoticConormal.lean` lines 31–38):

```lean
theorem coordinate_axis_mem_smooth_fibre_closure
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : PrimeSpectrum (MvPolynomial (Fin m) k))
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I.asIdeal, y ⟨0, hm⟩ ≠ 0) :
    (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I.asIdeal))
```

in namespace `Stafford38.Geometry.SameWitness`; open the namespace that
defines `smoothConormalFibreProjection` (it is
`Stafford38.Geometry.ProjectiveConormalDirections`).

Proof (about 10 lines):

```lean
  rcases Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness.coordinate_axis_or_visible_frame_of_avoidance
      hm I havoid with h | ⟨w⟩
  · exact h
  · exact axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput hm I w
      (Stafford38.Geometry.ActualSameWitnessGroundPointCompletion.exists_actual_same_witness_groundpoint_chart hm I w)
      (Stafford38.Geometry.exists_nonzero_smooth_away_quotient I.asIdeal)
```

(Check the exact namespace of `coordinate_axis_or_visible_frame_of_avoidance`
with `grep -n "^namespace" $WT/Stafford38/Geometry/OriginalPrimeCoordinateAvoidanceWitness.lean`.)
The first branch is the direct constant-coordinate case; the second is the
paper's retained-witness route.

Accept: builds; consumer with the literal statement prints only the three
allowed axioms.

### T42 Rewire the terminal geometric theorem

Owned: `$WT/Stafford38/Geometry/GeneralAsymptoticConormal.lean` (**proof
body of `coordinate_axis_mem_smooth_fibre_closure` and the import list
only**).

1. Save the current statement: `sed -n 31,38p <file> > $SCR/T42-statement-before.lean`.
2. Add `public import Stafford38.Geometry.SameWitness.OriginalPrimeAxis`.
3. Replace the proof body (from `:= by` to the end of that theorem) by
   `Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure hm I havoid`.
   Leave `coordinate_axis_mem_projective_conormal_directions` and every other
   declaration in the file untouched.
4. `sed -n 31,38p <file> | diff $SCR/T42-statement-before.lean -` must print
   nothing.
5. Remove imports that became unused **only** if the build stays green
   without them, and list them in the report. If unsure, keep them.
6. Build: `$GUARD run --timeout 14400 --log $SCR/logs/T42.log -- lake build Stafford38.Geometry.GeneralCoisotropicExclusion Solution FixedSourceSolution`.

Accept: exit 0; statement diff empty.

### T43 Install the strict dependency guard

Owned: the files created by the archived patches:
`scripts/dependency-guard/*`, `tests/dependency-guard-fixtures/*`, and the
two hunks of `scripts/verify.sh` from the wiring patch.

1. `cd $WT && git apply --check $SCR/archive/dependency-guard-integration.patch`, then apply it.
   Same for `$SCR/archive/palomar-verifier-guard-wiring.patch`. If `--check`
   fails, stop and report the failing hunk. Do not hand-edit around it.
2. Fixture behaviour test (independent oracle for the guard itself):
   `$GUARD run --timeout 3600 --log $SCR/logs/T43-fixtures.log -- python3 tests/dependency-guard-fixtures/test_behavior.py`.
   Its last line must start with `PASS:`.
3. Production guard on the real terminal roots:
   `$GUARD run --timeout 3600 --log $SCR/logs/T43-guard.log -- python3 scripts/dependency-guard/run_guard.py`.
   It rejects any terminal dependency on
   `Stafford38.Geometry.GeneralAsymptoticLaurentAxis` and five named old-route
   producers, and any axiom outside the standard three.
4. Never set `STAFFORD_ALLOW_OLD_ROUTE=1` or pass `--allow-old-route`.

Accept: fixtures `PASS`; production guard exit 0.

Stop if: the production guard still finds a banned name. Report the
dependency path it prints. Likely culprits are the visible-frame witness
producer (`generalDivisorialVisibleFrameWithResidueAlgebraicity`) or the
constant-coordinate branch. That is a real mathematical routing question for
the controller, not something to work around.

### T44 Literal route consumers

Owned: files of `$SCR/archive/literal-route-consumers.patch`.

`git apply --check`, apply, then compile each new test file with
`lake env lean --trust=0 -M 32000` through `GUARD`. These consumers were
written for the archived names. If they reference `ActualSameWitnessAffineFibreClosure`
or `GroundPointAxisLiftFromOutput`, update only the referenced names to the
new ones from `$CAMP/notes/renames.md`; statements stay literal.

Accept: every consumer prints only the three allowed axioms.

## 11. Phase 5: full verification on faepmac1

### T50 Full library build

Owned: `STATE.md`.
`$GUARD run --timeout 14400 --log $SCR/logs/T50.log -- lake build`
then the explicit list from `scripts/verify.sh` lines 22–42 (the retained
module list is generated there; run the same Python snippet). Record wall
time and `peak_rss_gb`.

Accept: exit 0, no `sorry` warning: `grep -c "declaration uses 'sorry'" $SCR/logs/T50.log`
must be `0`.

### T51 Repository verifier

Owned: `STATE.md`.
`$GUARD run --timeout 21600 --log $SCR/logs/T51.log -- bash scripts/verify.sh`.
This is the only task allowed to let `scripts/bootstrap-palomar-tools.sh`
install the pinned Lean toolchain or Palomar tools if they are missing (it
checks the exact commit `470d5ce…`).

Accept: exit 0. Then list `.lake/verification/*.log` with sizes and record
the last line of each in `$CAMP/notes/T51-receipt.md`, with
`git -C $WT rev-parse HEAD` and `git -C $WT diff --stat main | tail -1`.

Stop if: any check fails twice. Report the first failing log.

### T52 Status drafts (no authoritative edits)

Owned: `$CAMP/notes/T52-docs-proposal.md`.

Draft the replacement text for the `component_status` and `open_bridges`
entries of `$WT/docs/paper-route-alignment.json` and for the "Proof and
correspondence" paragraph of `$WT/STATUS.md`, citing the T51 receipt. Mark
nothing as released. The controller applies and reviews it.

### T53 OWNER GATE: integrate into main

The controller reviews the branch (full diff, receipts, statement diffs) and
the owner decides about merge and push. Pi does nothing here.

## 12. Phase 6: readability and duplication pass (report-first)

This phase only adds documentation and proposals. It renames or deletes
nothing that existed before the campaign.

### T60 Definition owners

Owned: `$CAMP/notes/T60-definition-owners.patch`.

For every entry of `$CAMP/notes/new-definitions.md`, check once more that
no existing owner fits (2.5), then write a patch adding rows to
`$WT/docs/definition-owners.md` in its table format. Do not apply it; the
controller does.

### T61 Paper map of the new theorems

Owned: `$CAMP/notes/T61-paper-map.md`.

For each top-level theorem in `Stafford38/Geometry/SameWitness/`, one row:
Lean name, file:line, one sentence of mathematics, the matching place in
`/Users/ert/proj/stafford38-paper/human_readable_main.tex` (search with
`grep -n` for the key words: normalization, ground point, étale, tilt, arc,
tangent, conormal). Write "no paper counterpart" when there is none. Do not
edit the manuscript.

### T62 Unreachable and duplicate geometry (report only)

Owned: `$CAMP/notes/T62-cleanup-report.md`.

1. With the T40 script, compute the set of `Stafford38/Geometry` modules
   reachable from `Stafford38.lean`, `Solution.lean`,
   `FixedSourceSolution.lean`, `CorollaryChallenge.lean`,
   `PaperPairChallenge.lean` and every `tests/**/*.lean`. List the
   unreachable ones.
2. List groups of declarations with near-identical statements: same
   conclusion after `grep -h "^theorem" -A8`, compared by eye in groups of
   at most 20.
3. Propose, per group, which declaration is the owner. Delete nothing.

The owner decides on a later clean-up campaign.

## 13. Phase 7: Linux replay and Palomar comparisons

### T70 OWNER GATE: frozen public commit

The controller merges, the owner approves the push, and the controller
records the exact commit in `STATE.md` under "Frozen commit". Pi waits.

### T71 Remote preflight on mailuefterl

Owned: `STATE.md`.

```sh
ssh mailuefterl 'hostname; nproc; free -g | head -2; df -h /mnt/storage | tail -1; pgrep -a lean | head; pgrep -a lake | head'
```

Accept: `hostname` is mailuefterl, at least 100 GiB free on `/mnt/storage`,
at least 64 GiB available RAM, no `lean`/`lake` running. Otherwise stop and
report. Never use any other host (2.3).

### T72 Launch the archived Linux driver

Owned: remote directory created by the snapshot script; `STATE.md`.

Read `$ARCH/palomar/stafford38-linux-execution-contract-20261002.json`
completely in two parts (`python3 -m json.tool … | sed -n 1,120p`, then
`121,240p`). It specifies the host, the fresh directory template
`/mnt/storage/stafford38-final-replay-20261002.XXXXXX`, the exact pins, the
source-freeze rule (`git archive` of the frozen commit, never the live
directory), the ordered commands and the process tracking. Follow it
literally, with the frozen commit from `STATE.md` as source:

1. Verify the SHA-256 of the two scripts against the contract's `artifacts`
   field: `shasum -a 256 $ARCH/palomar/stafford38-linux-snapshot-20261002.sh $ARCH/palomar/stafford38-linux-driver-20261002.sh`.
   Any mismatch: stop.
2. Copy both scripts to the remote fresh directory with `scp`, run the
   snapshot script, then start the driver **detached** as the contract
   requires (this is the single exception to "no background jobs": it runs
   on mailuefterl, not here, and the contract demands it). Record pid,
   process group, log path and start time in `STATE.md`.

Accept: driver running, recorded. Set T72 `done`; T73 becomes the next task.

### T73 Collect the Linux result

Owned: `STATE.md`, `$CAMP/notes/T73-linux-receipt.md`.

One check per run: `ssh mailuefterl 'ps -p <pid> -o pid,etime,cmd; tail -5 <log>'`.
If the driver still runs, report `RESULT: running`, leave T73 `todo`, and
stop. The owner restarts Pi later. When it has finished, copy the receipt
files named in the contract back to `$CAMP/notes/linux-receipt/`, record exit
status and the comparator results for both challenges, and mark `done` only
if every ordered command passed.

### T74 OWNER GATE: official Palomar workflow dispatch

Uses the contract's `official_dispatch` section. Owner and controller only.

## 14. Phases 8–9: review bundle and release

### T80 Re-anchor the review map

Owned: `$WT/docs/paper-lean-audit/*` map file named by the script's `--map`
argument (find the current map with `ls $WT/docs/paper-lean-audit`).

```sh
cd $WT && python3 scripts/reanchor-review-map.py --paper /Users/ert/proj/stafford38-paper \
  --paper-file human_readable_main.tex --map <map file>
```

Then add rows for the new SameWitness theorems from the T61 table. Accept:
the script exits 0 and every map entry's Lean declaration exists:
`lake env lean` on a generated scratch file with one `#check <name>` per
entry (through `GUARD`, 900 s) shows no `unknown identifier`.

### T81 Build the review site

`cd $WT && $GUARD run --timeout 3600 --log $SCR/logs/T81.log -- python3 scripts/build-review-site.py`
(read its `--help` first). Accept: exit 0; record output paths.

### T82 Rebuild the manuscript PDFs (no text edits)

In `/Users/ert/proj/stafford38-paper`, following its README:

```sh
latexmk -pdf human_readable_main.tex && latexmk -pdf lean_proof_details.tex && latexmk -pdf main.tex
grep -c "undefined" human_readable_main.log lean_proof_details.log main.log
```

Accept: three PDFs, zero undefined references. Never edit `.tex` files: the
manuscript preserves Johanna's proof, and Overleaf is its editing authority.
If a reference to a Lean name breaks, report it for the controller.

### T83 Supplementary bundle (local only)

In `/Users/ert/proj/stafford38-supplementary`, follow steps 2–4 of
`docs/release-preparation.md` with the frozen commits. Run
`python3 scripts/rebuild.py`. Do not create tags, releases or DOIs.
Record every check in `$CAMP/notes/T83-supplementary-receipt.md`.

### T84 OWNER GATE: review handover

Johanna reviews the mathematical prose and marked proposals; Max reviews the
complete paper/Lean correspondence. The owner sends the package.

### T90 Release drafts

Owned: `$CAMP/notes/release/`.

From `$ARCH/release-preparation/` (`PROPOSAL.md`, `RELEASE-NOTES-PENDING.md`,
`release-body.template.md`, `CITATION.prearchive.cff`) prepare filled-in
drafts for the next formal version with the frozen commit, the receipts of
T51 and T73, and the AlgebraicAnalysis DOI `10.5281/zenodo.23104842`. No
placeholders may remain except the future version DOI.

### T91 OWNER GATE: signed tag, GitHub release, Zenodo

Owner and controller only, using `$ARCH/release-preparation/future-commands.sh.txt`.

### T92 Verify the Zenodo archive

After the owner records the Zenodo record id in `STATE.md`: download the
archive as described in the template, compare every file byte for byte
with the tag (`git -C $WT archive <tag> | tar -t` against the unpacked
archive, then `shasum -a 256` per file), and write
`$CAMP/notes/T92-zenodo-receipt.md` with counts, extras and mismatches.
Accept: zero mismatches.

### T93 Citation drafts

Owned: `$CAMP/notes/release/citations.md`. Draft the updated citations
for the formal repository, the paper and the supplementary bundle with the
new DOI. The controller applies them; Overleaf sync is the owner's.

When T93 is done, the campaign is complete. Report `RESULT: campaign
complete` and stop.
