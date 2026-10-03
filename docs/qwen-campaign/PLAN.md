# Stafford 3.8 parallel proof and release campaign

This is the work order for the controller and parallel agent team. On
3 October 2026 the owner requested heavy parallelism, Luna workers with
Sol escalation after failed tasks, regular commits/pushes, both repository
releases and a final review email. This replaces the former serial Pi/Qwen
execution model. The historical directory and branch names are retained
for receipt continuity; no Qwen worker or driver is used.

The controller runs on Linux `mailuefterl`. The owner clarified on
3 October 2026 that all campaign execution uses this Linux host and Linux
compute allocations on `acluster` and `scluster`. Do not run checks, sync
candidates, bootstrap caches, or schedule campaign work on any Mac. Saved
Mac branches and receipts remain historical provenance only.

Immediate priority: finish the same-witness proof faithful to Johanna’s
original manuscript argument, with necessary explicit corrections. Derive
each input from the retained witness; preserve the visible author proof and
marked proposals. Finish T34–T36 and T40–T51, then deliver matching formal and supplementary
releases. Verify both Zenodo archives and cite them from the paper. This is
one delivery, with proof and asset checks as its acceptance gates.

Current checkpoint (3 October 2026): all manuscript-route modules, their
literal trust-zero consumers, the shared terminal theorem and all four solution
assemblies passed their bounded Linux checks. Accepted source is integrated and
pushed in MAIN. The unchanged challenges are shared by the main paper route and
the separately labeled generic/Laurent solution variant.

The complete pinned Linux repository verifier passed at frozen public source
`12ae3cc49152672a48a96f13994314b65ae38197` in scluster3131801: fresh
4475-job build, strict four-root/main/alternative dependency inspections,
116 consumer files with317 required reports,111 paper-linked names and37
endpoint axiom reports. The3 retained proof modules passed in3136492.
All four actual Palomar comparisons passed in3137241: main19:22:38Z,
fixed-source19:39:44Z, alternative19:47:11Z and alternative fixed-source
19:54:35Z. Final tracked-source manifests and all10 package pins match;
the allocation drained guard0 with no resource stop, swap growth or children.
The primary receipt is docs/verification-results.json; historical receipts
and earlier scoped runner failures remain preserved. No successful verifier,
library or comparison check will be repeated.

The bounded compiler-name acceptance passed all399 public owner/name checks
in3139266, with4 isolated groups and guard0/drained. The earlier standalone
import error is archived; only its check arrangement changed. Release
qualification is complete. Formal signed v1.3.0 was published at20:12:31Z; all1,163 files match its
Zenodo archive, DOI10.5281/zenodo.23126868. The P4 citation/source-link update
is pushed to GitHub and Overleaf. Finish matching supplementary v0.2.0. Human reviews remain pending.

The guided renderer 40967b6740c2ceaf515a2fb47a5ca9571be6495f passed the complete
57-card browser walkthrough. The public review site is deployed. All three
manuscript PDFs compile with zero undefined references at paper a5a703f5, with snapshot 22b44d56 and formal links to 12ae3cc.
The refreshed map/PDF asset gate passed. Refresh their citations after
verified archive publication. Human review remains pending. Formal v1.3.0 and its byte-verified DOI are published; supplementary
v0.2.0, final citations and final emails remain to finish.

Efficiency update (owner steering, 3 October 2026): assign each proof check
to one Linux slot. Use acluster and scluster for distinct tasks, never duplicate
the same candidate for extra validation. Reuse the accepted tools and receipts;
add no new infrastructure or optional checks. The release gate is one complete
pinned Linux repository verifier and all four actual Palomar comparisons.
T50/T51 and T73 share that final run; do not run the full verifier once on the
candidate and again on a fresh release clone. Bounded module/consumer checks
resolve proof errors before source freeze. Publish both releases after this
gate, then verify their Zenodo archives, cite them, and send the review emails.

Campaign folder (absolute): `/home/ert/proj/stafford38-formal/docs/qwen-campaign`

| Name | Path |
| --- | --- |
| `MAIN` | `/home/ert/proj/stafford38-formal` (controller checkout, branch `main`; do not edit Lean here) |
| `WT` | `/home/ert/proj/stafford38-qwen` (campaign worktree, branch `campaign/paper-route-20261003`, restored from `c3dccd4b3f93`; all Lean edits go here) |
| `CAMP` | `$MAIN/docs/qwen-campaign` (this plan, `STATE.md`, Linux guards, notes) |
| `ARCH` | `$MAIN/docs/audits/paused-2026-10-02` (archived failed candidates; read-only) |
| `SCR` | `$WT/.lake/qwen` (scratch files, extracted archives and logs; never committed) |
| `GUARD` | `python3 $CAMP/linux-guard.py` on local Linux; reviewed allocation guard on acluster/scluster |

## 0. How workers and controller operate

1. Read sections 0–4, the assigned task, `STATE.md`, relevant controller
   hints and project provenance before editing. Work only on assigned paths.
2. The controller assigns independent tasks concurrently using the dependency
   table below. Later tasks may prepare candidates before prerequisites pass;
   their acceptance and promotion must wait for those prerequisites.
3. Use `gpt-6-luna` workers and subagents. A failed bounded task escalates to
   `gpt-6.1-sol`. Subagents may investigate, review or edit disjoint delegated
   paths; tell the controller their ownership and dependencies. Never use Qwen.
4. Share proposed interfaces early with dependent workers. Import actual data
   dependencies; do not add imports solely to preserve former task order.
5. Send Lean check requests to the controller. It assigns independent checks
   to guarded local slots or bounded Slurm jobs on acluster/scluster. Each
   host or allocation has an explicit RAM and CPU budget; checks on different
   hosts may run concurrently. Editing, source analysis, review and artifact
   preparation continue in parallel. Return the exact job handle and receipt.
6. Return candidates, frozen source hashes, commands, logs and acceptance
   evidence. Workers never edit the authoritative ledger or promote results.
   The controller reviews, updates `STATE.md`, stages explicit paths, commits
   accepted work and pushes regularly.
7. A worker stops its bounded assignment after returning the report in 4.3.
   The controller continues the full campaign and assigns further work.

If a task's **Stop if** condition fires, or the same error appears after three
different repairs, return the exact first error and attempted repairs in
`notes/<task-id>-blocked.md`. Do not raise budgets, weaken statements or
bypass guards. The controller repairs the plan or escalates; independent work
continues. A blocked task is distinct from the active thread goal's status.

Owner gates are controller promotion gates. Workers cannot execute them.
The current user instruction authorizes integration, pushes, releases and
the final email after the stated verification gates pass; do not ask again
for actions already authorized. Preserve the separate human-review status.

### Parallel task dependencies

| Work | Acceptance prerequisites | Work that can overlap |
| --- | --- | --- |
| T20–T22 diagnostics and endpoint | Baseline and source-resolved imports; T22 checked against the endpoint | T30 setup, generic transport analysis and release audit |
| T30 chart setup | Baseline, archived mathematics and literal consumer | T22, T31 interface design, T43/T44 preparation |
| T31 coordinate presentation | Accepted T30 interface and retained ground-point output | T32 common-open design and generic column/étale analysis |
| T32 common open | T31 and accepted axis-lift/chart-map helpers | T33 arc, T34 columns and T35 étale candidates from shared interfaces |
| T33 arc | T32 | T35 and independent portions of T34 |
| T34 columns | T22 interface, T32/T33 | T35 |
| T35 étale maps | T13, T22 interface, T32 | T33/T34 |
| T36 closure | Accepted T22 and T30–T35; frozen target and unconditional consumer | T40/T41/T42 candidates and T43/T44 preparation |
| T40–T44 terminal integration | Completed closure; no cycles; unchanged target; strict guard and consumers | Definition-owner and paper-map preparation |
| T45 solution variants | Shared unchanged challenges; route-neutral downstream assembly; genuinely distinct geometric endpoints | T46 cleanup and variant tooling |
| T46 package cleanup | Reference/dependency evidence; retain both useful solution routes and historical receipts | Final declaration and paper maps |
| T50–T53 full verification/integration | Accepted proof modules, both isolated solution variants, cleanup and strict dependency guards | T60–T62, review-anchor and release-draft preparation |
| T60–T62 documentation | Final accepted declaration names | Review tooling and manuscript compilation |
| T70–T74 source freeze and replay | Integrated public source; final Linux receipts and Palomar-ready package | Review-bundle work pinned to the same freeze |
| T80–T84 review bundle | Frozen source inputs and completed map/compilation checks | T90 release materials |
| T90–T93 publication/citations | All verification, source/asset matching and archive gates | Independent formal and supplementary artifact checks |

Preparatory drafts never count as completed gates. The controller selects
the final coherent source and publishes only after its required checks pass.
T84 prepares the review handover; the requested email is sent after both
releases, archive verification and final citations, as the owner instructed.

## 1. Goal and end state

The owner further clarified the final package: challenge statements remain
unchanged. The main solution uses the paper-conforming retained-witness route.
Preserve the older verified route as a separately labeled solution variant,
sharing the challenge when possible; copy a challenge only if packaging needs
it and preserve its exact statement. Mark both routes in release notes. Remove
obsolete unused front doors, candidate scaffolding and files after checking
references and retaining the useful alternative route; Git history preserves
their development. The owner will perform Palomar’s online submission. Our
job is to deliver a tidy package with local source-policy and kernel-comparison
receipts ready for that submission; do not submit/register online on his behalf.

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
- Workers may edit in `MAIN` only their explicitly assigned `$CAMP/notes/*`.
  The controller owns `PLAN.md`, `STATE.md`, integration and release metadata.
  The former macOS serial-runner scripts are retired. Use only the Linux guard
  and reviewed cluster guard named in sections 2.3 and 3; keep host-specific
  execution receipts in the task notes.
- Never edit files under `.lake/packages/` (Mathlib, AlgebraicAnalysis).

### 2.3 Machines

- Execute only on local Linux `mailuefterl` and Linux compute allocations
  on `acluster` and `scluster`, as the owner explicitly instructed. No Mac
  execution or source synchronization. Cluster login nodes are for submission
  and lightweight inspection. Preserve foreign jobs and persistent services.
- Never connect to, run on, or schedule anything on `faepop*` or `faepcr*`.
- Phase 7 requires a fresh immutable Linux replay. Use `mailuefterl` when
  its guard remains clear; the owner's approved `acluster`/`scluster` allocations
  are the fallback when repeated node-pressure stops prevent completion.
  Preserve the archived mailuefterl contract and receipts unchanged. For a
  cluster replay, record a separately reviewed host-specific driver/contract
  with the same source-freeze, exact pins, ordered verifier and kernel checks,
  extended to both solution variants, under the accepted allocation guard.
  Candidate cluster diagnostics alone never replace this final receipt.

### 2.4 Git

- Workers never commit, push, tag, merge or promote. The controller commits
  accepted proof changes in `WT` on `campaign/paper-route-20261003`, and authoritative
  campaign/integration records in `MAIN`, staging explicit paths only.
- The controller pushes accepted checkpoints regularly and performs the
  authorized integration and new signed releases after their gates pass.
- Never move existing tags, `reset --hard`, `clean`, `stash`, delete branches
  or remove worktrees. Preserve unrelated edits and historical receipts.
- Review inputs use an exact base commit plus a frozen patch digest including
  new paths when uncommitted; do not treat a hashed patch as unreproducible.

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
- Keep proofs short. About 60 lines guides new construction; do not delay a
  working derived generic bridge with an optional refactor when its checks pass
  under the fixed budgets. T36's terminal assembly keeps its stated 60-line bound.
- No `letI`/`haveI` of `Algebra`, `SMul`, `Module` or `IsScalarTower` inside
  a proof about concrete heavy types. Follow the rules in section 6.
- Keep the existing file style: `module` header, `public import`,
  `@[expose] public section`, `set_option autoImplicit false`, a namespace
  matching the path, `universe u`.

## 3. Resources: RAM, disk, time

The active hosts are local Linux `mailuefterl`, `acluster`, and `scluster`.
Initial module and consumer checks use **8 GiB RAM and two actual CPUs**.
The local rc3 Linux cache is already bootstrapped and pin-checked. Cluster
allocations use isolated source/build trees with the same frozen source and
pins; preserve all historical verification evidence.

- The controller grants one local guarded slot per host and separate bounded
  cluster allocations. Independent allocations may run concurrently against
  immutable input snapshots; never share writable build trees or mix Darwin
  and Linux build artifacts. Record the source base, complete patch digest,
  package/toolchain pins, host, job ID, resource limits and result hashes.
- Every local Lean-invoking command uses `GUARD`:

  ```sh
  $GUARD check
  $GUARD run --timeout <seconds> --log $SCR/logs/<task-id>-<n>.log -- <command>
  ```

  On Linux, invoke `python3 $CAMP/linux-guard.py check` and then
  `python3 $CAMP/linux-guard.py run --timeout <seconds> --log <log>
  --cwd $WT -- <command>`. The accepted local guard uses two-CPU affinity,
  an 8 GiB aggregate RSS cap, an atomic host slot, Linux node RAM/PSI and
  incremental swap safeguards, and 100/50 GiB disk thresholds. Existing
  swap is the recorded baseline under the archived mailuefterl contract.
  Its synthetic behavior receipt is `notes/linux-guard-sol-evidence.tar.gz`.

  Never stop unrelated services or foreign jobs to obtain capacity.
- Cluster jobs request one task with an explicit memory limit, CPU allocation
  and time limit. Set Lean and native-library thread counts to the intended
  actual CPU count. Check whether memory cgroups enforce the request. If RAM
  enforcement cannot be verified, reserve ghost CPUs according to
  `max(actual_threads, ceil(job_memory / usable_memory_per_CPU))`, using the
  least favorable eligible node and leaving node memory headroom. Lean still
  uses only the actual thread budget. Ghost CPUs reserve the job's share of
  node RAM; they do not create a hard memory limit. Retain an aggregate RSS
  watchdog and refuse placement whose reservation cannot cover the budget.
  Current preflights show approximately 14.76 GiB/CPU on acluster and
  11.82 GiB/CPU on scluster; with 10% headroom, two reserved CPUs cover
  an 8 GiB job on either cluster. Recheck these ratios before submission.
- Every cluster allocation also runs our node safeguard. It requires
  available node RAM above the job cap plus a reserve of
  `max(8 GiB, 5% of node RAM)` before starting. During the job it polls
  aggregate RSS and node available RAM every 250 ms; it stops only our
  process group below that reserve, at serious memory pressure, or after
  1 GiB of additional node swap use. Serious pressure means Linux memory
  PSI `full avg10 >= 1%` or `some avg10 >= 10%` when PSI is available.
  Missing PSI is recorded as unknown; the RAM reserve remains enforced.
  Atomic live telemetry every two seconds records current/peak job RSS,
  node RAM, pressure, swap and timestamp. Terminal receipts record the
  minimum available RAM and exact stop cause. The controller and assigned
  host worker monitor the job handle and telemetry; cancel only our jobs
  if resource telemetry stops or Slurm reports memory trouble.
- Initial module/consumer jobs use 8 GiB and two threads. Full verification
  receives a separately recorded budget based on measured dependencies and
  scheduler capacity. A larger allocation needs a concrete resource reason;
  a proof elaboration timeout is repaired by splitting the proof.
- Standard timeouts: scratch file 900 s; one module `lake build` 2700 s;
  full library build 14400 s; `scripts/verify.sh` 21600 s.
- Single-file checks add a Lean memory cap:
  `lake env lean -M 8000 <file>` (the value is in MB).
- Exit codes and responses:

  | Code | Meaning | Action |
  | --- | --- | --- |
  | 90 | refused at start | Run `$GUARD check`. If another lake/lean runs, it is not yours: stop, report `blocked: foreign lean process`. If memory/disk is low, stop and report. Never kill processes you did not start. |
  | 91 / 94 | memory or swap kill (`reason=rss-cap`, `memory-pressure`, `memory` or `swap`) | Do not retry the same command. Split the file or the proof (section 6.3) and report. Two memory kills in one task: `blocked`. |
  | 92 | disk kill | Stop immediately, report `blocked: disk`. Never delete anything to make room. |
  | 93 | timeout | Look at the log for the last file compiled. Usually a proof is too heavy: split it. Do not raise the timeout yourself. |
  | 95 | sustained CPU oversubscription | Reduce concurrent compilation or thread use. Do not raise the CPU cap without a separately allocated resource budget. |

- **Disk hygiene.** Reuse the existing campaign `WT` and its fresh Linux
  rc3 cache under `/mnt/storage/stafford38-campaign-rc3-20261003/lake`.
  Cluster snapshots/build trees are isolated per accepted source input. Never
  copy Darwin build artifacts. Dependency/toolchain bootstrap is permitted
  only for the pinned Linux environment on a newly allocated check host,
  through the allocation guard after preflight; record unchanged manifest
  bytes and every package HEAD. Do not clean or replace existing caches.
  Keep command logs and terminal receipts; compress large logs.
- **Context hygiene (your memory).** Never print a whole log or a whole large
  file. Use `grep -n "error" <log> | head -20`, `tail -40 <log>`,
  `sed -n 'A,Bp' <file>`. Read Lean files in pieces of at most 150 lines.
  Keep each tool output under about 200 lines.

## 4. STATE.md and worker reports

### 4.1 Status values

`todo` → `doing` → `done`, or `retry` (controller reopened it), `blocked`
(needs the controller), `owner` (controller promotion gate). The controller
sets `doing` at assignment and records acceptance or the next repair action.
Several independent rows may be `doing` at once.

### 4.2 Ledger row

Each task row in `STATE.md` has: id, status, attempts (runs used), last log
path, one-line note (what was proved or the first error). The task may also
ask you to record numbers (build time, peak memory) under "Measurements".

### 4.3 Report block (last thing you print)

```
TASK: <id> <title>
RESULT: candidate | done | blocked
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

1. Reuse `/home/ert/proj/stafford38-qwen` on `campaign/paper-route-20261003`;
   it was restored from saved source `c3dccd4b3f93`. Preserve unrelated edits.
2. Use its fresh Linux rc3 cache, not MAIN’s historical Lean 4.33 cache.
3. For cluster checks, freeze the exact source commit plus complete binary
   patch and new-file manifest before creating an isolated Linux snapshot.
4. Bootstrap only the pinned toolchain and manifest dependencies under the
   allocated resource guard. Check manifest byte identity and all package HEADs.
5. Keep each host’s build artifacts isolated; never fetch them from a Mac.

Accept: source identity, Linux environment and pins match the selected input.
Existing T01 historical receipts remain unchanged.

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
  `Stafford38.Geometry.SameWitness`. Each file imports its actual data
  prerequisites and only the modules it needs (take them from the archived file's
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

  Both must print nothing in concrete constructions. Abstract-ring adapters
  following the T22 pattern may install the required instances locally;
  identify their generic ring variables and scalar-map equations in the report.
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

Completed3October2026: actual8af wrapper module and unchanged literal trust-zero consumer passed3127001; WT7d645f2 committed/pushed. The drained allocation subsequently failed the shared adapter assembly, recorded separately. See notes/T41-original-prime-linux-accepted-checks-20261003.md.

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

Completed3October2026: all four solution assemblies and terminal geometry passed3127814 after two small adapter elaboration repairs. T41 checks were reused. Exact19-source acceptance packet: notes/T42-four-assemblies-linux-accepted-20261003.md. Final single verifier and four comparators remain required.

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

Actualproductionfailure3October2026: final3128526 fullbuild passed4475jobs, theninspection lacked private Mathlib bodies because the guard selected the public environment view. Sol repairs only the inspection view and multiline marker parsing, preservingallstrictchecks; boundedactualproductioninspection mustpass before finalreplay. Failurepacket: notes/T73-dependency-guard-failure-3128526-20261003.md.

Owned: the files created by the archived patches:
`scripts/dependency-guard/*`, `tests/dependency-guard-fixtures/*`, and the
two hunks of `scripts/verify.sh` from the wiring patch.

1. `cd $WT && git apply --check $SCR/archive/dependency-guard-integration.patch`, then apply it.
   Same for `$SCR/archive/palomar-verifier-guard-wiring.patch`. If `--check`
   fails, stop and report the failing hunk. Do not hand-edit around it.
   At resumed WT `0340cf2`, the controller verified all 18 integration
   new-file payloads are already tracked and byte-identical to the archive.
   Reuse those files and apply only the still-applicable verifier wiring;
   retain this source-match evidence separately from fixture behavior tests.
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

### T45 Shared challenges and distinct solution variants

Keep `Challenge.lean` and `FixedSourceChallenge.lean` unchanged. Main
`Solution.lean` and `FixedSourceSolution.lean` use the checked same-witness
paper route. `AlternativeSolution.lean` and `AlternativeFixedSourceSolution.lean`
use the preserved generic/Laurent geometric endpoint through shared downstream
assembly. Check each solution in isolation against its original challenge and
check declaration dependencies to establish that the endpoints differ. Copy a
challenge only if the actual packaging contract requires it, with its statement
unchanged. Document the two routes in the release and owner handover.

### T46 Tidy the final package

Delete obsolete unused scaffolding and front doors after checking imports,
tooling and documentation references. Preserve historical verification receipts,
pinned dependencies and the useful alternative solution. Refresh retained roots
and run the complete verifier after cleanup. This cleanup is authorized by the
owner for this delivery; Git history preserves removed development material.

## 11. Phase 5: full verification on Linux

### T50 Full library build

The retained full build is the build stage of the single final Linux verifier
(T51/T73). Record its exit, wall time and peak RSS there. Do not add a separate
whole-library build before or after that run. Required bounded module/consumer
checks remain the way to repair individual proof failures before source freeze.

### T51 Repository verifier

Run `bash scripts/verify.sh` once on the frozen public source in the selected
Linux slot, together with the four actual `scripts/verify-palomar.sh` comparisons
in T72/T73. Reuse the already reviewed Linux driver. Its pinned tool bootstrap
and exact dependency checks remain mandatory; no optional second cluster replay
or duplicate verification run is required.

Accept: verifier and all four comparisons exit 0. Record the verification logs,
source commit, source hashes, exact pins, axiom/route checks and resource receipt
in the final Linux receipt. T50, T51 and T73 refer to this same accepted run.
If a command fails, repair that concrete failure and retain the failed receipt.

### T52 Status drafts (no authoritative edits)

Owned: `$CAMP/notes/T52-docs-proposal.md`.

Draft the replacement text for the `component_status` and `open_bridges`
entries of `$WT/docs/paper-route-alignment.json` and for the "Proof and
correspondence" paragraph of `$WT/STATUS.md`, citing the T51 receipt. Mark
nothing as released. The controller applies and reviews it.

### T53 OWNER GATE: integrate into main

Completed3October2026: controller integrated55 explicit accepted proof/tooling paths, registry owners and current source-scoped metadata. Challenges, pins and historical receipts remain preserved.

The controller reviews the branch (full diff, frozen evidence and statement
diffs), then performs the already authorized integration and push. Workers
do not merge or promote candidates.

## 12. Phase 6: readability and duplication pass (report-first)

The owner now authorizes removal of obsolete unused material. Keep the useful
older solution route as a labeled alternative. Determine actual import, test,
review-map and release consumers before deleting; preserve pinned dependencies,
unchanged challenges and the evidence needed for the final release. Git history
retains prior candidate scaffolding. The controller integrates cleanup and runs
the complete verifier afterward.

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
`/home/ert/proj/stafford38-paper/human_readable_main.tex` (search with
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

The controller performs the authorized cleanup in this delivery, preserving
the useful alternative route and all still-used proof/review interfaces.

## 13. Phase 7: Linux replay and Palomar comparisons

### T70 OWNER GATE: frozen public commit

Completed3October2026: immutable public45037fbc16329df7a208eb3de91aca31d720f03c pushed before finaljob3128039.

After bounded proof module/consumer acceptance and integration, the controller
pushes the candidate source for the single final Linux/Palomar verification
and records its exact commit in `STATE.md` under "Frozen commit". Workers
use that immutable public source for all release and replay inputs.

### T71 Preflight the selected Linux replay host

Owned: `STATE.md`.

```sh
ssh mailuefterl 'hostname; nproc; free -g | head -2; df -h /mnt/storage | tail -1; pgrep -a lean | head; pgrep -a lake | head'
```

For local replay, accept `hostname` mailuefterl, at least 100 GiB free on
`/mnt/storage`, at least 64 GiB available RAM and no foreign Lean/Lake.
If node-pressure guards repeatedly stop otherwise bounded checks, select
an approved acluster/scluster node allocation instead. Require the reviewed
two-CPU/8GiB guard, verified job/step placement, node RAM/PSI/swap/disk
safeguards and a fresh source directory. Record the chosen host and reason.

### T72 Launch the frozen Linux driver

Launched3October2026 as scluster3128039, soleapprovednode20 two-CPU/8GiB allocation, exactpublic45037fb. T50/T51/T73 share this one run plus four comparators. Luna monitors receipts; no duplicatecluster orcandidatewhole-verifier launch.

Owned: fresh snapshot directory; host-specific replay contract; `STATE.md`.

The archived mailuefterl contract below remains the local replay recipe.
For a cluster fallback, prepare and independently review a separate driver
and contract before launch. It must archive only the T70 immutable public
commit, verify source and manifest hashes before/after, check every dependency
pin and all four challenge/solution comparisons, and preserve the ordered
repository verifier and terminal receipts. Run it inside the accepted srun
allocation guard. Record its script hashes and scheduler handle; do not edit
the archived contract to imply that it covered a different host or source.

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

Concrete tooling failure3October2026:3128039 stopped before any full verifier/comparator because bwrap0.8.0 did not meet required0.12.0. See notes/T73-tooling-failure-3128039-20261003.md. Repair only the isolated tooling, then resume the same byte/mode-checked public clone with separate receipts; the completed cache copy is reused. No full proof run has yet occurred.

Owned: `STATE.md`, `$CAMP/notes/T73-linux-receipt.md`.

Poll the exact recorded process handle (or recorded Slurm job/step for a
cluster fallback):
`ssh mailuefterl 'ps -p <pid> -o pid,etime,cmd; tail -5 <log>'`.
While it runs, leave T73 `doing` and continue independent bundle work.
An observation timeout is not termination; revalidate the same handle and
terminal receipt, and never restart merely because a poll timed out.
When it has finished, copy the receipt
files named in the contract back to `$CAMP/notes/linux-receipt/`, record exit
status and the comparator results for both challenges, and mark `done` only
if every ordered command passed.

### T74 OWNER HANDOVER: Palomar-ready package

The owner will perform Palomar’s online submission. Deliver the immutable
source/release links, unchanged challenges, paper-conforming main solution,
labeled alternative solution and local source-policy/kernel-comparison receipts.
Record exact submission commands and target names. Do not dispatch or register
online on the owner’s behalf. Official online status remains pending until he
submits; the historical dispatch contract remains in the archived dossier.

## 14. Phases 8–9: review bundle and release

### T80 Re-anchor the review map

Owned: `$WT/docs/paper-lean-audit/*` map file named by the script's `--map`
argument (find the current map with `ls $WT/docs/paper-lean-audit`).

```sh
cd $WT && python3 scripts/reanchor-review-map.py --paper /home/ert/proj/stafford38-paper \
  --paper-file human_readable_main.tex --map <map file>
```

Then add rows for the new SameWitness theorems from the T61 table. Accept:
the script exits 0 and mapped declarations resolve at the frozen sources.
After the accepted build, use guarded `lake env lean --trust=0` with scratch
`#check` files, without another full build. Keep four import groups separate:
main/shared declarations, Challenge alone, FixedSourceChallenge alone, and
both alternative solutions. Root challenges and proof modules deliberately
reuse names and cannot be imported together. The two archived Global Stafford
references are source-only provenance outside this package's build dependencies;
check their exact archived source locations separately. These name checks do
not certify the challenge placeholders or whole-proof correspondence.

Each mathematical claim must have a stable review entry in paper order,
covering the complete proof and both Challenge/Solution comparisons. Record
the paper passage, exact Lean statement, relevant definitions and hypotheses,
supporting lemma statements, and links to their sources at the frozen commits.
Label manuscript corrections, correspondence gaps, and alternative solution
variants explicitly. Keep the paper-conforming main route distinct from the
alternative route and preserve the unchanged challenge statements.

### T81 Build the review site

`cd $WT && $GUARD run --timeout 3600 --log $SCR/logs/T81.log -- python3 scripts/build-review-site.py`
(read its `--help` first). Record output paths. The interface must make Max's
complete review easy to follow with low mental load:

- Provide one starting link and a guided sequence in paper order, with one
  mathematical claim per review entry and previous/next navigation.
- Show the paper passage and corresponding Lean statement together, with
  plain-language explanations of the definitions and hypotheses that matter.
- Link directly to exact paper locations, Lean declarations, and supporting
  definitions and lemma statements at the frozen commits. Make custom
  dependency interfaces accessible without searching through subpackages.
- Keep technical boilerplate collapsed by default, with access to supporting
  proof details. Keep mathematical assumptions and known gaps visible.
- Mark proposed paper corrections, incomplete correspondence, and the
  alternative solution route. Show verification evidence separately from
  mathematical correspondence and human review status.
- Provide a checklist keyed to stable review entries, with a way to record
  findings and resume from the last reviewed claim. Reading the bundle must
  require no Lean installation or private repository access.

Accept: build exits 0 and a browser walkthrough follows the complete claim
sequence from the starting link. Check every generated paper/source link and
record broken links, missing claims, or places requiring a manual repository
search in the T81 receipt; resolve these before accepting the interface.
Max must be able to follow the complete correspondence without manually
hunting across repositories, while retaining access to every supporting detail.

### T82 Rebuild the manuscript PDFs (no text edits)

In `/home/ert/proj/stafford38-paper`, following its README:

```sh
latexmk -pdf human_readable_main.tex && latexmk -pdf lean_proof_details.tex && latexmk -pdf main.tex
grep -c "undefined" human_readable_main.log lean_proof_details.log main.log
```

Accept: three PDFs, zero undefined references. Workers do not edit `.tex`
files. The controller may repair source locators and apply the requested final
citations after fetching the Overleaf authority. Preserve Johanna's visible
proof and keep mathematical proposals explicitly pending her review.

### T83 Supplementary bundle (local only)

In `/home/ert/proj/stafford38-supplementary`, follow steps 2–4 of
`docs/release-preparation.md` with the frozen commits. Run
`python3 scripts/rebuild.py`. Do not create tags, releases or DOIs.
Record every check in `$CAMP/notes/T83-supplementary-receipt.md`.

### T84 OWNER GATE: review handover

Johanna reviews the mathematical prose and marked proposals; Max reviews the
complete paper/Lean correspondence. Prepare their concrete review package
here, including the T81 starting link, pinned input revisions, review checklist,
and instructions for recording findings. Explain Max's review scope through
definitions, hypotheses, and supporting lemma statements; link the build,
kernel-comparison, and transitive axiom-audit evidence for formal verification.
Keep both human reviews pending and identify Johanna's marked proposals on
the selected manuscript, with Overleaf as the editing authority.
The controller sends the owner's
requested short email after both releases, archive checks and citations.

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

After the controller records each published Zenodo record id in `STATE.md`, download the
archive as described in the template, compare every file byte for byte
with the tag (`git -C $WT archive <tag> | tar -t` against the unpacked
archive, then `shasum -a 256` per file), and write
`$CAMP/notes/T92-zenodo-receipt.md` with counts, extras and mismatches.
Accept: zero mismatches.

### T93 Citation drafts

Owned: `$CAMP/notes/release/citations.md`. Draft the updated citations
for the formal repository, the paper and the supplementary bundle with the
verified new DOIs. The controller applies them and synchronizes Overleaf as
authorized by the current campaign request.

### T94 Final review emails

After both releases, both zero-mismatch Zenodo archive checks and final paper citations are complete, send the authorized short English emails: Johanna at j.moser@tugraz.at reviews the marked manuscript corrections on Overleaf; Max at philipp@student.tugraz.at uses the guided tooling for the complete Lean–paper comparison. Sign each with Chris&AI and record delivery. Human review and online Palomar registration remain owner follow-up actions.

When T93 and T94 are done, the campaign is complete. Report `RESULT: campaign complete` and stop.
