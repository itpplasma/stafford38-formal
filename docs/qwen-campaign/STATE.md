# Qwen campaign state

Plan: `PLAN.md` in this folder. The controller updates task rows,
measurements, hints, frozen commits and promotion gates. Parallel Luna
workers and subagents return candidates and evidence; failed tasks escalate
to Sol. Historical Pi/Qwen records remain preserved.

## Tasks

| Id | Title | Status | Attempts | Last log | Note |
| --- | --- | --- | --- | --- | --- |
| T00 | Resource and state check | done | 1 | docs/qwen-campaign/notes/T00-check.log | GUARD OK; 116 GiB free RAM, 553 GiB free disk, no foreign lake/lean; MAIN clean outside docs/qwen-campaign |
| T01 | Create campaign worktree | done | 1 | docs/qwen-campaign/notes/T01-worktree.log | WT at /Users/ert/proj/stafford38-qwen on qwen/paper-route @2a9c264; .lake APFS clone (cp -cR, 22 s, df delta 0 GiB); manifest identical, toolchain leanprover/lean4:v4.35.0-rc3 |
| T02 | Baseline build of prerequisites | done | 2 | docs/qwen-campaign/notes/T02-check.log | baseline OK: lake build of the 11 prerequisite modules exit=0, 3148 jobs, 0 errors, no Mathlib compile/fetch; consumer check exit=0 (axioms propext/choice/Quot.sound only) |
| T10 | Extract archived candidates | done | 1 | docs/qwen-campaign/notes/T10-extract.log | 9 files / 2164 lines extracted to SCR/archive; repair4 5 files (closure 446, A0Etale 332, axis lift 123, away 70, consumer 35) + 4 patches; closure-frontier.txt read |
| T11 | Port AwayFactorToAtPrime | done | 1 | docs/qwen-campaign/notes/T11-check.log | ported to Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean, namespace Stafford38.Geometry.SameWitness, statements byte-identical; build exit 0 (10 s, 1579 jobs); consumer exit 0, axioms propext/choice/Quot.sound only; reused Mathlib IsLocalization.Away.lift + lift_comp (replaces archived ext/simp), map_units; commit 134f04b; flag: nothing imports the new module yet, so T43/T50 must add it to a root list or check it by name |
| T12 | Port axis lift from ground point | done | 1 | docs/qwen-campaign/notes/T12-check.log | ported to Stafford38/Geometry/SameWitness/AxisLiftFromGroundPoint.lean, namespace Stafford38.Geometry.SameWitness, docstring+statement byte-identical (diff exit 0), maxHeartbeats 4000000->1600000; build exit 0 (10 s, 3079 jobs, 4.9 s for the module, 0 errors); consumer exit 0 axioms propext/choice/Quot.sound; proof needed no repair - reuses exists_actual_point_axis_lift + T11 pair_factorizations_to_atPrime, no new instances beyond the frozen let-block; commit 8ef595c; flag: still not in any root list, T42/T43/T50 must wire or check by name |
| T13 | Port chart ground-map lemma | done | 1 | docs/qwen-campaign/notes/T13-check.log | ported repair4 addition (archived lines 280-328) to Stafford38/Geometry/SameWitness/ChartGroundMap.lean, namespace Stafford38.Geometry.SameWitness, theorem signature byte-identical (diff exit 0), maxHeartbeats 2400000->1600000; A0ChartFormalEtale.lean untouched; build exit 0 (10 s, 2927 jobs, module 1.8 s, 0 errors); consumer exit 0 axioms propext/choice/Quot.sound; reuses originalAffineChartToCommonOpen + originalAffineChartOverlapEquiv + selectedChartAwayEquivOfQuotientEquiv + genericOpenBMap_base_eq + Mathlib IsLocalization.Away.map/IsScalarTower.algebraMap_apply; no new def; matches repair3-groundmap-audit PASS on 4.33; commit 0340cf2; flag: frozen statement carries `letI : Algebra Q U := Algebra.compHom U _` (rule 6.2.8 diamond source) - T34/T36 must use the hom equation, not a second Algebra on U; still not in any root list, T43/T50 must wire or check by name |
| T20 | Instance inventory | done | 2 | docs/qwen-campaign/notes/T20-diagnostics.tar.gz | Sol completed concrete nine-ring and ten-prerequisite inventory after Luna acceptance failed; inherited Q/B,Q/F,Q/U,k/U and staged R/U duplicates; default synthesis timeouts preserved; 264 source hashes and five log hashes checked |
| T21 | Minimal tower reproducer | done | 1 | .lake/qwen/logs/T21-luna-2.log | Mathlib quotient and abstract hom towers compile; frozen negative probe captures oldTower/compHom action mismatch; guarded final exit0,10s; receipt in notes/T21-repro.md |
| T22 | Ring-hom form of the endpoint | doing | 1 | | Luna implementing generic endpoint and literal consumer; guarded Lean slot assigned |
| T30 | Chart and away data | doing | 1 | | Luna preparing chart setup in parallel; checks queued with controller |
| T31 | Coordinate presentation | todo | 0 | | |
| T32 | Maximal ideal and common open | todo | 0 | | |
| T33 | Arc into Laurent series | todo | 0 | | |
| T34 | Columns, derivatives, numerator | todo | 0 | | |
| T35 | Étale structure as ring homs | todo | 0 | | |
| T36 | Same-witness closure theorem | todo | 0 | | |
| T40 | Import-cycle check | todo | 0 | | |
| T41 | Original-prime wrapper | todo | 0 | | |
| T42 | Rewire terminal geometric theorem | todo | 0 | | |
| T43 | Strict dependency guard | todo | 0 | | |
| T44 | Literal route consumers | todo | 0 | | |
| T50 | Full library build | todo | 0 | | |
| T51 | Repository verifier | todo | 0 | | |
| T52 | Status drafts | todo | 0 | | |
| T53 | Integrate into main | owner | 0 | | owner gate |
| T60 | Definition owners patch | todo | 0 | | |
| T61 | Paper map of new theorems | todo | 0 | | |
| T62 | Unreachable/duplicate report | todo | 0 | | |
| T70 | Frozen public commit | owner | 0 | | owner gate |
| T71 | Remote preflight on mailuefterl | todo | 0 | | |
| T72 | Launch Linux driver | todo | 0 | | |
| T73 | Collect Linux result | todo | 0 | | |
| T74 | Official Palomar dispatch | owner | 0 | | owner gate |
| T80 | Re-anchor review map | todo | 0 | | |
| T81 | Build review site | todo | 0 | | |
| T82 | Rebuild manuscript PDFs | todo | 0 | | |
| T83 | Supplementary bundle (local) | todo | 0 | | |
| T84 | Review handover | owner | 0 | | owner gate |
| T90 | Release drafts | todo | 0 | | |
| T91 | Signed tag, release, Zenodo | owner | 0 | | owner gate |
| T92 | Verify Zenodo archive | todo | 0 | | |
| T93 | Citation drafts | todo | 0 | | |

## Current execution (resumed 2026-10-03 by owner)

- The active user instruction resumes the full campaign, authorizes regular commits/pushes and both releases, and requests the final review email after completion.
- Workers use `gpt-6-luna`; failed bounded tasks escalate to Sol. No Qwen/Pi campaign driver is used in this resumed run.
- The owner's follow-up explicitly replaces serial task selection with heavy parallelism. Independent workers/subagents prepare disjoint candidates concurrently; actual dependencies govern acceptance. The controller schedules the shared guarded Lean queue.
- The controller owns authoritative state, integration, commits, pushes and promotion. Workers return evidence without committing or changing the ledger.
- Lean execution remains serial through `guard.sh`; pins, archived receipts, mathematical statements and protected-host restrictions remain in force.
- Resume preflight: MAIN `ecedcf5`, WT `0340cf2`, both clean; guard OK, 104 GiB free RAM, 553 GiB free disk, no lake/lean processes.

## Previous resume instructions (historical)

- Plan: `docs/qwen-campaign/PLAN.md` (work order, 43 tasks); ledger: this file; worker prompt: `prompt.md`.
- Driver: `cd docs/qwen-campaign && nohup ./drive.sh 9 "T22 T36 T42 T43 T51" > runs/drive4.out 2>&1 &`
  (serial; stops at the checkpoints listed; `guard.sh` protects RAM/disk; Pi via `run-pi.sh`, use PI_RUN_FIRST_OUTPUT_TIMEOUT=14400).
- Next task: T20. Worktree `/Users/ert/proj/stafford38-qwen` on branch `qwen/paper-route` (Lean work); this ledger lives on MAIN.
- Gateway: Pi uses provider `itpcp` -> slopgate :8090. Do not restart slopgate/adapters while Pi runs.
- Owner gates (T53, T70, T74, T84, T91) need the owner. Never touch faepop*/faepcr*.

## Measurements

- Free memory / disk at T00: 116 GiB truly free (guard), swap used 0 GiB, pressure normal; disk 553 GiB free of 1.8 Ti on /System/Volumes/Data
- MAIN commit at T00: 2a9c264c5ad881fec8f70b9ad0d53861b72279b0 (branch main; untracked only docs/qwen-campaign/run-pi.sh, docs/qwen-campaign/runs/, docs/qwen-campaign/notes/)
- T02 prerequisite build (wall time, peak RSS, jobs): attempt 1 first compile pass in WT 91 s wall, peak_rss 2 GiB, 3148 jobs, exit 0 (.lake/qwen/logs/T02-attempt1.log); attempt 2 re-check all up-to-date 10 s wall, peak_rss <1 GiB, 3148 jobs, exit 0 (.lake/qwen/logs/T02.log); guard never refused, no `fetching revision`, no `Building Mathlib`
- Single-file check turnaround: 10 s wall, peak_rss <1 GiB (`lake env lean -M 32000 tests/ActualSameWitnessGroundPointCompletionConsumer.lean`, exit 0)
- T02 provenance note for the controller: two WT sources differ from the cache donor `stafford38-rc3-final-worker`. Lake recompiled `A0ChartFormalEtale`, `A0NormalizedProjectiveCoordinates`, `ActualWitnessSelectedChartBinding`, `ActualWitnessCommonOpenColumnGlue` from the WT sources; it accepted the cloned olean for `GeneralAsymptoticConormal` by content trace, and that file was elaborated separately from the WT source (exit 0, log `.lake/qwen/logs/T02-oracle-gace.log`). See notes/T02-check.log.
- T10 archive line counts (SCR/archive, 9 files, 2164 lines total): repair4/Stafford38/Geometry/A0ChartFormalEtale.lean 332; repair4/Stafford38/Geometry/ActualSameWitnessAffineFibreClosure.lean 446; repair4/Stafford38/Geometry/AwayFactorToAtPrime.lean 70; repair4/Stafford38/Geometry/GroundPointAxisLiftFromOutput.lean 123; repair4/tests/ActualSameWitnessAffineFibreClosureConsumer.lean 35; assembly/assembly-wrapper.patch 193; dependency-guard-integration.patch 828; literal-route-consumers.patch 115; palomar-verifier-guard-wiring.patch 22. repair4 sources are old 4.33 style (plain `import`, no `module` header); `originalAffineChartToCommonOpen_groundMap` present at archived A0ChartFormalEtale.lean:282 (for T13).
- T11 port build / consumer (wall time, guard reason): build exit 0, 10 s wall, peak_rss 0 GiB, 1579 jobs (`.lake/qwen/logs/T11-3.log`; attempts 1–2 failed on a stuck `IsLocalization.Away ?m ?m` instance in the hand-written `hψ`, fixed by reusing `IsLocalization.Away.lift_comp` with explicit `R`/`S`/`P`/`x`); consumer `lake env lean --trust=0 -M 32000 tests/SameWitness/AwayFactorToAtPrimeConsumer.lean` exit 0, 11 s wall (`.lake/qwen/logs/T11-consumer.log`), axioms `[propext, Classical.choice, Quot.sound]` for both consumers
- T12 port build / consumer (wall time, guard reason): build exit 0, 10 s wall, peak_rss 0 GiB, 3079 jobs, module itself 4.9 s, 0 errors, 5 linter.unusedVariables warnings on frozen-statement binders (`.lake/qwen/logs/T12-1.log`); consumer attempt 1 exit 1 (`#print axioms` named a constant without the `_consumer` suffix), attempt 2 `lake env lean --trust=0 -M 32000 tests/SameWitness/AxisLiftFromGroundPointConsumer.lean` exit 0, 10 s wall (`.lake/qwen/logs/T12-consumer.log`), axioms `[propext, Classical.choice, Quot.sound]`; guard never refused, no `fetching revision`, no `Building Mathlib`
- T13 port build / consumer (wall time, guard reason): build exit 0, 10 s wall, peak_rss 0 GiB, 2927 jobs, module itself 1.8 s, 0 errors (`.lake/qwen/logs/T12`-style cached warnings only; `.lake/qwen/logs/T13-2.log`); consumer attempt 1 exit 1 (`Unknown identifier` for `exact` after stripping `:= by` from the frozen statement), attempt 2 `lake env lean --trust=0 -M 32000 tests/SameWitness/ChartGroundMapConsumer.lean` exit 0, 10 s wall (`.lake/qwen/logs/T13-consumer-2.log`), axioms `[propext, Classical.choice, Quot.sound]`; guard never refused, no `fetching revision`, no `Building Mathlib`
- T50 full build (wall time, peak RSS):
- T51 verifier (wall time):

## Frozen commit

(controller/owner only)

## Controller hints

(controller only; Pi reads the hints for its task before starting)

- T02: The controller already replaced `WT/.lake` with a clone of the rc3 build
  cache of `stafford38-rc3-final-worker` and aligned the package git remotes
  to the manifest URLs (MAIN's `.lake` is the old 4.33 cache and must not be
  used). Do not run `lake update`/`cache get`. Just run the T02 build through
  guard.sh. If lake prints `fetching revision` or starts compiling Mathlib
  modules (`Building Mathlib.`), kill it via the guard timeout and report
  `blocked`: that means the cache does not match. Compiling `Stafford38.*`
  modules is expected.

- T35: `SameWitness/ChartGroundMap.lean` (T13) contains the archived lemma with a local
  `Algebra Q U := Algebra.compHom …` inside its own proof. That is the only place it may live.
  Do not use that lemma's instance in later files: use only its *conclusion*, the equation
  `φ.comp (algebraMap k A₀) = algebraMap k U`, and build `φk : A₀ →ₐ[k] U` from it.
- T22/T36: if Lean rejects a `FormallyEtale` or tower statement for `U`, do not install instances
  on `U`; adapt over an abstract ring (PLAN 6.2 rule 4).

- T20 resumed review: archived import `GroundPointAxisLiftFromOutput` has no WT source
  but is present in the cloned cache. Diagnostic scratch imports must use the accepted
  `SameWitness.AxisLiftFromGroundPoint` rename and resolve every project import to source.
  A green abstract probe assuming scalar actions is conditional evidence, not a concrete
  witness inventory. Pair each frozen scratch hash with its own real log; record missing
  synthesis and timeouts as diagnostics instead of adding assumptions or raising budgets.

## Blocked

(Pi: one line per blocked task with the path of its `notes/<id>-blocked.md`)
