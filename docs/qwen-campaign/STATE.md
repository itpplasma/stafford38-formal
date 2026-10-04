# Qwen campaign state

## Current review/release snapshot

Formal v1.3.1 `f9448d6307fa25aff9d9f94ce0a9c7f9b03e63ff`, DOI10.5281/zenodo.23127367, and supplementary v0.2.2 `a114b06749fb01cf352f8b13ad3fda8267293ac6`, DOI10.5281/zenodo.23132562, are published. Their archives match all 1,172 and 16 tagged files with zero missing files, extras or mismatches. The current reader shows complete Lean proof bodies beside the manuscript, with direct source links, optional annotations and review notes. Obsolete supplementary logs, status pages, duplicate receipts and nested archives were removed; release downloads provide the offline HTML and journal supplements.

Selected review source remains P7 `760c68d2d79a8fd2c4b58f35f32dd90969591300` / S7 `9f6ca3241edcf88da42a3a000f25514d105e2f30`, synchronized to GitHub and Overleaf. The immutable v0.2.2 companion freezes P7/S7/R131 and the matching PDFs. All 654 protected proof/tool files in formal v1.3.1 match C2; descriptor provenance and package-version exceptions are recorded. The complete C2 verifier, all four local Palomar comparisons and 399 public-name checks passed and were not repeated. T96 validates the changed reader: 71 generator tests passed; all 504 displayed Lean excerpts match their pinned source ranges; desktop/mobile/offline reading, formula annotations, notes and export passed. Both Pages deployments succeeded.

The current ledger is `docs/paper-lean-audit/review-status.json`. It classifies proposed corrected review text, preserves original findings and records both human reviews pending. Current statement labels are exact21/equivalent11/Lean-stronger9/partial8/n/a8; routes same18/similar13/Lean-only1/n/a25. Paper-wrong, not-formalized and different-route counts are zero; the genuine scope limits remain visible. Final live HTTP source pins,57 cards and both PDF hashes passed; both authorized handovers were sent with mail-service sent=true. The campaign is complete. Johanna/Max reviews remain human follow-ups. Palomar v3 registered source `0bb3aa929b931bf5d82d90f62d7508d3ae1dccc1` on 4 October 2026 with comparator.json. Its 587 Lean/configuration files match R131; T97 records exact source scope and the paper’s updated v3 citation.

Owner steering and earlier checkpoint history, 3 October 2026: finish the proof as the immediate
priority, faithful to Johanna’s original manuscript proof with necessary
corrections. Execute only on local Linux `mailuefterl` and Linux allocations
on `acluster`/`scluster`. Mac execution and candidate synchronization are no
longer authorized. All campaign Mac checks had already ended at this steering;
no new Mac action is scheduled. Historical Mac receipts remain unchanged.
T32’s frozen source passed its Linux module and unchanged trust-zero consumer
checks. T33 and T35 passed Linux module and literal trust-zero consumers. T35's frozen
sourcef30 passed on scluster3113113 with only three permitted axioms, zero
pressure/swap growth and no survivors; committed at WT4c1678e. T34 positions passed module and literal trust-zero consumer and is committed
WT1a3fcfd. The controller validated the exact private test-name report after
a wrapper-name mismatch. Corrected wrapper3115702 confirmed positions again,
then Columns468 failed actual compilation. Sol's abstract derivative
certificate08db failed the Laurent action/tower match in scluster3116538.
T34 Columns actual modules and unchanged literal consumer passed3125101
and are committed/pushedWT1fedc6e, with only three permitted axioms. The
allocation drained normally; see notes/T34-columns-linux-accepted-checks-20261003.md.
Earlier conversion diagnostics are preserved in notes/T34-memory-block-20261003.md.
Full Closure4307877 and its unchanged unconditional literal trust-zero
consumer passed3126415, with only three permitted axioms and guard0/drained,
and are committed/pushedWT5607e3e. The strengthened canonical-map Etale
interface passed3126127 and is committed/pushedWT3be4598. Both acceptance
packets and earlier scoped failures remain in notes. Original-prime module/consumer and all four solution assemblies passed their bounded Linux checks; final public verifier/comparators are next. T35 also passed independently on acluster21805719. Both cluster
bootstraps passed exact pins and T32. Alternative geometry endpoint passed
scluster3114679, committedWT71e966a; full alternative assembly/comparators
remain required. Actual guard fixtures passed3112916. No guard or proof
claim was weakened.
Both clusters use reviewed two-CPU/8GiB allocation guards. See the scoped
bootstrap/fixture receipt in notes/scluster-bootstrap-fixture-20261003.md.
One delivery: finish the faithful proof, cut matching formal/supplementary
releases, verify both Zenodo archives, and cite them from the paper. Challenge
statements stay unchanged; main solution follows the paper, with the older
route preserved as a labeled solution variant. Tidy obsolete unused material.
The owner performs Palomar online submission; we deliver local checks/package.

Synchronization checkpoint, 3 October 2026: incoming campaign documents and notes were preserved at `origin/wip/sync-20261003/faepmac1/stafford38-formal` (`4fed8b73c008`). The latest proof files are separately preserved at `origin/wip/sync-20261003/faepmac1/stafford38-qwen` (`c3dccd4b3f93`). See [the controller branch map](../../PLAN.md#branches-for-resuming-saved-work) and [exact snapshot manifest](../synchronization-2026-10-03.json). Rows marked `doing` remain preparation awaiting acceptance; synchronization does not resume jobs or certify candidates. No local Stafford executor was observed on faepmac1 at 05:40 UTC.

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
| T22 | Ring-hom form of the endpoint | done | 2 | notes/T22-accepted-checks.tar.gz | Sol removed two redundant rfl tactics; module and trust0 consumer exit0,5s each,peak2009/1860MiB,three allowed axioms; statement unchanged; static audit reanchored PASS; WT commit e2ba158 |
| T30 | Chart and away data | done | 1 | notes/T30-accepted-checks.tar.gz | Luna module/consumer exit0,7/3s,peak2.1/0.9GiB,three allowed axioms; existing numerator/chart owners retained; WT commit ef715e7; independent Linux module and trust0 consumer also passed (notes/linux-baseline-20261003.md) |
| T31 | Coordinate presentation | done | 6 | notes/T31-reindex-accepted-checks.md | Canonical fFin accessor fixes missing map relation; Linux module/unchanged trust0 consumer pass,three permitted axioms; independent Mac module pass23s/2182MiB; WT8fa692f pushed; full-route verifier pending |
| T32 | Maximal ideal and common open | done | 9 | notes/T32-linux-accepted-checks.md | Frozen8656c5e module/unchanged trust0 consumer passed on Linux210s/2.28s,peak3865/2745MiB,three permitted axioms; WTda00639 pushed; full-route review pending |
| T33 | Arc into Laurent series | done | 4 | notes/T33-linux-accepted-checks.md | Sol module/unchanged-statement trust0 consumer passed41.01s/2.28s,peak4139/2746MiB,three permitted axioms; committed and pushed; full-route review pending |
| T34 | Columns, derivatives, numerator | done | 29 | notes/T34-columns-linux-accepted-checks-20261003.md | Actualmodules+unchangedtrust0consumer PASS3125101,3axioms,drained; committed/pushedWT1fedc6e. Positions9417 accepted earlier |
| T35 | Étale structure as ring homs | done | 7 | notes/T35-canonical-map-linux-accepted-checks-20261003.md | Strengthened3c79 module+unchangedconsumerPASS3126127,3axioms; controller validated namespace after wrapper mismatch. Drained; committed/pushedWT3be4598 |
| T36 | Same-witness closure theorem | done | 10 | notes/T36-closure-linux-accepted-checks-20261003.md | Full4307877 module+unchangedunconditionaltrust0consumerPASS3126415,3axioms,guard0/drained; committed/pushedWT5607e3e |
| T40 | Import-cycle check | done | 2 | notes/T40-imports.md | Both current roots exist;272modules/582edges, no forbidden or missing sources. Rerun if imports change; proof acceptance separate |
| T41 | Original-prime wrapper | done | 3 | notes/T41-original-prime-linux-accepted-checks-20261003.md | Actual8af module+unchangedconsumerPASS3127001,3axioms; drained; committed/pushedWT7d645f2. Subsequentassemblyfailed separately |
| T42 | Rewire terminal geometric theorem | done | 5 | notes/T42-four-assemblies-linux-accepted-20261003.md | Sharedterminal+4solutionsPASS3127814,3allowedaxioms,guard0/drained; WTe380306 pushed. Earlier2adapter failures retained |
| T43 | Strict dependency guard | done | 9 | notes/T73-strict-guard-all-routes-linux-accepted-20261003.md | Actual4terminalroots+independentfixtures+main/alt required/excluded routes PASS3129931; guard0/3.05GB/zero swap/nochildren |
| T44 | Literal route consumers | done | 1 | finalC2-resume3131801 | All116consumerfiles completed;317 requiredimport/axiomreports PASS. Five exactclosure/originalprime reports each once, exactly3allowedaxioms; wholeverifier/drain stillpending |
| T45 | Shared-challenge solution variants | done | 4 | docs/verification-results.json | All4 actualPalomarcomparatorsPASS3137241; sharedchallenges unchanged; main/alternative routes strictly checked |
| T46 | Tidy final package | done | 3 | README.md; STATUS.md; docs/verification.md | Retired wrappers/unusedfragments removed, usefulmath/history retained; main/variantstatus and4localPalomarcommands ready |
| T50 | Full library build | done | 2 | finalC2-resume3131801 | Fresh exactC2 fullbuildPASS4475jobs (mtime16:41:29Z afterverifierstart16:32:53Z); historicalC1build retained; completeverifier acceptance separate |
| T51 | Repository verifier | done | 3 | notes/T73-full-verifier-pass-retained-target-failure-3131801-20261003.tar.gz | ExactC2 fullverifierPASS3131801 at18:28:39Z;4475build/317consumer/111names/37axioms/allroutes. Laterdriver125 and remainingcomparisons/source-after gates are T73 |
| T52 | Status drafts | done | 3 | README.md; STATUS.md; docs/paper-lean-audit/review-status.json | Final P7/S7/R131 review scope and both verified archives recorded; human reviews pending |
| T53 | Integrate into main | done | 1 | notes/T42-four-assemblies-linux-accepted-20261003.md | Controllerintegrated55explicitproof/toolpaths afterboundedacceptance; authoritative docs and unrelateduntracked preserved |
| T60 | Definition owners patch | done | 4 | notes/T80-399-public-names-linux-accepted-3139266-20261003.tar.gz | All399 publicowner/name checksPASS exactC2;11private+2Global source-only; humanreviewpending |
| T61 | Paper map of new theorems | done | 4 | notes/T80-399-public-names-linux-accepted-3139266-20261003.tar.gz |57cards/519refs exactpins;399publicnamescompilerPASS; whole-papercorrespondence humanreviewpending |
| T62 | Unreachable/duplicate report | done | 2 | notes/T62-current-reachability-20261003.md | Frozen580sources/138roots:572reachable,244/246geometry;2useful unimportedmodules retained and full-build covered; no deletion proposed |
| T70 | Frozen public commit | done | 2 | notes/T73-final-C2-submission-3131361-20261003.json | Exact publicC2=12ae3cc49152672a48a96f13994314b65ae38197 pushed before final launch; priorC1 retained |
| T71 | Final Linux host preflight | done | 2 | notes/T73-final-C2-submission-3131361-20261003.json | Prior3129931guard0/drained; empty userqueue/node20idle;3controlhashes exact; fresh source/receiptpaths absent |
| T72 | Launch Linux driver | done | 6 | notes/T73-final-C2-resume4-submission-3137241-20261003.json | SoleS3137241 allocation-localdevice/cachelayout repair+4comps/finalintegrity exactC2; no completedcheck repeat |
| T73 | Collect Linux result | done | 6 | notes/T73-four-Palomar-comparisons-linux-accepted-3137241-20261003.tar.gz | R1verifier/R2retained/R4all4comparatorsPASS; final1095filemanifest+10pins exact; guard0/no stops/children/swap |
| T74 | Palomar registration | done | 2 | notes/T97-Palomar-v3-registration-and-citation-20261004.json | Immutable v3 registered at 0bb3aa9; main comparator passed all three kernels; automated review identified no problems; proof/configuration files match R131 |
| T80 | Re-anchor review map | done | 4 | notes/T80-399-public-names-linux-accepted-3139266-20261003.tar.gz |393+2+2+2 actualnamechecksPASS;3139266guard0/no stops/children/swap; no proofchange |
| T81 | Build review site | done | 3 | notes/T81-P7-S7-R131-final-live-receipt-20261003.json | Public HTTP200, exactP7/S7/R131 pins,57cards/currentlabels and both actualPDFhashes PASS; earlier57-card browserwalk inherited |
| T82 | Rebuild manuscript PDFs | done | 5 | notes/T82-P7-S7-PDF-build-20261003.tar.gz | All3 P7 builds0undefined; actualsourcehashesmatch; source/PDF assetgatePASS and publicPDFhashesPASS |
| T83 | Supplementary bundle (local) | done | 4 | notes/T83-v0.2.1-corrected-review-package-20261003.json | v0.2.1 exactP6/S6/R131 publicrebuildPASS;18ZIP members/17checksums; version-preservation regressionPASS; published6517aa94 |
| T84 | Review handover | owner | 1 | docs/paper-lean-audit/review-status.json | Review package ready; Johanna marked proposals and Max all57 full correspondence checks remain pending |
| T90 | Release drafts | done | 3 | docs/releases/v1.3.1.md; supplementarydocs/release-v0.2.1.md | Both actualDOIs and verification scopes inpublishednotes; oldernotes preserved |
| T91 | Signed tag, release, Zenodo | done | 4 | notes/T92-formal-v1.3.1-Zenodo-bytecheck-20261003.json | Signedformalv1.3.1 and supplementaryv0.2.1 tags/releases published; immutable |
| T92 | Verify Zenodo archive | done | 4 | notes/T92-supplementary-v0.2.1-Zenodo-bytecheck-20261003.json | All1172formal and29supplementary tagged files byte-identical toZenodo; zero missing/extras/mismatches |
| T93 | Citation drafts | done | 4 | paperP7=760c68d2d79a8fd2c4b58f35f32dd90969591300 | ActualverifiedDOIs23127367/23127468 cited; GitHub+Overleaf pushes0 |
| T94 | Final review emails | done | 1 | notes/T94-final-review-email-receipt-20261003.json | Both authorized short English emails sent; work mail service sent=true; Chris&AI signatures; Johanna/Max human reviews remain pending |
| T97 | Palomar v3 citation and registration records | done | 1 | notes/T97-Palomar-v3-registration-and-citation-20261004.json | Exact registered source and immutable citation recorded; paper compiled and pushed to GitHub and Overleaf; frozen companion unchanged |

## Earlier execution history (resumed 2026-10-03 by owner)

- Linux controller resume: MAIN `3214f5c8f336`, WT restored at `c3dccd4b3f93` on `campaign/paper-route-20261003`; unrelated untracked `cluster-guard.py` preserved. Authoritative documentation remains in MAIN.
- All 578 candidate Lean/configuration source hashes matched the saved Mac WT before the first check. Manifest SHA-256 `181dc71c535a28f43a1bb7db37de14b6781cc7a1de2512cb76595d05b3285342`; this identifies candidates, not accepted proof evidence.
- Mac guarded T31 check reproduced the saved failure in 22 seconds, peak 2163 MiB, two threads, 8 GiB cap. The first invocation failed before Lean because SSH lacked Lake in PATH; the corrected invocation supplied the installed rc3 bin path.
- Local canonical cache is still 4.33 and must not be reused. A fresh Linux rc3 cache and local Linux resource guard are accepted under the archived mailuefterl execution contract; final frozen replay remains a separate gate.
- Local Linux guard accepted after Sol repaired foreign-process refusal, signal cleanup and descendant lock retention; synthetic behavioral suite passed without Lean. Fresh guarded dependency setup exited0 at peak2435MiB, followed by an explicit cache run exit0 at peak916MiB. Manifest bytes remained unchanged (SHA-256 `29658324d2c247fb161a35c9869ac7e3c43491614304343a81337c65fae5dcbc`) and all ten package HEADs matched their pinned revisions. Linux prerequisite modules and all three T22/T30/T31 trust0 consumers passed, with only the three permitted axioms and zero swap growth (notes/linux-baseline-20261003.md); this setup is not the final frozen replay.
- Luna workers assessed disjoint T31–T44 and release inputs. T31 escalated to `gpt-6.1-sol` after its recorded failed task; downstream acceptance waits for checked prerequisites. No release or final email has been sent.
- The active user instruction resumes the full campaign, authorizes regular commits/pushes and both releases, and requests the final review email after completion.
- Workers use `gpt-6-luna`; failed bounded tasks escalate to Sol. No Qwen/Pi campaign driver is used in this resumed run.
- The owner's follow-up explicitly replaces serial task selection with heavy parallelism. Independent workers/subagents prepare disjoint candidates concurrently; actual dependencies govern acceptance. The controller schedules bounded Lean checks across approved hosts.
- The controller owns authoritative state, integration, commits, pushes and promotion. Workers return evidence without committing or changing the ledger.
- The owner's further instruction authorizes local guarded Lean and concurrent acluster/scluster allocations. Small jobs use 8 GiB RAM and two actual CPUs. The latest owner steering restricts active execution to Linux here and acluster/scluster; cluster CPU reservations must cover RAM when enforcement cannot be verified. Pins, archived receipts, mathematical statements and protected-host restrictions remain in force.
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

- Revised resource guard: 12 GiB start, 4 GiB free floor, 8 GiB aggregate RSS, two Lean/native threads; behavior checks passed including surviving-child lock, aggregate RSS, timeout and signal cleanup (notes/resource-guard-behavior.md). Mac CPU-average watchdog is separate from kernel CPU quotas.
- Cluster resource preflights: acluster/scluster each permit an initial two-CPU, 8 GiB job; RAM cgroup enforcement unverified, so CPU reservation covers RAM using 10% headroom. Scluster job3090343 refused before installation/Lean because the step affinity had only one CPU; explicit srun -c2 repairs the step request. The owner subsequently required node RAM/pressure safeguards and live monitoring; enhanced guard preparation and independent review are active, acluster submission is held for that concrete safeguard.
- The WT guard copy was stale despite MAIN being authoritative. Controller copied the validated guard to WT and pushed5228a6d; future check grants require the absolute MAIN guard path and expected8GiB/2CPU summary. Old T31 runs remain diagnostic evidence.

## Frozen commit

(controller/owner only)

## Archived controller hints (historical)

(These describe the former campaign. Use current task receipts and Linux guards.)

- T02 is complete. The Mac cache/runner directions below are historical.
  Any specifically authorized Linux recheck uses the current `GUARD` route
  in the work order and does not reuse the old MAIN 4.33 cache.

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

- T43: all 18 dependency-guard integration payloads are already tracked at WT
  `0340cf2` and match the archived new-file bytes. Reuse them; apply only the
  verifier wiring after its successful `--check`. Fixture behavior and strict
  production checks are still required; source identity is not a behavior test.

## Blocked

(Pi: one line per blocked task with the path of its `notes/<id>-blocked.md`)

## Reviewed cluster replay driver (3 October 2026)

The cluster-specific final immutable-source driver and contract are accepted
as reviewed preparation. Independent review first found mode and run-root
containment gaps; Sol repaired both and Luna independently confirmed the
behavioral negative/positive oracles. Actual filesystem modes are compared
with Git modes even when Git ignores chmod; canonical existing-directory
containment rejects traversal and symlink escapes before writes.

Driver SHA256 43666f950d7de083a32ff2207c21b730179accf3bf1eaebc5c180e4dfe42db53.
The exact heavy CommonOpenEtale module prebuild runs after cache loading, before
the authoritative verifier, to avoid overlapping its observed7406MiB peak with
a wide build. Independent gate-order/failure review passed; caps are unchanged.
Its four comparator gates remain ordered and all ten resolved package HEADs
must match immutable rev pins. The archived mailuefterl driver/contract remain
byte-identical. No final replay was launched; T70 immutable public source,
T71 preflight, actual T72 run and T73 collection remain required.

## Package cleanup checkpoint (3 October 2026)

The controller removed the four obsolete Mac/Pi serial runner, guard and
prompt files and their unused runs ignore file after the reference audit.
Git preserves their bytes. Historical proof/resource receipts remain intact;
active Linux guards, all mathematical modules, unchanged challenges and both
solution routes are retained. This completes the obsolete-runner cleanup
component; final README/status and Palomar package checks await proof acceptance.

- T41 accepted after3127001 drained: actual module and unchanged literal trust-zero consumer passed. Shared assembly failed its first actual adapter elaboration atExclusion44:19; Sol repairs that explicit field inference and rechecks only assembly. No completed wrapper/consumer rerun or duplicate cluster job. See notes/T41-original-prime-linux-accepted-checks-20261003.md.

- All four main/alternative solution assemblies passed3127814 with the unchangedguard and no survivors. Controller integrated55 explicit proof/tooling paths, sameunchangedchallenges, registry owners and current release metadata. The one final public-source verifier and four actual comparators remain next; no duplicate whole-library check.

- Final driver launched as scluster3128039 against immutable public45037fbc16329df7a208eb3de91aca31d720f03c. Staged driver SHAe9f19350e4f3dd6558abcbcbfb9ce2b93fae8cfc5cf0b78911c61c943942f4ac; Slurmguardca59b4b7c067851dca28aaff59b3919ec9224bda16a324fa2233d29d1c898506; Linuxguardcd072bba9e2dead893791503bb6115299ba0a65eb106b126a376a1ab948b7b87. Fresh sourcecheckout/Lean gates passed; accepted build-cache copy is active. The single full verifier and all four actual comparators still require completion.

- Final3128039 stopped at tooling only: required bubblewrap0.12.0, found0.8.0. Fresh public source, Lean pin, complete cache copy and source policy passed; no full verifier/comparator ran. Failure/drain archive retained. Luna repairs official bwrap inside isolated bootstrap; bounded resume of the same unchanged clean public clone skips only repeated fetch/copy, retains every proof/pin/comparator gate and separate receipts.

- Official isolated bwrap repair3128465 passed exact version/sandbox probes and drained. Independently reviewed bounded resume3128526 kept original source45037fb byte/mode-identical; tooling,10pins,cache andEtaleprebuild passed. The first full verifier started14:57:12UTC. Prior tooling failure archived; no repeated full verifier or cluster work.

- Finalpinnedmap519locators/108SameWitnessrows has zero unresolved sources; publicgenerator40967 check andactual57-cardChromium walk passed. Current111 manuscript-linked declarations match its manifest. Exact6sourceinputs and2PDFs passpublicationassetgate; deployable sitebuildpassed. Four399-name compiler groups remain afterfinalverifier; archive/citations/humanreviews are separate.

- Final verifier3128526 failed strictdependencyinspection after4475-job fullbuildPASS; all earlier source/pin/tool/cache stages passed. Guarddrained normally withno survivors. Sol traced unavailableprivateMathlib helpers to inspecting env.isExporting publicview; smallestrepair selectsprivateenvironmentview, retainingallbody/owner/axiom/forbiddenroutechecks. Markerregexnewlinebug also corrected. Boundedactualguardgate required before nextpublicsource verifier; fouractualcomparators unexecuted.

- Strict guard repair3129931 passed actualproduction (all4roots, zero forbidden/unavailable) and independent behavioral fixtures. Frozenpatch899582 and scoped receipt archived; no mathematical source or pin changed. Main/alternative route stages continue in the same sole slot. Fresh public-source verifier and four comparators remain required.

- Public repair source C2 is12ae3cc49152672a48a96f13994314b65ae38197. PaperP3a5a703f588ef3a2c43e8fc21f89db8bf494af5db is pushed to GitHub/Overleaf; public snapshotS3 is22b44d56af302bbf8dd3542316d8b15a2b0c5315. All three PDFs compiled0undefined; matching map/PDF asset gate passed. Main required/excluded routes passed in3129931; alternative stages and final public verifier/comparators remain required.

- S3129931 completed all strict production/fixture/main/alternative route stages PASS and drained guard0/nochildren. Exact publicC2 final replay3131361 launched after fresh preflight; this is the only active cluster run. All four actual Palomar comparisons remain its required stages.

- FinalC2 attempt3131361 failed before any verifier/comparator: generated `.lake` symlink was not covered by directory-only Git ignore. Public source identity, tooling, cache reuse, dependency materialization and10pins passed; guarddrained normally/nochildren. Exact failed receipt archived. Sol repairs only generated-cache Git metadata handling for a bounded same-source resume; no proof or manuscript pin changes.

- SameC2 boundedresume3131801 launched after3131361normaldrain, emptyqueue/node20idle and exactdriverhash5720dad. Independentreview/Git behavior oracle PASS; narrowgeneratedcachemetadataignore retains alltrackedbyte/mode/source/pin/fullverifier/comparator gates. No proof/paper pin changed. Newreceiptroot final-receipts-guard-repaired-resume1; originalfailure preserved.

- Fresh C2 verifier progress3131801: independent dependency fixtures PASS16:41:02Z; actual4475job buildPASS16:41:29Z; strict4terminalroots PASS16:53:45Z withzero forbidden/unavailable. Logs are newer than the16:32:53Z verifier start. Main/alternative routes, consumers, remaining verifier checks and four actual comparisons are still required. Old donor build logs are not new C2 evidence.

## Fresh final public-source main route result

The sole same-source resume scluster3131801 passed both main required/excluded
route checks at17:03:45Z after the fresh4475-job build and strict terminal
inspection. Both main roots reach the same-witness endpoint and exclude the
generic/Laurent solution variant; forbidden0/unavailable0. Both alternative route
checks also passed: their roots reach the generic/Laurent endpoint and exclude
the same-witness endpoint, forbidden0/unavailable0. The complete verifier, retained proof-library build and
four actual Palomar comparisons remain pending; this milestone does not
qualify the release. No duplicate final check is scheduled.

## Fresh complete literal-consumer audit

The same exactC2 run scluster3131801 completed all116 literal consumer files
and reported `Literal consumers and import/axiom audits: 317 reports passed`.
The fresh completed consumer log SHA-256 is
`96686584ecf6205a78f045cd1c7e7d61821201da304ff16ce321a52fc93f5993`.
Its331 distinct printed reports include the317 required audited reports; the
controller separately parsed all5 new closure/original-prime full names, each
with exactly propext, Classical.choice and Quot.sound. This completes T44.
The paper-name/endpoint audits, complete verifier exit, retained proof-library
build, four comparisons and final guard/source-identity receipt remain required.

## Complete verifier pass and retained-target runner repair

Exact publicC2 `12ae3cc49152672a48a96f13994314b65ae38197` passed the
complete repository verifier in3131801 at18:28:39Z. The log SHA-256 is
`acfe9dcd8e48105289ebd6555fe90a6c85043ad963409cab66bbe082d13fcea6`.
Counts:4475 build jobs,116 consumer files/317 required reports,111 paper-linked
names,37 endpoint reports, all3 permitted axioms only; strict terminal and both
route-direction inspections passed forbidden0/unavailable0.

The later `lake build proofs` runner step requested absent `proofs.lean`,
then reported a trailing timeout Remote I/O write error and exited125.
The3 existing retained modules already occur in ordinary project imports;
the repair names them explicitly and changes no tracked proof/configuration.
Comparators and source-after integrity were not executed. Guard finished125,
stop[]/children[]/zero swap growth, peak4336214016 bytes, within original caps.
The88-file exact evidence packet is archived at
`notes/T73-full-verifier-pass-retained-target-failure-3131801-20261003.tar.gz`,
SHA-256 `8e5970c2e66db658e1f985d394185fdb11b22b028abc063aa672394b3ff38a01`.

Reviewed remaining-stage driver:
`notes/cluster-final-retained-library-resume2-20261003.sh`, SHA-256
`e462d482bacf03dd908435e804e72c3e48e81ec02d02e7555b35159d3ba9b8b4`.
It binds the actual failure, successful verifier log, drained guard and exact
C2/cache/raw-byte/mode/pin evidence, uses fresh receipt paths, probes actual
receipt write/flush/fsync/read and bounded ordinary stdout/stderr capture,
builds the3 explicit retained modules, then runs all4 actual comparators and
final source/pin gates. No whole-verifier repeat or cap/source change.
Independent review2 PASS and preserved review1/scope clarification are in
`notes/T73-retained-target-resume-review-20261003.tar.gz`, SHA-256
`b8b22d458f0ba20800fdf1940a536940dc4580d5111f97b0c095f00fd2339864`.
Read-only home filesystem check reported39% used; quota unavailable. Actual
allocation I/O probe acceptance remains required. Resume is prepared, not yet
submitted. No release, new DOI or final review email has been sent.

## Remaining-stage resume submitted

Controller submitted sole scluster3136492 at18:43:19.466507Z using the reviewed
resume2 driver after commit/push1b8a1af. Staged driver e462d482, submit script
484bbfdc and accepted guard ca59b4b7 full hashes matched; user queue was empty,
node20 idle, receipt/guard/slurm paths absent. Exact publicC2 remains unchanged.
Receipt root is `final-receipts-guard-repaired-resume2`; guard prefix is
`final-C2-resume2-outer-guard`. The successful verifier in3131801 is inherited;
only actual I/O probes,3 retained module targets,4 comparators and final
source/pin identity remain. Original21600/19800-second and2CPU/8GiB caps remain.
No other proof job or unchanged verifier rerun is scheduled.

## Retained module pass and sandbox cache-layout failure

Remaining-stage3136492 passed the actual receipt filesystem and bounded ordinary
stdout/stderr probes at18:43:28Z, then all3 explicit retained modules at18:43:42Z.
The retained module log SHA-256 is
`ae4cb0eefad61910d6734ba0df4620d6059d6d1dd791439f818a89b13278dd59`.
Raw source-before manifest remained2c697217/1095 tracked files; all10 pins matched.

The first comparator stopped before proof checking at18:45:55Z because pinned
bubblewrap0.12.0 cannot mount onto `final-source-guard-repaired/.lake`, which is a
generated cache symlink. Pinned rc3 Lake/CLI/Check.lean binds the project's
`.lake` at that same project path during resolution/build/export. No theorem,
configuration, proof mechanism or policy exception was implicated. The other3
comparators and final source-after check were not executed. Guard finished1,
stop[]/children[]/zero swap, peak3833794560 bytes. The80-file exact packet is
`notes/T73-retained-build-pass-cache-mount-failure-3136492-20261003.tar.gz`,
SHA-256 `e1778d9af7eb48b8dae02944a863134183c7197d9c316d9abafedd204d1cbf0e`.

The bounded next repair relocates only the existing actual cache directory into
C2's `.lake` path, preserving inode/content and old donor access, without copying,
source/tool/package changes or sandbox flag changes. Remaining scope is only4
actual comparisons and final source/pin integrity under the same accepted caps.
The successful whole verifier and retained module build will not be repeated.
Resume3 is in preparation; no slot is running or duplicated.

## Cache-layout-only comparator resume reviewed

Remaining-stage driver `notes/cluster-final-cache-layout-resume3-20261003.sh`
is frozen at SHA-256
`6fa1ae519128afcbae5253ae3666ae498876ec3f406cb82751b68c383644b85d`.
It binds exact3136492failure1/drained/retainedmodule0 and inherited3131801
verifier0, plus all source/cache/pin evidence. It journals the exact existing
donor dev46/inode10611031912501232925, removes only the validated C2 `.lake`
symlink, atomically renames the existing real cache into that destination and
preserves donor access through a backlink. No copying or tracked source,
configuration, package, tool or policy flag changes. Inode/containment/pins
and tracked raw-byte/mode manifest are checked after relocation and at end.
Only4 comparisons remain; no successful verifier/module/probe repeats.
Independent review PASS SHA-256
`79e7168ebd30490c8e9c839c604d4b11ece43442ea3f5d59c6abd5c8ccfe5350`;
real-filesystem oracle preserved inode/content/donor access and rejected a wrong
donor before mutation. Evidence is
`notes/T73-cache-layout-resume-review-20261003.tar.gz`, SHA-256
`d3f2b2831e4ebd486d333f61b9c7009a6c5606b6adc5761eacdeaedbaf047a9e`.
Original caps remain; prepared for controller submission after fresh preflight.

## Cache-layout comparator resume submitted

Controller submitted sole scluster3136992 at18:58:07.033096Z after review and
commit/push39f2106. Driver6fa1ae51, submit ee35a9c1 and accepted guard ca59b4b7
full hashes matched remotely. User queue empty, node20 idle, fresh receipt/guard/
slurm paths absent and exact original donor dev/inode verified before launch.
Receipt root is `final-receipts-guard-repaired-resume3`; guard prefix is
`final-C2-resume3-outer-guard`. Source remains publicC2. Completed verifier3131801
and retained module/probe3136492 receipts are inherited; no repeat or duplicate
proof slot. Remaining4 comparator results, final identity/pins and guarddrain
are pending. T80 will run once on the same accepted cache after these complete.

## Allocation-local device check repair

3136992 stopped before receipt creation, cache relocation or comparison because
login host reports st_dev46 and node20 reports st_dev45 for the SAME frozen
cache inode10611031912501232925. Guard finished1 with stop[]/children[]/zero
swap; cache/source untouched. Exact failure is archived at
`notes/T73-cross-host-device-setup-failure-3136992-20261003.tar.gz`, SHA-256
`794aea9bd1070bbee007d8b82b3f6757af6250a5278443334a5124bc4b6d941c`.

The corrected driver `notes/cluster-final-cache-layout-resume4-20261003.sh`,
SHA-256 `f88e8e0daf0996638d3fdc687c44b36a2680750c866b1f2b114e49f8a50e6e95`,
changes only the2 host-local-device assertions to the frozen inode, retains
allocation-local same-device and full runtime identity after rename, and adds
exact3136992failure/drain/log plus absent-receipt gates with fresh resume4 paths.
All source/cache/pin, inherited verifier/module,4 comparator and final integrity
checks/caps remain. Independent targeted review PASS SHA-256
`86d4e65c22a52f50af4e440158bbb4e7a4b3d46303bd72b38024877ee540a4ea`.
Review/driver/submission packet:
`notes/T73-runtime-device-resume-review-20261003.tar.gz`, SHA-256
`3dfa80a790ed03cc6953d0725cd9296e46a51c47478f2ea2784e4d1ebc748e91`.
Prepared for controller submission; no full verifier/library repeat.

## Allocation-local cache relocation passed

Controller submitted sole3137241 at19:05:23.499140Z after reviewed R4 driver
commit/push1c3cba2 and exact staged hashes, empty queue/idle node20/fresh paths.
Actual relocation preserved dev45/inode10611031912501232925, made C2 `.lake`
a real directory and retained old donor access by backlink. Before and after
relocation source manifests are2c697217/1095 tracked files; all10 package HEADs
matched both before and after. Comparator-main began19:05:37Z. Four actual
comparison results, final identity/pins and guard0/drain remain pending.
No source/config/tool/policy changes or completed verifier/library repeats.
Receipt root: `final-receipts-guard-repaired-resume4`; guard prefix:
`final-C2-resume4-outer-guard`. Single proof slot remains assigned to this job.

- R4 actual comparison checkpoint: main `comparator.json` exited0 at 2026-10-03 19:22:38Z, with fresh con-ron (53,716 declarations, `--verified`), nanoda, Lean default kernel and statement-comparison acceptance. Fixed-source began at that timestamp. The other three comparisons and final integrity/drain are still required; the complete verifier and retained modules are not repeated.

- R4 fixed-source comparison exited0 at 2026-10-03 19:39:44Z with all three kernels and statement comparison accepted. Both main-route configurations are complete. The generic/Laurent alternative started then; both alternatives and final integrity/drain remain required.

- R4 generic/Laurent alternative comparison exited0 at 2026-10-03 19:47:11Z with con-ron (46,598 declarations, `--verified`), nanoda, Lean default kernel and statement-comparison acceptance. The alternative fixed-source comparison started then and is the last comparison. Final source integrity and guard drain remain pending.

- Final C2 formal acceptance: all four Palomar comparisons and final integrity passed in3137241; guard0 at19:54:40Z, peak RSS6,468,694,016bytes, zero swap growth/stops/children. Root validated all60 collected inventory rows and32 compressed evidence artifacts. Primary receipt SHA256 `1ccb4a3b422041b3f894ea8709d60dcce782b13e1b33e01c7a396e3951a71ca5`; complete R4 archive SHA256 `d728e399984d5cd6d7697a15c30b9d10435e24856cf34e8691759603550fd868`. Historical f691 receipt remains preserved.
- Bounded T80 job3138990 failed before checking declarations on an unavailable `tests` import; other groups did not run and guard drained1 cleanly. Sol repairs only the name-check arrangement. No full-verifier, retained-module or comparator repeat is authorized or needed.
- Controller reviewed and launched sole bounded name-check resume3139266 after exact hashes, prior clean drain and empty-queue/idle-node preflight. Common393 checks are391 imported names plus2 exact C2 standalone consumer sources with qualified queries; remaining3 isolated groups have2 checks each. No formal source or declaration changed.
- Final compiler-name acceptance3139266 passed399 checks in4 isolated groups, guard0/no stops/children/swap. Results SHA256 `c735cdd29b3f463c505761ef5c2011dbd1b0bb5a168b23bae663f68258a8250d`; guard SHA256 `df241036fec3bf3d3ef5bd21bf169222d3be2d4920f9c3142b08b350ac092cd6`; root checked every completed count and part exit. Formal release qualification complete.
- Formal release v1.3.0 published20:12:31Z at54c4f0c902bcd840e44eeba80686ef3fa0e7dc2b; signed tag595eef30a0285f892a0ef4189d79de7302101137 verified. Zenodo23126868/DOI10.5281/zenodo.23126868 downloaded16,282,434bytes, SHA256 `b6ec84e622ee2905e00148ad43401e7ca72b4fb236b3a2607ebcf9839d1247b3`; all1,163 taggedfiles byte-identical, no missing/extras/mismatches.
- P4 paper4d19a183846beb50f37ad2b4e51e836a76ed8bac cites the actual verified formal DOI and links formalreleaseR; author proof body preserved. GitHub+Overleaf pushes succeeded. Three matching PDFs are rebuilding; companion freeze will use P4 and its public snapshot.

- P4/S4/R matching PDFs and source hashes were accepted; source/PDF asset gate passed. The public-only companion rebuild fetched exact public revisions and rendered all57 cards successfully. Its existing filename handoff was fixed to copy the configured output stem to index.html; generator runtime and proof sources are unchanged. Current16-member package awaits final source/hash metadata and signed supplementary publication.

## T95 Verification provenance correction

The owner supplied the Palomar review finding. The descriptor now links its historical cbb2396 commit/report hash to the exact historical report, with both completed later replay scopes recorded separately. Formalv1.3.1 is published and all1,172 archive files match. See `notes/T95-v1.3.1-verification-provenance-fix-20261003.json` and the v1.3.1 archive/congruence receipts. No mathematical source or proof-verifier program changed.

## Campaign completed

Formalv1.3.1 and supplementaryv0.2.1 are signed, published and byte-verified. Final P7/S7 citations, PDFs and live guided review are accepted; both authorized review emails were sent. Johanna/Max reviews remain explicit human follow-ups. Palomar v3 registration completed on 4 October 2026 at source 0bb3aa929b931bf5d82d90f62d7508d3ae1dccc1, whose Lean/configuration files match R131. No new mathematical replay is claimed by the provenance patch or final handover records.


## T96 Supplementary reader refresh

In progress: simplify the reader and package without changing formal v1.3.1.
All 423 mapped references resolve at their exact pins; 261 theorem/lemma
excerpts contain full proof bodies. User-facing process prose is removed.
Publication and browser checks remain pending. No cluster or Lean work starts.


T96 complete: supplementary v0.2.2 published at `a114b06749fb01cf352f8b13ad3fda8267293ac6`,
DOI10.5281/zenodo.23132562, all 16 archive members byte-verified. The public
reader and five online/download assets match the checked local files. All 57
passages remain accessible; 504 displayed Lean source excerpts are exact.
Generator tests: 71 passed, one historical fixture skipped. Current review
ledgers point to the new reader; Johanna and Max remain pending. No mathematical
source, formal release, cluster job or email changed during this UI refresh.

## T97 Palomar v3 registration and citation

Complete: [immutable v3](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=3) registered at
`0bb3aa929b931bf5d82d90f62d7508d3ae1dccc1` on 4 October 2026. The mechanical
report and preserved comparator hashes match; Lean, nanoda and con-ron accepted
the solution. Automated review identified no problems. All 587 Lean/configuration
files match R131. This receipt covers the named headline theorem and exact
source; human manuscript and full correspondence reviews remain pending.

Paper commit `44e7189725ec52c20256babda76f24a669184b5b` updates the existing
citation key to v3, is pushed to GitHub and Overleaf and compiles without
unresolved references or citations. Current ledgers record registration complete.
Supplementary v0.2.2 retains its frozen P7/S7/R131 inputs and PDFs. Receipt:
`notes/T97-Palomar-v3-registration-and-citation-20261004.json`.
