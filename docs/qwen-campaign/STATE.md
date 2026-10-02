# Qwen campaign state

Plan: `PLAN.md` in this folder. Pi updates task rows, measurements and
notes. Only the controller or owner edits "Controller hints", "Frozen
commit" and owner-gate rows.

## Tasks

| Id | Title | Status | Attempts | Last log | Note |
| --- | --- | --- | --- | --- | --- |
| T00 | Resource and state check | done | 1 | docs/qwen-campaign/notes/T00-check.log | GUARD OK; 116 GiB free RAM, 553 GiB free disk, no foreign lake/lean; MAIN clean outside docs/qwen-campaign |
| T01 | Create campaign worktree | done | 1 | docs/qwen-campaign/notes/T01-worktree.log | WT at /Users/ert/proj/stafford38-qwen on qwen/paper-route @2a9c264; .lake APFS clone (cp -cR, 22 s, df delta 0 GiB); manifest identical, toolchain leanprover/lean4:v4.35.0-rc3 |
| T02 | Baseline build of prerequisites | doing | 1 | docs/qwen-campaign/notes/T02-check.log | running guarded baseline build of 11 prerequisite modules |
| T10 | Extract archived candidates | todo | 0 | | |
| T11 | Port AwayFactorToAtPrime | todo | 0 | | |
| T12 | Port axis lift from ground point | todo | 0 | | |
| T13 | Port chart ground-map lemma | todo | 0 | | |
| T20 | Instance inventory | todo | 0 | | |
| T21 | Minimal tower reproducer | todo | 0 | | |
| T22 | Ring-hom form of the endpoint | todo | 0 | | |
| T30 | Chart and away data | todo | 0 | | |
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

## Measurements

- Free memory / disk at T00: 116 GiB truly free (guard), swap used 0 GiB, pressure normal; disk 553 GiB free of 1.8 Ti on /System/Volumes/Data
- MAIN commit at T00: 2a9c264c5ad881fec8f70b9ad0d53861b72279b0 (branch main; untracked only docs/qwen-campaign/run-pi.sh, docs/qwen-campaign/runs/, docs/qwen-campaign/notes/)
- T02 prerequisite build (wall time, peak RSS, jobs):
- Single-file check turnaround:
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

## Blocked

(Pi: one line per blocked task with the path of its `notes/<id>-blocked.md`)
