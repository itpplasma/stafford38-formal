# T46 final package cleanup proposal

Status: proposal only. No files were deleted, no authoritative status or
source was edited, and no Lean, verifier, SSH, or release command was run.

## Review scope and finding

- MAIN reviewed at `12d7598fc5efd56317e01e4f3dd2d2b85843faf1`; WT reviewed at
  `4c1678e563b8b7e4f32b9c951b823ef9f5f44e53`. WT is intentionally dirty
  with T34–T45 candidate sources. This report does not freeze or change that
  source.
- Read the provenance contract, main and campaign plans, campaign ledger,
  project/verifier entrypoints, WT README/PLAN/alignment map, and candidate
  Palomar configurations. Searched tracked-text references to every legacy
  wrapper and checked the Linux verifier paths.
- The earlier Lean reachability review found no safe mathematical deletion.
  This proposal deletes no Lean modules, alternative-route code, challenge
  roots, pins, verification receipts, paper assets, or proof-review evidence.

The complete active execution route is Linux-only: local checks use
`docs/qwen-campaign/linux-guard.py`; approved cluster jobs use the separately
reviewed Slurm guard and frozen job-specific driver. The tracked macOS/Pi
serial wrappers are no longer used. The current Linux verifier, policy checker,
and comparator configs have no runtime import or invocation of those wrappers.

## Smallest deletion set

Subject to controller approval and one final reference check, delete exactly:

| Path | Why it is obsolete | Tracked textual references before cleanup |
| --- | --- | --- |
| `docs/qwen-campaign/drive.sh` | Hard-coded Mac paths; serial Pi scheduler automatically commits/pushes MAIN and WT. No current driver calls it. | 2 occurrences: its own usage comment and the historical STATE invocation. |
| `docs/qwen-campaign/run-pi.sh` | Hard-coded Mac Pi runner and log path; caller is only the retired serial driver. | 5 occurrences: self, driver, two historical STATE mentions, and T00 receipt. |
| `docs/qwen-campaign/prompt.md` | Old worker prompt requires Mac worktree, Pi task order, and the removed guard. | 2 occurrences: the retired runner and historical STATE pointer. |
| `docs/qwen-campaign/guard.sh` | macOS-only guard for the retired runner; active Linux guard is a different implementation. | 19 occurrences: this script's examples, stale campaign instructions, and historical check notes listed in the JSON manifest. |

Also remove the now-unused `runs/` ignore entry from
`docs/qwen-campaign/.gitignore`: the directory is absent and its only
producers are the retired scripts. Leave historical notes and logs untouched;
their literal commands describe past runs and are not current run instructions.
The T00 historical statement that the old run directory was untracked remains
accurate and may remain as chronology.

No files under `docs/audits/`, `docs/verification/`, or
`docs/qwen-campaign/notes/` meet the deletion test. Retain
`linux-guard.py`, `linux-slurm-guard.py`, all cluster replay receipts and
drivers, and the four unchanged-challenge comparator configurations. The
untracked `docs/qwen-campaign/cluster-guard.py` is unrelated and explicitly
out of scope; do not touch or stage it.

## Proposed front-door status

The exact MAIN-document hunks are in `T46-final-cleanup-proposal.patch`; they
are not applied. They remove stale serial-runner instructions, identify Linux
guards as the only active execution route, and refresh the root campaign
checkpoint from “T35 Sol repair active” to “T35 checked, final assembly/replay
and correspondence open.”

For the formal-package `README.md`, add only a short route/delivery paragraph,
and only when T45 source integration is accepted: the two Challenge statements
stay shared and unchanged; the paper-conforming solution is primary; the old
generic/Laurent proof is a separately named alternative; correspondence and
new-release qualification remain pending; online Palomar submission belongs
to the owner. Keep existing theorem-receipt scope and author proof unchanged.
This candidate sentence is recorded as text in the JSON rather than injected
into the source before the final proof passes.

The WT `PLAN.md` says work is “paused at owner's request,” while the active
controller ledger now tracks Linux completion tasks. After final source
freeze, replace only its `active_work` value with a dated, conservative
checkpoint: Linux completion work is managed by the controller; same-witness
closure, final replay, and full paper correspondence remain open; no new
handover/release is recorded. Keep the rest of its scope and proof statements
unchanged. `docs/paper-route-alignment.json` already accurately says full
correspondence remains open and its same-witness endpoint is incomplete; do not
change that record in this cleanup.

## WT and Palomar-route audit

WT's `README.md` has no links to the retired wrappers. It accurately says
same-witness closure and new-release comparison remain pending. The candidate
`PLAN.md` currently freezes an older paused checkpoint; refresh only its
status line after T70 source freeze, not its mathematical scope.

MAIN currently includes `comparator.json` and
`comparator-fixed-source.json`; its tracked runner and policy checker cover
those two variants. WT's candidate adds
`comparator-alternative.json` and
`comparator-alternative-fixed-source.json`, and its candidate runner,
policy checker and verifier explicitly include all four. Keep them together:
the challenge and fixed-source challenge modules remain shared, while solution
routes differ. Do not remove an alternative front door or claim it has passed
until the final verifier and all four comparisons pass. Palomar online
registration remains an owner action after delivery.

## Preservation and acceptance boundary

The old wrapper bytes remain recoverable from Git history. Retained historical
receipts remain unchanged, as do the pinned dependencies, selected paper,
definition-owner registry, alignment map, and all mathematical route modules.
The cleanup is only a proposed package tidy; the controller integrates,
rechecks references, updates status, and accepts the final source after its
proof and replay gates.
