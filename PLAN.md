# Stafford 3.8 formalization status

```yaml
terminal_claim: Stafford Conjecture 3.8 and fixed-source strengthening
terminal_proof: verified at named historical checkpoints; candidate source requires final replay
paper_correspondence: selected same-witness route assembled in candidate; full correspondence and human review pending
current_alignment_checkpoint: docs/audits/paper-route-checkpoints/actual-orders-chart-source-checkpoint.json
historical_release: v1.2.3 remains attached to its recorded source
candidate_releases: formal v1.3.0; supplementary v0.2.0; no new release published
active_work: T34/T35/T36/T41 modules and literal consumers accepted; four shared solution assemblies passed on Linux; final verifier and four Palomar comparisons pending
handover: pending final checks and human reviews
```

A proved terminal theorem does not establish correspondence of every intermediate manuscript argument. The preserved author proof remains visible; local mathematical proposals remain marked for review. New formal bridges must derive their geometric inputs from the retained witness rather than assume them in a terminal wrapper.

The README and `docs/paper-route-alignment.json` summarize the proof route and the current scoped evidence. Historical release and audit receipts remain tied to their named sources and configurations.

The [2 October checkpoint archive](docs/audits/paused-2026-10-02/README.md) preserves earlier baseline receipts, migration patches, review-tool preparation, and failed closure repairs. The current candidate has accepted T34/T35/T36/T41 modules and literal consumers with only the three permitted axioms. The four shared solution assemblies passed on Linux; the final repository verifier and four Palomar comparisons remain pending.

## Remaining completion gates

1. Completed: all four shared main and alternative solution assemblies passed on Linux, as did the T34/T35/T36/T41 modules and literal consumers, with only the three permitted axioms.
2. Run the final repository verifier on the frozen candidate with Lean 4.35.0-rc3 and the pinned Mathlib and AlgebraicAnalysis revisions.
3. Run all four Palomar comparisons on that frozen source: `comparator.json`, `comparator-fixed-source.json`, `comparator-alternative.json`, and `comparator-alternative-fixed-source.json`. Keep both challenges unchanged and preserve the generic/Laurent route as an alternative. Deliver the Palomar-ready package; the owner submits online.
4. Freeze exact paper, formal, library and generator inputs. Re-anchor every review card; rebuild matching manuscript PDFs and the complete Max correspondence package. Preserve Johanna's visible proof and local annotated proposals.
5. Remove obsolete unused review front doors and scaffolding after reference checks. Synchronize the final manuscript to Overleaf and its GitHub mirror; publish matching signed formal and supplementary releases, verify both Zenodo archives and cite the verified records from the paper. Record the main and alternative routes in release notes; send the requested review email after delivery.

The controller owns integration and promotion. Isolated worker candidates and fixture passes do not certify the final package. Human review and Palomar registration remain separate from local verification and release.

## Branches for resuming saved work

Updated 3 October 2026. The campaign ledger is [docs/qwen-campaign/STATE.md](docs/qwen-campaign/STATE.md); its `doing` rows record unfinished preparation. The synchronization audit observed Codex application daemons on faepmac1 but no local Stafford Lean, Lake, Python or Git execution worker at 05:40 UTC. No proof campaign was resumed by synchronization.

All branches below belong to `itpplasma/stafford38-formal` and are pushed to `origin`. Their full names start with `wip/sync-20261003/faepmac1/`. Original Mac worktrees remain under `/Users/ert/proj/<suffix>` with their existing working files and staging preserved.

| Branch suffix | Commit | Contents and remaining work |
| --- | --- | --- |
| `stafford38-formal` | `4fed8b73c008` | Exact incoming campaign PLAN/STATE, T22/T30 accepted-check packets, later task notes, definition/map patches and draft cluster guard; proof integration remains pending. |
| `stafford38-qwen` | `c3dccd4b3f93` | Current same-witness modules, literal consumers and verifier wiring after `qwen/paper-route` at `5228a6d3f372`; T31–T44 candidates need acceptance. |
| `stafford38-assembly-audit` | `5336b805deef` | `ActualSameWitnessAsymptoticConormal.lean`, original-prime consumer and `GeneralAsymptoticConormal.lean` rewire; unverified. |
| `stafford38-closure-repair` | `570455456326` | Earlier affine-fibre closure, away-factor/ground-point lifts, chart edit and literal closure consumer; unverified. |
| `stafford38-formal-palomar-gates` | `b1f33471467b` | Challenge source policy, comparator wrappers, verifier/bootstrap scripts and behavioral fixtures; actual final-package qualification remains open. |
| `stafford38-rc3-final-worker` | `feb87b498b13` | Broad rc3 migration/compatibility candidate and independent consumers; final combined replay remains open. |
| `stafford38-rc3-worker` | `78ca1edbea40` | Earlier broad rc3 migration candidate; compare with final-worker before selecting a source. |
| `stafford38-rc3-minimal` | `040acabc2429` | Smaller rc3 source/toolchain adaptation candidate. |
| `stafford38-rc3-saved` | `55768c0ec9a4` | Earlier broad source/status migration based on `b62f8cc0663a`; historical alternative, not current main. |
| `stafford38-review-bundle-candidate` | `3bd3b2926464` | Review generator, anchor script, map and rendering/asset tests; final paper/formal pins and full bundle regeneration remain open. |

The separate suffixes `stafford38-rc3-final-worker-index` and `stafford38-rc3-worker-index` preserve staged candidates when their staged trees differed from working-file snapshots. Exact base commits, patch digests and index commits are in [the synchronization manifest](docs/synchronization-2026-10-03.json). These branches preserve candidates; they do not extend any verification receipt.

On either host, fetch `origin`, then create a new checkout without disturbing the original worktree, for example:

```sh
git fetch origin
git worktree add --detach ../stafford38-resume-qwen origin/wip/sync-20261003/faepmac1/stafford38-qwen
```

Read the campaign plan and ledger before assigning work. Its historical Mac absolute paths must be adapted on another host. Keep the named base and patch digest when requesting a review; run the required consumers and verifier before accepting a proof candidate.
