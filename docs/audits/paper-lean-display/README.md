# Complete paper–Lean display review

This is the historical display audit at the source pins recorded in `verification.json`. It does not cover the current same-witness assembly or the next release. The [current route map](../../paper-route-alignment.json) records their scope.

The five historical Lean probes are preserved byte for byte as `.lean.txt` files, with their original paths, source commit and hashes in [the archive index](archive-source-locations.json). This keeps the evidence intact without submitting old diagnostic programs as current Lean sources. Historical receipts retain their original paths; restore the recorded filenames to replay those probes at their recorded configuration.

All 55 cards were independently reviewed in three frozen partitions. The
[inputs](cards-1-inputs.json), [first report](cards-1.md), [second report](cards-2.md),
[third report](cards-3.md), and [tool review](tool-review.md) preserve the findings
before integration. The [final tool check](tool-final-review.md) independently
confirms all six repairs and the final artifact hashes. They are AI review evidence; human acceptance remains pending.
The reports describe the earlier display, so their baseline test counts and
missing links are historical. [Final verification](verification.json) records
the exact integration base, tool patch digest, source pins and artifact hashes.

## Integrated repairs

- Show locally available variables, universes, notation, opens and instance
  signatures with pinned source links. Imports and other inferred instances
  remain available in the linked full module.
- Preserve blank-separated pattern branches and structure fields; mark omitted
  bodies and excerpt limits. Expand named result propositions and explicit
  imported predicates without guessing among ambiguous or shadowed names.
- Show the actual source repository on each declaration. Review criteria,
  vocabulary and generator code now invalidate stale review sign-offs.
- Add omitted right-PBW, associated-graded, symbol-action, finite-length,
  quotient-filtration and noncharacteristic links. Mark specialized results,
  partial conventions and different proof routes explicitly.
- Repair excerpt boundaries around AI annotations and retain proposed red text
  as a proposal. Link historical editorial issues to their existing AI comments;
  do not describe a pending proposal as a human-approved correction.

## Evidence and limits

Both tool copies pass 48 tests, with no failures or skips. The rendered 55-card
HTML has 3,248 Lean excerpts from 142 pinned files; an independent Git-source
comparison checks each excerpt and source range. Chromium checks the abstract
quantifiers, coordinate condition, both weight branches, AI comment link and
expandable signatures. The PDF prints all expanded context and has 258 pages.
The source-comparison and browser scripts retain their execution-environment
paths; adjust those paths to rerun elsewhere.

Lean checks with `--trust=0` cover 252 mapped public declarations from Stafford38,
AlgebraicAnalysis and Mathlib, six separately imported challenge proposition
definitions, and the additionally linked quotient filtration. All report only
the standard axioms `propext`, `Classical.choice`, `Quot.sound` where needed.
Challenge templates containing intentional placeholders are not presented as
proved endpoints. The compressed logs and probe source are retained here.
Global Stafford links were checked against pinned source and existing archive
verification; a fresh Global kernel replay was not completed in this repair.

The human manuscript and mathematical Lean source were not edited. Remaining
paper issues are visible in the map: the abstract's coordinate refinement omits
the positive-rank condition, the tangential-finiteness proof needs its finite
module bridge, and generic geometry/filtration claims exceed some specialized
Lean statements. Original blue Euler formulas still need human resolution of
the red correction. Those are mathematical/editorial review items, not tool
successes. Historical comments remain historical unless checked against the
current excerpt. In particular, `k_0 := k` already resolves the alleged field
mismatch and is not reported as an outstanding defect.
