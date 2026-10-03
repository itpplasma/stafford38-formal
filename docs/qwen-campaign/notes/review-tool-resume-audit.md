# Review map and bundle tooling audit (T60–T83)

Read-only tooling review for the controller. All generated maps, render output
and logs from this audit are in `/tmp/stafford-review-scratch`; no repository
tool, manuscript, Lean, PDF or supplementary asset was edited.

## Exact inputs

| Input | Revision/hash | Finding |
| --- | --- | --- |
| formal worktree at audit | `0203fa45329c8b10bd979ab1ad79b92fa4e42356` | Candidate branch compared against this base; concurrent untracked work was left alone. |
| saved review-bundle candidate | `3bd3b2926464c440acba0daaca63532c326bda2a` (parent `eed5291e072d7af8f9a48a242e498325d9c5e2c1`) | Versus formal HEAD, only `tools/paper_lean_audit/paper-lean-map.json` differs in the reviewed paths. Candidate tooling commits saved by that branch are already present at formal HEAD. |
| candidate map input from branch | SHA-256 `b820d00e459b78ae153daf23dcd1a11acfdb838c42c4bf09d41fa9613a2bb189` | Stored as `/tmp/stafford-review-scratch/reanchor-input.json`. |
| re-anchored candidate map | SHA-256 `2ebffb1a6cb69e2b331d5110b7345032fa3c3996e3ab20bbbdb7562cf0f2ea63` | 55 cards, 28 AI comments, candidate status remains `pending-final-source-pins`; all 55 paper ranges are within the selected file. |
| paper source checkout | `53882beb19c1491c43867fa78ee3b5bba3f18169` | `human_readable_main.tex` SHA-256 `fd707283bda604800400fd86cb31f9e3ab083f29a3fb8e556c230ccd83aaaa3b`. |
| standalone generator | `f0ce035538b4fa704109a34d14aa22265dec2a31` (`paper-lean-audit`, main) | `build.mjs` SHA-256 `70908923650dd2777d4681646ba0555f791845295e5a4bd772bfc42115cf303c`. |
| formal vendored generator | formal `tools/paper_lean_audit/build.mjs` SHA-256 `8f8131689c414a6508a1774ee038da5cd43d6c8618a3a33023c09fdda3cfa8ba` | Its current tests pass, but this is a distinct copy. `lean.mjs`, `texhtml.mjs`, CSS, browser JS and `test/build-validation.test.mjs` match the standalone current checkout; `build.mjs` and `test/texhtml.test.mjs` differ. |
| formal cached library pins | AlgebraicAnalysis `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` | Exact historical map pins are available locally. Current release proposal instead suggests AA `bbbbf3fc358ca8100b158cec4cf47f336ab70163` and Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; controller must use the accepted final manifest, not this audit’s cache. |
| supplementary current manifest | existing checked-in v0.1.3 | Still names old formal and paper commits and an older generator pin; refresh only from final accepted source/asset receipts. |

## Candidate and tool behavior

The re-anchor command succeeds against the current paper commit:

```sh
python3 scripts/reanchor-review-map.py \
  --paper /home/ert/proj/stafford38-paper \
  --paper-file human_readable_main.tex \
  --commit 53882beb19c1491c43867fa78ee3b5bba3f18169 \
  --map /tmp/stafford-review-scratch/reanchor-input.json
```

It reports 55 cards and 28 comments and records the paper commit/file hash in
`candidate.manuscript`. It deliberately leaves `sources.paper` at the old
formal snapshot and labels the candidate pending. That is useful as a frozen
draft, but it is not yet a renderable final map: promoting the accepted paper
repository/commit/file into `sources.paper` (or a byte-matching committed
formal-repository snapshot with its paper origin recorded) is required before
generation. The map must likewise be repinned to the accepted public formal
source and exact AlgebraicAnalysis/Mathlib pins, and the candidate status must
not be presented as complete until those sources and receipts are accepted.

For diagnosis, I copied the scratch map and pointed its primary paper source
at the current paper commit while intentionally leaving its formal source at
historical v1.2.3. The current standalone generator wrote HTML but exited 1
with 40 source-resolution errors and 32 warnings. This confirms the old formal
pin cannot support the restored current paper’s Lean references: among the
unresolved items are `PaperSameWitnessTangentDimension` and
`PaperActualWitnessConormalData` files absent from v1.2.3, plus moved or renamed
declarations. These are expected stale-pin failures, not evidence against the
unaccepted candidate route. The complete summarized diagnostic is
`/tmp/stafford-review-scratch/render-current-paper-check.log` (SHA-256
`6eaf84023ac4d7007be9f039053bc69c7e8195f5605d8e77d116b1ba5aabfa87`). A second
check against the old formal paper snapshot also exits 1 because the newly
re-anchored ranges belong to the current paper, not that historic snapshot.

The underlying standalone generator already renders the challenge templates,
their curated definitions and proved endpoints from `challenge_definitions`
and `challenge_endpoints`. The map has 32 definition references and both main
proved endpoints (`Stafford38Challenge.universalStatement` and
`Stafford38FixedSourceChallenge.universalFixedSourceStatement`); the cards
include 14 whole-proof correspondence prompts. No generator feature is needed
for those two Challenge/Solution comparisons. The T61 additions are the
missing map work: one paper-location/correspondence row for every accepted
top-level theorem in `Stafford38/Geometry/SameWitness/`, explicitly marking
declarations with no paper counterpart. Keep the author’s visible proof and
AI proposal state intact; neither generated checks nor Max’s review substitutes
for Johanna’s acceptance.

The standalone generator accepts arbitrary pinned repositories with
`--source NAME=PATH`; `scripts/rebuild.py` in the supplementary bundle uses
this feature to fetch its map sources. Therefore T83 can render a paper source
in `stafford38-paper` separately from the formal repository. By contrast,
formal `scripts/build-review-site.py` currently requires paper and formal to
have the same repository and reads both frozen paper bytes and PDFs via the
formal root. For T81 either use a byte-matching committed manuscript snapshot
inside the selected formal revision, or update this wrapper to accept a
separate paper checkout and resolve its exact commit. The latter requires
changes to `scripts/build-review-site.py` and behavioral fixtures in
`scripts/tests/test_review_site_assets.py`; it was not authorized in this task.

At supplementary T83, use the verified public standalone generator commit,
not an unreviewed local checkout; update `manifest.json`’s `generator` pin and
version/hash metadata consistently with the final bundle. Run its existing
`scripts/rebuild.py` only after final map/source/PDF receipts exist. Then check
map declaration links, both Challenge/Solution endpoints, full paper proof
coverage, every PDF/ZIP asset hash, and HTML layout. The existing HTML rebuild
does not generate PDFs or the archive ZIP.

## Checks run

- Re-anchor script: exit 0; map 55 cards/28 comments; 0 invalid line ranges.
- Standalone generator `npm test`: 63 passed, 0 failed, 1 skipped because the
  sibling paper clone was not present at that test’s expected path. Log SHA-256
  `c36b2aabfd78886e7beab8b0b7142aa252dd2d6883b91f6950511bda0a34c557`.
- Formal vendored generator `npm test`: 64 passed, 0 failed, 0 skipped. Log
  SHA-256 `c17be97ae4799641bd6dbf0b02f962fe9b84b35cffaa30e19a73cc56e543dcfc`.
- `scripts/tests/test_review_site_assets.py`: 7 passed. Log SHA-256
  `adee6bebc6937962dc1e19c422be6291eb02d264b51cccf8c25c78a8cda530eb`.
- No Lean check, PDF build or public bundle build was run.

## Next owned paths for the controller

Wait for accepted declaration names, final source commits and final dependency
pins. Then update/review the formal map at
`tools/paper_lean_audit/paper-lean-map.json` and T61’s
`docs/qwen-campaign/notes/T61-paper-map.md`; update the supplementary map and
its source manifest/artifact hashes under `/home/ert/proj/stafford38-supplementary`
for T83. T81’s `scripts/build-review-site.py` is the only identified tooling
path that may need separate-paper support. Preserve human review as pending;
Max’s scope is every selected paper proof and both Challenge/Solution pairs,
while Johanna reviews and responds to the marked Overleaf proposals.

