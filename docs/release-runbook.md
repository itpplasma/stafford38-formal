# Release procedure

The author authorized the public Apache-2.0 software releases and confirmed
that the Zenodo integration is enabled on 2026-09-08. This procedure covers
Stafford38 v1.1.0; manuscript publication and Palomar submission are separate
human actions. Human mathematical review remains open.

## Verify the source

Use the exact source commit in `docs/verification-results.json`. The release
commit may add documentation, citation metadata, verification evidence and the
built dossier after that snapshot. Its Lean sources, dependency pins,
Comparator configurations and verifier scripts must match the verified source.
Preserve the v1.0.2 report under `docs/verification/history/`.

The shared library dependency is AlgebraicAnalysis v0.3.0 at
`4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`. Lean and Mathlib remain v4.33.0;
the exact Mathlib commit is in `lake-manifest.json`. Its official public cache
was tested during release preparation.

Run in a clean public clone with fixed dependencies:

```bash
bash scripts/verify.sh
bash scripts/verify-palomar.sh
bash scripts/verify-palomar.sh comparator-fixed-source.json
```

All three commands passed on the controller host. On 2026-09-08 the author explicitly requested publication before the additional isolated-clone replay; that replay remains pending. Retain command exit statuses and log hashes,
20 endpoint axiom reports, 14 consumer reports, import audits, and the two
Comparator logs with both NanoDa and Lean acceptance. The one-shot Fable audit
and corrections are recorded in `docs/audits/exact-source-review-2026-09-08.md`;
they supplement the kernel checks.

## Build and publish

Build `docs/dossier/stafford38-challenge-dossier.tex` twice with LuaLaTeX.
Check references and layout, retain the PDF in the Git tree for Zenodo's source
archive, and attach the PDF and verification report to the GitHub release.
Check that the original `Challenge.lean` and `Solution.lean` match v1.0.2.
Commit and push the verified source and release metadata before signing:

```bash
formal_commit=$(git rev-parse HEAD)
test -z "$(git status --porcelain)"
git tag -s v1.1.0 "$formal_commit" -m 'Stafford38 v1.1.0: exact-source comparison'
git verify-tag v1.1.0
git push origin refs/tags/v1.1.0
```

Create the GitHub release at that tag with the reviewed notes and assets.
Do not move an existing tag. Wait for the Zenodo record, download its source
ZIP, and compare every archived file with the tagged Git tree. Record the
version DOI in a subsequent citation commit without moving the release tag.
Upload the final dossier to Slopbox for the author's review.

## Palomar submission

The author submits Stafford38 before Global Stafford, using the complete
40-character v1.1.0 release commit and `comparator-fixed-source.json`. This
configuration compares the stronger exact-source statement. The original
`comparator.json` remains available and is verified for compatibility.
Use `formalization.yaml` as metadata and the repository root as the project
directory. Use an existing Palomar identifier only when a registration receipt
confirms it. No submission receipt is retained in this repository.

Global Stafford then pins the exact Stafford38 release commit and the same
AlgebraicAnalysis release, passes its own Phase I/full/Comparator replay, and
publishes its release. AlgebraicAnalysis is a dependency library; this release
procedure does not create a separate Palomar theorem submission for it.
