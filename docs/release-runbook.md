# Release procedure

The author authorized pulling, verifying, signing and publishing Stafford38
v1.2.0, including the manuscript correspondence snapshot, and updating the
paper's archive citations. Overleaf remains the manuscript editing authority.
Human mathematical review remains open. This release does not resubmit to Palomar.

## Verify the source

Use the exact source commit in `docs/verification-results.json`. A later release
commit may add documentation, citation metadata, verification evidence and the
built dossier. Its Lean sources, dependency pins, Comparator configurations and
verifier scripts must match the verified source. Preserve historical reports
under `docs/verification/history/`.

The dependency remains AlgebraicAnalysis v0.3.0 at
`4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`, with Lean v4.33.0 and the exact
Mathlib commit in `lake-manifest.json`. Newer library releases do not silently
replace the dependency used by this proof.

Run in an isolated clean clone at the selected commit:

```bash
bash scripts/verify.sh
bash scripts/verify-palomar.sh
bash scripts/verify-palomar.sh comparator-fixed-source.json
```

Retain exit statuses, log hashes, endpoint and consumer axiom reports, the
paper-linked declaration audit, import audits, and both Comparator logs with
NanoDa and Lean acceptance. State whether the clone reused a compiled cache;
a warm cache is not a cold rebuild. Independent AI proof reviews supplement
kernel checks and are distinct from human review.

## Build and publish

Build `docs/dossier/stafford38-challenge-dossier.tex` twice with LuaLaTeX.
Check references and layout, retain its PDF in the Git tree for Zenodo, and
attach the PDF and verification receipt to the GitHub release. Preserve both
compared theorem interfaces and their fixed dependency pins.

Commit and push the verified source and release metadata. Sign a new immutable
`v1.2.0` tag, verify its signature, push it, and create the GitHub release with
the release notes and assets. Do not move an existing tag. Wait for Zenodo,
download its source ZIP, and compare every archived file with the tagged Git
tree. Record the version DOI in a subsequent citation commit without moving
the release tag. Refresh the paper's bibliography and the formal repository's
manuscript snapshot together, and push both paper remotes.

## Registry scope

The existing Stafford38 registry entry is
[PALOMAR-2026-09-05-000007 v2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2).
It certifies the theorem and source revision named by that entry. Local replay
of both Comparator configurations and publication of newer auxiliary proofs
do not constitute a new registry version.

The separate Global Stafford archive is v1.0.6 at
[10.5281/zenodo.22669444](https://doi.org/10.5281/zenodo.22669444), alongside
[PALOMAR-2026-09-09-000001 v2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-09-000001&version=2).
Its exact version remains pinned in the manuscript correspondence map.
