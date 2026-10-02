# v1.3.0 formal-release metadata proposal

This directory contains candidates only; canonical repository files are untouched.

Candidate file diffs:
- `lakefile.toml`: package version 1.2.3 -> 1.3.0; Mathlib pin -> c55e6e786f49471c72fbddbec5415808896aec1e; AlgebraicAnalysis pin -> bbbbf3fc358ca8100b158cec4cf47f336ab70163.
- `CITATION.prearchive.cff`: version -> v1.3.0; remove current version DOI/date until Zenodo assigns and archive bytes are verified; preserve old version identifiers and concept DOI 10.5281/zenodo.22390721.
- `.zenodo.json`: version -> v1.3.0; update the `requires` identifier from AA v0.3.0 to AA v0.3.3 DOI 10.5281/zenodo.23104842. Preserve scope description for controller review against final verified proof route.
- `formalization.yaml`: no change. Its `version: "v0.4"` is the formalization metadata schema version, not project release version. Its embedded verification commit/report and status narrative should only be revised after the new evidence exists; do not claim the existing Palomar v2 record checks this new source.
- `lean-toolchain`: candidate target should be `leanprover/lean4:v4.35.0-rc3`; regenerate `lake-manifest.json` with `lake update`/the pinned Lake workflow after applying the candidate lakefile in the verified release checkout, then confirm exact AA/Mathlib revisions.
- Add a release note based on `RELEASE-NOTES-PENDING.md` only after final proof/review evidence exists. Keep all prior release receipts immutable.

Publication date and version DOI are intentionally unset. Zenodo concept DOI for this project already present in CFF: 10.5281/zenodo.22390721; that is not the v1.3.0 version DOI. AA v0.3.3 version DOI is 10.5281/zenodo.23104842.
