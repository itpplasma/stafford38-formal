# Agent guidance

- This repository is the completed Stafford 3.8 formalization. `PLAN.md` is a
  pointer-only status file; the README, `docs/verification-results.json`, and
  `docs/proof-graph.yaml` are the detailed authorities. There is no open
  theorem-formalization task here.
- Preserve the pinned Lean/Mathlib/AlgebraicAnalysis revisions and recorded
  verification receipts. Do not add axioms, `sorry`, or terminal wrappers.
- Workers may prepare bounded documentation or proof-map changes, but the
  controller owns integration, release metadata, commits, and pushes.
- Run the repository verifier before claiming a substantive source change; do
  not treat a state-matching check as a behavioral test.
- Remaining work is human review, release hygiene, and publication, not a new
  formal proof obligation. Report adjacent documentation inconsistencies rather
  than silently changing mathematical status.

## Proof-source provenance

Read `docs/proof-source-provenance.md` before any work that touches theorem,
manuscript, or provenance status. The canonical proof is already this formal
repository. `itpplasma/stafford38` is the private research archive and
`itpplasma/stafford38-paper` is the manuscript mirror; they are not build
dependencies and do not create a new open formalization task. For manuscript
correspondence use the recorded paper revision and `main.tex` / `proof_map.tex`
as listed in the provenance document.
