# Agent guidance

- This repository is the completed Stafford 3.8 formalization. The README,
  `docs/verification-results.json`, and `docs/proof-graph.yaml` are the status
  authorities; there is no open theorem-formalization PLAN here.
- Preserve the pinned Lean/Mathlib/AlgebraicAnalysis revisions and recorded
  verification receipts. Do not add axioms, `sorry`, or terminal wrappers.
- Workers may prepare bounded documentation or proof-map changes, but the
  controller owns integration, release metadata, commits, and pushes.
- Run the repository verifier before claiming a substantive source change; do
  not treat a state-matching check as a behavioral test.
- Remaining work is human review, release hygiene, and publication, not a new
  formal proof obligation. Report adjacent documentation inconsistencies rather
  than silently changing mathematical status.
