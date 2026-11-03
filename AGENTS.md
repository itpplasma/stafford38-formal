# Agent guidance

- This repository contains the formal proof of Stafford's Conjecture 3.8. README.md and docs/proof-graph.yaml describe the theorem and its proof; docs/paper-route-alignment.json and docs/paper-lean-specification.md relate the manuscript to the Lean declarations.
- Preserve the pinned Lean, Mathlib, and AlgebraicAnalysis revisions. Do not add axioms, sorry, or terminal wrappers.
- Workers may prepare bounded documentation or proof changes, but the controller owns authoritative integration, release metadata, commits, and pushes.
- Run the repository verifier before claiming a substantive source change. A state-matching check is not a behavioral test.
- Keep repository files to facts the build, the verifier or Comparator checks, sources and authorship. Audit, review and process records belong in pull requests and Git history, not in tracked files.
- When the manuscript's Lean links change, update docs/paper-linked-declarations.json to match; scripts/check-paper-declarations.sh checks that every listed declaration exists and uses only the permitted axioms.
- The itpplasma/stafford38 research archive and itpplasma/stafford38-paper manuscript are not build dependencies.
