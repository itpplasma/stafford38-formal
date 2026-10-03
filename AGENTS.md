# Agent guidance

- This repository contains the formal proof of Stafford's Conjecture 3.8. Its recorded terminal theorem source has a clean-checkout receipt. The selected manuscript-to-Lean correspondence is separate; see docs/paper-route-alignment.json for its current scope and status. README.md, docs/verification-results.json, and docs/proof-graph.yaml describe the theorem and its evidence.
- Preserve the pinned Lean, Mathlib, and AlgebraicAnalysis revisions and all historical verification receipts. Do not add axioms, sorry, or terminal wrappers.
- Workers may prepare bounded documentation or proof changes, but the controller owns authoritative integration, release metadata, commits, and pushes.
- Run the repository verifier before claiming a substantive source change. A state-matching check is not a behavioral test.
- Keep the formal theorem and manuscript correspondence as distinct review claims. Do not claim whole-proof correspondence from a terminal theorem receipt or from a different formal route.

## Proof-source provenance

Read docs/proof-source-provenance.md before changing theorem, manuscript, or provenance materials. The theorem's formal proof and the selected paper-to-Lean comparison have separate evidence and status. For manuscript correspondence, use the selected human_readable_main.tex review surface and docs/paper-route-alignment.json; preserve the visible author proof and track local proposals for review. The itpplasma/stafford38 research archive and itpplasma/stafford38-paper mirror are provenance records, not build dependencies.
