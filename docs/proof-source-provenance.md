# Proof-source provenance

## Sources and status

The Lean repository records a verified proof of Stafford's Conjecture 3.8 at source revision f6915782d2281e3d3b51011b97ace866928053b9. Its clean-checkout receipt is preserved at [the historical verification record](verification/f6915782/verification-results.json). That receipt certifies only the named source and configuration.

The selected manuscript is human_readable_main.tex, based on paper commit 7d10c6297f8367b3f0061d61bda5ae86f9945c2c and SHA-256 6fcd4afc1008978154762755a0a142ad69a22e03ee3d57223df2618f4f0b3800. The preserved restoration is commit bd913a381b714fd8f909159a33fe845b5373ba0f, recorded as pushed to GitHub paper main and Overleaf main. The visible author proofs remain intact, with local mathematical proposals marked for review.

The current annotated review is paper commit P5 `75f79630141f2bbeedc4e154288978020c7f2e83`, human-readable source SHA-256 `a68b21fc1012da2f431aeb91e17226d657f483eb4a2cf8a152499b2fd427ea6b`, with public snapshot S5 `973fa2831cf7520fc42566587e3946b4b7444093`. Relative to P4, only citation text and bibliography entries changed; the author proof and marked proposals are preserved. The published supplementary v0.2.0 remains the immutable P4/S4 bundle at commit `31aea05344c3fa35fb19a3ff35f7518d723e26ec`, DOI `10.5281/zenodo.23127103`.

The historical receipt covers the formal theorem at its named source and configuration. Formal core C2 `12ae3cc49152672a48a96f13994314b65ae38197` passed the complete pinned Linux verifier, retained R2 targets, all four Palomar comparisons and the 399-name declaration audit. Signed formal v1.3.0 release R `54c4f0c902bcd840e44eeba80686ef3fa0e7dc2b` (DOI `10.5281/zenodo.23126868`) contains the 656 core files byte-for-byte; all 1,163 tagged files matched the published archive. These source and archive receipts do not establish full manuscript correspondence. The P5/S5 review input is recorded separately; Max’s full correspondence review and Johanna’s review of the visible manuscript and marked proposals remain pending.

## Review responsibilities

Max’s review of the complete paper proof and both Challenge/Solution comparisons, including statement scope and proof correspondence, remains pending. Johanna’s review of the selected visible manuscript and marked local proposals also remains pending; the proposals do not replace the visible author proof. Automated checks and AI review do not replace either human review.

## Source authority

The formal repository owns Lean declarations, proof maps, and verification records. Overleaf is the manuscript editing authority; pinned Git revisions preserve review inputs. The itpplasma/stafford38 research archive records development history and task planning, while the older paper mirror records manuscript provenance. Neither is a formal build dependency. The Palomar entry certifies only its named theorem and source revision.

For maintenance, read PLAN.md, docs/proof-graph.yaml, docs/verification-results.json, and docs/paper-route-alignment.json. Consult the research archive for chronology and the pinned manuscript when checking a paper comparison.
