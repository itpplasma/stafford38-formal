# Proof-source provenance

## Sources and status

The Lean repository records a verified proof of Stafford's Conjecture 3.8 at source revision f6915782d2281e3d3b51011b97ace866928053b9. Its clean-checkout receipt is preserved at [the historical verification record](verification/f6915782/verification-results.json). That receipt certifies only the named source and configuration.

The selected manuscript is human_readable_main.tex, based on paper commit 7d10c6297f8367b3f0061d61bda5ae86f9945c2c and SHA-256 6fcd4afc1008978154762755a0a142ad69a22e03ee3d57223df2618f4f0b3800. The preserved restoration is commit bd913a381b714fd8f909159a33fe845b5373ba0f, recorded as pushed to GitHub paper main and Overleaf main. The visible author proofs remain intact, with local mathematical proposals marked for review.

The current annotated review is paper commit `4d19a183846beb50f37ad2b4e51e836a76ed8bac`, human-readable source SHA-256 `a6a50d1a46fccb964ba72a0f60a85aec46b4d20e7d17e7a248dd152e62c87a88`, with public snapshot `2fde6c6311b9cc2e8b789649132ff87bdbcdb3d5`. It preserves the author baseline named above and marked correction proposals.

The historical receipt covers the formal theorem at its named source and configuration. The v1.3.0 source `12ae3cc49152672a48a96f13994314b65ae38197` separately passed the complete pinned Linux verifier and all four Palomar comparator configurations, including a 4,475-job build and strict four-root dependency inspection with zero forbidden or unavailable dependencies. The verified source uses Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163`. The receipt does not establish full manuscript correspondence: the paper-route map records that claim separately, while Max’s full comparison review and Johanna’s review of the visible manuscript and marked proposals remain pending.

## Review responsibilities

Max’s review of the complete paper proof and both Challenge/Solution comparisons, including statement scope and proof correspondence, remains pending. Johanna’s review of the selected visible manuscript and marked local proposals also remains pending; the proposals do not replace the visible author proof. Automated checks and AI review do not replace either human review.

## Source authority

The formal repository owns Lean declarations, proof maps, and verification records. Overleaf is the manuscript editing authority; pinned Git revisions preserve review inputs. The itpplasma/stafford38 research archive records development history and task planning, while the older paper mirror records manuscript provenance. Neither is a formal build dependency. The Palomar entry certifies only its named theorem and source revision.

For maintenance, read PLAN.md, docs/proof-graph.yaml, docs/verification-results.json, and docs/paper-route-alignment.json. Consult the research archive for chronology and the pinned manuscript when checking a paper comparison.
