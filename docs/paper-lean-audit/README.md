# Manuscript correspondence

The [source index](source-index.md) links every category of material in the paper.

The [audit generator](../../tools/paper_lean_audit/README.md) and its
[declaration map](../../tools/paper_lean_audit/paper-lean-map.json) connect
manuscript claims to exact formal sources. Each card records the statement
relation, proof route, dependencies and remaining review issues. Checks include
manuscript declaration links and theorem-environment coverage. The pinned
Global Stafford result is linked to its separate formal repository; it is not
imported into Stafford38, which would create a dependency cycle.

The manuscript remains authoritative in the author's Overleaf-synchronized
`stafford38-paper` checkout. The [manuscript snapshot](manuscript/human_readable_main.tex)
and its [provenance manifest](manuscript/provenance.json) retain all TeX sources,
bibliography and visible annotations for correspondence review. The manuscript
retains its CC BY 4.0 license; the Lean software retains Apache-2.0. Refresh the
snapshot from Overleaf when editing the paper; do not edit two competing copies.

The [bibliography](references.bib) records the paper's literature, software and
proof-registry sources. The [workflow account](ai_workflow.tex) retains the
short research history, models and representative prompt from its AI appendix.
The [workflow evidence](workflow-evidence/README.md) retains historical skills,
protocols, model-use records and reconstruction sources. These are exposition
and provenance, rather than premises of the Lean theorem.

Run the generator's source checks and inspect its HTML or PDF alongside the
[verification evidence](../verification-results.json). Local browser reviews
are exported as JSON. Place reviewed exports in `reviews/` with a signed Git
commit. The [current source-pinned review ledger](review-status.json) records the active review inputs and scope; no automated review record is a human mathematical approval.

The Palomar registry record certifies the theorem and source revision it names.
The newer Zenodo archive also includes locally checked auxiliary declarations;
publication of that archive does not resubmit the theorem to Palomar.

The [current review ledger](review-status.json) records exact review inputs, completed formal checks, all57 review cards and pending human responsibilities. Classifications compare the proposed corrected text; the visible original and its historical findings remain available. Archived review ledgers keep their original source scope.
