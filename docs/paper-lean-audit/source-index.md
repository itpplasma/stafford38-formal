# Paper source index

| Paper content | Auditable source |
| --- | --- |
| Main text, introduction, proofs and appendices | [Manuscript snapshot](manuscript/human_readable_main.tex), [snapshot hashes](manuscript/provenance.json) |
| Detailed formal comparisons retained separately | [Technical supplement](manuscript/lean_proof_details.tex), [standalone TeX](manuscript/lean_proof_details.tex), [compact-review receipt](../audits/paper-lean-display/compact-human-review.md) |
| Numbered claims and proof steps | [Correspondence map](../../tools/paper_lean_audit/paper-lean-map.json), [proof specification](../paper-lean-specification.md) |
| Every named Lean declaration in the paper | [Declaration manifest](linked-declarations.json), checked by [the kernel gate](../../scripts/check-paper-declarations.sh) |
| Literature, libraries and registered proofs | [Bibliography](references.bib), [archive receipts](../releases/zenodo.md) |
| AI research history, models, prompts and skills | [Appendix source](ai_workflow.tex), [workflow evidence](workflow-evidence/README.md) |
| New cyclicity and noncharacteristic results | [Frozen AI reviews](../audits/manuscript-corollaries.md), [verification receipt](../verification-results.json) |
| Mathematical dependency structure | [Proof graph](../proof-graph.yaml), [proof guide](../proof-guide.md) |
| Complete AI display/source review | [Frozen reports and integration evidence](../audits/paper-lean-display/README.md) |
| Human correspondence reviews | [Review records](reviews/README.md), [review generator](../../tools/paper_lean_audit/README.md) |

AlgebraicAnalysis and Global Stafford have separate canonical repositories and
immutable archive citations. Their exact source revisions are pinned in the
map and build manifest. Linking those sources preserves their ownership;
Global Stafford is not imported into Stafford38 because it depends on it.
Cited publications remain external works identified by their bibliographic
records. The snapshot retains visible AI additions and removed text; the map
states the relationship between the proposed current text and Lean.
