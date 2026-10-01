# Human-readable Overleaf review

The human-readable draft keeps the original author prose and visible AI
corrections, comments and mathematical qualifications. Thirteen long AI
formal-proof comparisons were moved to the separate editable
[technical supplement](../../paper-lean-audit/manuscript/lean_proof_details.tex),
with concise COMP comments beside the corresponding mathematics. The moved
text is preserved, apart from external-reference prefixes needed to compile
it separately. The generic-conormal clarification, coisotropic strengthening
and order-initial-ideal base-change lemma remain in the human-readable paper.

The default `formalref` macro displays only its mathematical qualification;
full declaration names stay in source. The supplement enables
`showleandetailstrue` and collects all declaration links. The formal-verification
paragraph now distinguishes verified results from certification of every
printed proof step. AI corrections remain proposals for human acceptance.

The human-readable PDF decreased from 46 to 35 pages; the technical supplement
compiles to 14 pages. Neither has unresolved references. Full-PDF text inspection
finds no long Stafford38 or AlgebraicAnalysis declaration names in the human
paper. All 101 source declaration links remain and pass the Lean declaration
kernel gate with standard axioms only. The 44 remaining main-document label
numbers are unchanged; 18 numbered technical proof steps move to the supplement.
All 55 audit excerpts and PDF page pointers are refreshed, and the tool's
48 tests pass. [The receipt](compact-human-review.json) records the exact pins
and hashes. Previous all-card artifact hashes are retained as historical evidence.
