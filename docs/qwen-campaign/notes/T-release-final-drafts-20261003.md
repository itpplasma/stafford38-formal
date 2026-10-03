# Final release and review email drafts

Drafts only, prepared 3 October 2026. The current campaign ledger still has
source freeze, final replay, Palomar comparisons, final correspondence bundle,
release and archive checks open. Do not publish or send these drafts until the
controller replaces every bracketed field from accepted immutable receipts.
No tag, release, DOI, final site URL, or reviewer response is asserted here.

## Formal release notes: Stafford38 v1.3.0

**Release title:** Stafford's Conjecture 3.8 for Weyl algebras: paper-route formalization v1.3.0

This release records the verified formal source for Stafford's Conjecture 3.8
and its fixed-source strengthening. The main solution follows the construction
in Johanna Moser's manuscript, with the accepted explicit corrections listed
in the paper-route review record. The visible author proof remains preserved
in the review manuscript.

The `Challenge` and `FixedSourceChallenge` declarations are unchanged and are
shared by the paper-conforming main solution and the separately named
`AlternativeSolution` and `AlternativeFixedSourceSolution` routes. The
alternative preserves the earlier generic/Laurent-series argument; it is not
presented as the manuscript's proof. This release also removes the retired
Mac/Pi campaign wrappers while retaining historical verification receipts,
pinned dependencies, useful mathematical modules, and review evidence.

- Immutable formal source: `[FINAL_FORMAL_COMMIT_40_HEX]`
- Lean: `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `[FINAL_MATHLIB_COMMIT_40_HEX]`
- AlgebraicAnalysis: `[FINAL_ALGEBRAICANALYSIS_COMMIT_40_HEX]` (v0.3.3; dependency DOI `10.5281/zenodo.23104842`)
- Clean-checkout verifier and source receipt: `[FINAL_FORMAL_VERIFICATION_RECEIPT_PATH_AND_SHA256]`
- Palomar local source-policy/kernel comparison receipt: `[FINAL_PALOMAR_COMPARATOR_RECEIPT_PATH_AND_SHA256]`
- Release tag and signed-tag verification: `[FORMAL_V1_3_0_TAG_AND_SIGNATURE_RECEIPT]`
- Full paper-correspondence map and review inputs: `[FINAL_PAPER_ROUTE_MAP_PATH_AND_SHA256]`
- Correspondence and human review: Max's complete paper/Lean review remains pending; Johanna's review of marked manuscript corrections remains pending.
- Release archive: `[FORMAL_ZENODO_ARCHIVE_RECEIPT_PATH_AND_SHA256]`; record the version DOI only after the archive matches the immutable tag file by file: `[FORMAL_VERSION_DOI_AFTER_ZERO_MISMATCH_ARCHIVE_CHECK]`

The existing Palomar v2 entry and earlier verification receipts apply only to
the sources and declarations they name. They do not certify this release or
establish complete manuscript correspondence. Online Palomar registration
remains an owner action.

## Supplementary release notes: Stafford38 reviewer companion v0.2.0

**Release title:** Stafford38 supplementary reviewer companion v0.2.0

This companion freezes the annotated manuscript, paper-ordered review map,
proof accounts, and browser interface against the exact public paper, formal,
and audit-generator revisions below. It preserves Johanna's visible author
proof and marks local mathematical corrections for her review. The main
formal route follows the manuscript construction; the earlier generic/Laurent
route remains separately labeled as an alternative. Both routes use the same
unchanged `Challenge` and `FixedSourceChallenge` statements.

The review site provides Max one paper-order starting point, sequential claim
navigation, saved progress, and finding export. Each entry places the paper
passage beside the Lean declaration, explains relevant definitions and
hypotheses, and keeps known gaps and proposed corrections visible. Proof and
build details remain available separately from the mathematical
correspondence assessment. The companion can be read without Lean or private
repository access.

- Immutable paper source: `[FINAL_PAPER_COMMIT_40_HEX]`
- Immutable formal source: `[FINAL_FORMAL_COMMIT_40_HEX]` (v1.3.0; DOI `[FORMAL_VERSION_DOI_AFTER_ZERO_MISMATCH_ARCHIVE_CHECK]`)
- Immutable audit-generator source: `[FINAL_GENERATOR_COMMIT_40_HEX]`
- Companion tag and signed-tag verification: `[SUPPLEMENTARY_V0_2_0_TAG_AND_SIGNATURE_RECEIPT]`
- Bundle manifest and paper/Lean map: `[FINAL_COMPANION_MANIFEST_AND_MAP_PATHS_WITH_SHA256]`
- HTML rebuild, link/layout, PDF, ZIP, and archive-content receipts: `[FINAL_T83_RECEIPT_PATH_AND_SHA256]`
- Companion archive: `[SUPPLEMENTARY_ZENODO_ARCHIVE_RECEIPT_PATH_AND_SHA256]`; assign the version DOI only after a zero-mismatch comparison against the immutable tag: `[SUPPLEMENTARY_VERSION_DOI_AFTER_ZERO_MISMATCH_ARCHIVE_CHECK]`
- Human review: Johanna's manuscript review and Max's complete paper/Lean correspondence review remain pending until they report their findings.

The companion archive DOI is distinct from the formal release DOI and from the
AlgebraicAnalysis dependency DOI. The historical v0.1.3 bundle remains tied
to its original sources and is not replaced by this release.

## Email to Johanna Moser

To: j.moser@tugraz.at  
Subject: Review of the marked Stafford 3.8 manuscript corrections

Dear Johanna,

We have completed the formal and supplementary release checks for the
paper-route version of Stafford's Conjecture 3.8. The review manuscript keeps
your proof visible and marks each proposed mathematical correction for your
attention. Overleaf remains the editing authority; we have not treated the
formal verification as approval of manuscript changes.

Could you review the marked passages in the annotated manuscript and tell us
which corrections you accept, would revise, or do not accept? The pinned
manuscript and review materials are here: `[FINAL_ANNOTATED_MANUSCRIPT_OR_OVERLEAF_REVIEW_LINK]`.
The released paper and formal revisions are `[FINAL_PAPER_COMMIT_40_HEX]` and
`[FINAL_FORMAL_COMMIT_40_HEX]`; the local proof-correspondence status and its
open items are summarized at `[FINAL_PAPER_ROUTE_REVIEW_LINK]`.

Please send your comments or edit the marked proposals in Overleaf, as you
prefer. We will keep the proposals pending until you have reviewed them.

Best,  
Chris&AI

## Email to Max Philipp

To: philipp@student.tugraz.at  
Subject: Complete paper-to-Lean review for Stafford's Conjecture 3.8

Dear Max,

The formal and supplementary releases are ready for the complete
paper-to-Lean correspondence review. Please start at `[GUIDED_REVIEW_START_LINK]`
and follow the claims in paper order. The interface preserves your place and
provides previous/next navigation; it also offers a checklist, finding notes,
and JSON export so you can resume later or return your findings without
installing Lean or accessing private repositories.

Please compare every paper claim with its Lean declaration, including the
definitions, hypotheses, and supporting lemma statements. Review both
`Challenge`/`Solution` comparisons: the `Challenge` and
`FixedSourceChallenge` statements are shared unchanged, while the main
solution follows the manuscript construction and the older generic/Laurent
proof is a separately labeled alternative. The entries mark proposed
corrections, known gaps, and incomplete correspondence explicitly. Build,
kernel-comparison, and axiom-audit evidence is linked separately; those checks
do not decide whether the paper proof and formal proof correspond.

Please record any missing claim, scope difference, hypothesis mismatch,
unsupported implication, or other issue in the entry notes, then export the
review JSON here: `[REVIEW_FINDINGS_EXPORT_INSTRUCTIONS_OR_DESTINATION]`.
The bundle is pinned to paper `[FINAL_PAPER_COMMIT_40_HEX]`, formal
`[FINAL_FORMAL_COMMIT_40_HEX]`, and generator
`[FINAL_GENERATOR_COMMIT_40_HEX]`. The supporting receipts are collected at
`[FINAL_REVIEW_EVIDENCE_INDEX_LINK]`.

Thank you for checking the full correspondence. We will leave the review
status open until you have completed it.

Best,  
Chris&AI

## Send gate

The controller fills the placeholders from the final manifest and immutable
release receipts, verifies all links and recipient details, and sends the
emails only after both releases, both zero-mismatch archive comparisons, and
final citations are complete. These drafts do not constitute human approval
or a release record.
