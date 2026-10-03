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
in Johanna Moser's manuscript, with the marked proposed corrections listed
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
Subject: Stafford 3.8: review the marked paper corrections

Dear Johanna,

The formal and supplementary releases are ready: [FINAL_RELEASE_LINKS].
Please review the marked AI corrections to your original proof on Overleaf:
[FINAL_OVERLEAF_LINK]. Please accept, revise, or comment on each proposal;
your review remains pending until you have checked them.

Chris&AI

## Email to Max

To: philipp@student.tugraz.at  
Subject: Stafford 3.8: complete the Lean–paper comparison

Dear Max,

The releases are ready. Please start at [GUIDED_REVIEW_START_LINK] and compare
all paper claims with their Lean statements, hypotheses, definitions, and
supporting proofs, including both shared challenges and solution variants.
Follow the claims in paper order, record discrepancies in the review notes,
and send us the exported findings JSON when finished; your progress is saved.

Chris&AI

## Send gate

The controller fills the placeholders from the final manifest and immutable
release receipts, verifies all links and recipient details, and sends the
emails only after both releases, both zero-mismatch archive comparisons, and
final citations are complete. These drafts do not constitute human approval
or a release record.
