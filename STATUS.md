# Current status

Updated 2 October 2026. Work resumed at the owner's request. Geometry assembly, Lean 4.35.0-rc3 migration, current Palomar qualification and reviewer-package repairs are being prepared in isolated worktrees. The final paper-aligned release and human-review handover remain open.

## Proof and correspondence

The repository has a verified proof of the unchanged main Stafford 3.8 challenge and its documented corollaries. The existing terminal proof still uses the earlier generic-divisor/Laurent geometry route. It does not yet establish full correspondence with Johanna's preserved geometric argument.

The paper-compatible route now has checked components for the selected normalization chart, the same-witness ground point and étale coordinates, common-open arc compatibility, coordinate-column transport, corrected tangent columns, tangent rank and the tangent-limit endpoint. Conditional adapters are proved under their stated inputs; they are not an unconditional construction of those inputs.

The remaining mathematical task is to assemble these components for one actual geometric witness, derive the affine conormal-closure conclusion from the original prime-variety hypotheses, and make that route carry the terminal theorem. The current audit identifies an existing generic-smooth-open producer and a direct constant-coordinate branch for the proposed wrapper; the repaired closure and wrapper still require compilation and independent checks. The full dependency audit must then confirm that the terminal proof no longer obtains this conclusion from the earlier alternative producer. Johanna's visible proof is preserved; only local, visibly tracked corrections or coordinate clarifications are proposed.

## Toolchain and checks

The checked-in toolchain remains Lean 4.33.0, with the pinned Mathlib and AlgebraicAnalysis revisions recorded in the repository configuration. The saved Lean 4.35.0-rc3 candidate is being reconstructed with exact remote dependency pins in an isolated worktree. It must pass the full build, independent consumers, axiom audits and current Palomar source checks before promotion and release.

Recent integrated geometry components have passed targeted builds and independent `--trust=0` consumer/axiom checks using only the standard axioms. An earlier full checkpoint passed 9,168 build jobs and 301 consumer/axiom reports; that receipt applies to its recorded source, not automatically to subsequent additions. The current full module build passed 9,181 jobs. The full verifier stopped at its 900-second limit during the serial consumer checks, without a reported build error. Its remaining stages have not passed as a whole; no completed full-verifier receipt for this checkpoint is claimed here.

AlgebraicAnalysis v0.3.3 is separately released on Lean 4.35.0-rc3. Its archived mathematical source is `bbbbf3fc358ca8100b158cec4cf47f336ab70163`, DOI [10.5281/zenodo.23104842](https://doi.org/10.5281/zenodo.23104842). The final formal migration will pin that source.

## Completion gate

Before the next formal release: finish the unconditional paper route and terminal wiring; remove redundant definitions and proof scaffolding without losing evidence; replay all checks on rc3; qualify the actual package with the current local Palomar scripts; regenerate the complete paper/Lean review bundle from exact committed inputs; update the archived version citations; and publish the release that triggers Zenodo.

Max will review the whole final paper/Lean correspondence, including challenge definitions and assumptions. Johanna will review the preserved paper and its marked local proposals, with mathematical explanations in prose. The final review handover is pending. No new formal or supplementary release has been published.

The current review map and supplementary assets refer to an older manuscript. They must be regenerated and every card re-anchored to the final selected paper. Current Palomar source policy also requires self-contained Challenge files; the isolation change must preserve the challenge definitions and pass both actual kernel comparisons on Linux.

See [the route map](docs/paper-route-alignment.json), [definition owners](docs/definition-owners.md) and [proof-source provenance](docs/proof-source-provenance.md). Historical receipts and release records retain their original scope.

## Saved candidate state

[The stopped-state archive](docs/audits/stopped-2026-10-02/README.md) records the exact bases, hashes and limitations of the unintegrated rc3 migration, affine-fibre closure candidate, dependency guard, verifier preparation and definition cleanup. Those archives preserve work for resumption; they are not part of the checked proof import graph.
