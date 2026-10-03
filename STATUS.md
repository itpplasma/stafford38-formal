# Current status

Updated 3 October 2026. Formalv1.3.1 corrects historical verification-report routing and the stale isolated-replay status. It is published at f9448d6307fa25aff9d9f94ce0a9c7f9b03e63ff, DOI 10.5281/zenodo.23127367, with all 1,172 archive files byte-verified; mathematical sources, dependency pins and verifier programs are unchanged. The owner will resubmit R131 to Palomar. Corrected supplementaryv0.2.1 is published at6517aa94ac04dfc2cae3b8b89636d631da1cded6, DOI 10.5281/zenodo.23127468, and all 29 tagged archive files match.

Earlier proof acceptance: The v1.3.0 source `12ae3cc49152672a48a96f13994314b65ae38197` passed the complete pinned Linux verifier and all four Palomar comparator configurations. The fresh C2 run passed a 4,475-job Lake build and strict dependency inspection of all four terminal roots with zero forbidden or unavailable dependencies. T34, T35, T36, and T41 modules, literal trust-zero consumers, and all four main and alternative solution assemblies passed with only propext, Classical.choice, and Quot.sound. Formal v1.3.0 is published and its 1,163-file Zenodo archive is byte-verified (DOI 10.5281/zenodo.23126868). Supplementary v0.2.0 is also published and byte-verified (DOI 10.5281/zenodo.23127103); a requested v0.2.1 patch will carry corrected comparison labels and the current ledger. Paper-correspondence reviews and the final handover remain pending.

## Proof and correspondence

The repository has historical verified checkpoints for the unchanged main Stafford 3.8 challenge and documented corollaries. The v1.3.0 source rewires the terminal asymptotic-conormal step through same-witness closure and the original-prime route; the generic/Laurent route remains a separately checked alternative. Full correspondence with Johanna’s preserved geometric argument remains subject to human review.

The candidate’s same-witness closure and original-prime modules, literal consumers, chart, ground-point, étale, column, and tangent components passed their scoped checks. The shared main and alternative solution assemblies and complete repository verifier also passed on Linux. Whole-paper correspondence remains a separate pending human review.

The affine-fibre closure and original-prime wrapper passed their module and literal-consumer checks. The successful final C2 run verified frozen public source `12ae3cc49152672a48a96f13994314b65ae38197`; the earlier failed attempts remain preserved in the [campaign ledger](docs/qwen-campaign/STATE.md) and are not counted as successes.

The final dependency audit, repository verifier, and four actual Palomar comparisons passed on the frozen C2 source; detailed source-scoped evidence is linked from [verification.md](docs/verification.md). These results certify formal verification and the compared Challenge/Solution configurations, not end-to-end manuscript proof correspondence. Max’s whole paper-to-Lean review and Johanna’s review of the visible author proof and marked proposals remain pending.

## Toolchain and completed checks

The saved source targets Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163`.

The isolated baseline completed 425 explicit targets, comprising 4,455 Lake jobs, at base `eed5291e072d7af8f9a48a242e498325d9c5e2c1` and patch SHA-256 `e7a467c3622d3782ead45b91a89fc3bfc573f9c7d6de28a49662c420f16be361`. All 116 independent consumers and 312 axiom reports subsequently passed at patch SHA-256 `315f910ee3acedc91f2d95b76813e3b67a4d59cebfb489a2abeed73532a754ae`. Three retained proof wrappers passed independent `--trust=0` compilation. The controller checked the integrated source hashes against the frozen migration and compatibility manifests. The separately authorized Euler-owner cleanup at `2e27340` was preserved from upstream; its focused Lean 4.33 trust-zero receipt remains historical. The later rc3 C2 replay and its exact source scope are recorded above; these historical counts and receipts retain their original scope. Source identity checks are integrity checks, not proof tests.

The local source-policy preflight and comparator behavior fixtures remain separate supporting checks; they are not substitutes for the completed C2 proof receipts. The final run used Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163` (v0.3.3, DOI 10.5281/zenodo.23104842).

Historical Lean 4.33 checkpoints passed 9,168 build jobs and 301 consumer/axiom reports, and later 9,181 build jobs. The latter full verifier stopped at its 900-second limit during serial consumers. Historical receipts retain their original source and configuration scope.

AlgebraicAnalysis v0.3.3 is separately released on rc3. Its archived mathematical source is the pinned `bbbbf3f…` revision, DOI [10.5281/zenodo.23104842](https://doi.org/10.5281/zenodo.23104842).

## Manuscript and review tools

The manuscript remains close to Johanna's historical human-readable version: the author proof is preserved, and necessary mathematical corrections, comments and amendments remain visible. The selected paper source is P7 commit `760c68d2d79a8fd2c4b58f35f32dd90969591300`; its public formal-repository snapshot is S7 `9f6ca3241edcf88da42a3a000f25514d105e2f30`, and the linked formal source is signed release R131 `f9448d6307fa25aff9d9f94ce0a9c7f9b03e63ff` (654 protected proof/tool files byte-identical to C2; descriptor provenance and package-version exceptions recorded). The refreshed map and PDF asset checks passed on these named inputs. Max’s full correspondence review remains pending as a separate human assessment.

The generator's approval digest now includes its review-scope module, and run-in paragraph headings render correctly. Packaging and rendering fixtures passed in their recorded worktrees. The refreshed review map and manuscript PDFs match the named paper snapshot and formal source; the asset-gate receipt is recorded with the campaign evidence. Human correspondence review remains pending.

## Remaining completion gates

The [current review ledger](docs/paper-lean-audit/review-status.json) records completed formal checks and pending Johanna/Max responsibilities. The owner’s v1.3.0 submission passed mechanical verification; its automated review identified the provenance issue now corrected in v1.3.1. The owner will resubmit R131. Both releases and archive checks are complete; the final paper cites them. All three matching P7 PDFs and the asset gate passed. Confirm the final live deployment, then send the authorized handovers.

The controller owns integration and promotion. Worker worktrees remain available; [the branch map](PLAN.md#branches-for-resuming-saved-work) identifies each pushed candidate and its recovery command. See [the route map](docs/paper-route-alignment.json), [definition owners](docs/definition-owners.md) and [proof-source provenance](docs/proof-source-provenance.md). The earlier [stopped-state archive](docs/audits/stopped-2026-10-02/README.md) retains its source packets and the incoming cleanup provenance annotations. No new mathematical verification is claimed by synchronization.
