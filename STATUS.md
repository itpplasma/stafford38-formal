# Current status

Updated 2 October 2026. Work is paused at the owner's request. All owned workers and compiler jobs are stopped. Completed migration and review-tool changes are saved; unverified geometry candidates, failed diagnostics and interrupted work are preserved in [the checkpoint archive](docs/audits/paused-2026-10-02/README.md). The final paper-aligned release and review handover remain open.

## Proof and correspondence

The repository has a verified proof of the unchanged main Stafford 3.8 challenge and its documented corollaries at named historical checkpoints. The existing terminal proof still uses the earlier generic-divisor/Laurent geometry route. Full correspondence with Johanna's preserved geometric argument remains unproved.

The paper-compatible route has checked components for the selected normalization chart, same-witness ground point and étale coordinates, common-open arc compatibility, coordinate-column transport, corrected tangent columns, tangent rank and tangent-limit endpoint. Conditional adapters establish their conclusions under their stated inputs; unconditional assembly remains open.

The current mathematical blocker is scalar-action and ground-field tower coherence in the same-witness affine-fibre closure. Repair3 failed during scalar-action inference; repair4, the original-prime wrapper and their literal consumers remain unverified. The combined rc3 candidate was deliberately interrupted, exit 143. A bounded scalar-tower diagnostic also failed; its errorful axiom output is not proof evidence. These candidates remain archived outside the active Lean source surface.

On resumption, finish the construction for one actual witness, derive the affine conormal-closure conclusion from the original prime-variety hypotheses, and make that route carry the terminal theorem. Then run a fresh dependency audit. The strict guard and its fixtures are prepared; wiring that depends on the unverified closure and wrapper is archived for resumption. Full Linux verification, current Palomar qualification and final review packaging are further pending gates and may expose additional issues.

## Toolchain and completed checks

The saved source targets Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163`.

The isolated baseline completed 425 explicit targets, comprising 4,455 Lake jobs, at base `eed5291e072d7af8f9a48a242e498325d9c5e2c1` and patch SHA-256 `e7a467c3622d3782ead45b91a89fc3bfc573f9c7d6de28a49662c420f16be361`. All 116 independent consumers and 312 axiom reports subsequently passed at patch SHA-256 `315f910ee3acedc91f2d95b76813e3b67a4d59cebfb489a2abeed73532a754ae`. Three retained proof wrappers passed independent `--trust=0` compilation. The controller checked the integrated source hashes against the frozen migration and compatibility manifests. The separately authorized Euler-owner cleanup at `2e27340` was preserved from upstream; its focused Lean 4.33 trust-zero receipt is historical, and the combined rc3 source after that cleanup has not been replayed. Source identity checks are integrity checks, not proof tests.

The local source-policy preflight passes 547 Lean files and both pinned configurations. Genuine Linux comparator fixtures accepted matching statements and rejected altered statements and rogue axioms. These results cover the recorded fixtures. The actual Stafford Linux replay, full combined verifier, fresh terminal dependency audit and official current Palomar reports remain pending.

Historical Lean 4.33 checkpoints passed 9,168 build jobs and 301 consumer/axiom reports, and later 9,181 build jobs. The latter full verifier stopped at its 900-second limit during serial consumers. Historical receipts retain their original source and configuration scope.

AlgebraicAnalysis v0.3.3 is separately released on rc3. Its archived mathematical source is the pinned `bbbbf3f…` revision, DOI [10.5281/zenodo.23104842](https://doi.org/10.5281/zenodo.23104842).

## Manuscript and review tools

The manuscript remains close to Johanna's historical human-readable version: the author proof is preserved, and necessary mathematical corrections, comments and amendments remain visible. The user-authorized cleanup is synchronized to GitHub and Overleaf at `ce09ead2553154c3521e0515c5e3db7a505832e0`. Relative to its frozen baseline, only eleven complete technical comparison boxes were removed from the main manuscript and moved to the companion; all 28 retained boxes are byte-identical. Max's final whole-paper correspondence package still requires exact final source pins, refreshed anchors and matching PDF receipts.

The generator's approval digest now includes its review-scope module, and run-in paragraph headings render correctly. Packaging and rendering fixtures passed in their recorded worktrees. The current review map and supplementary assets are historical; the archived candidate map and anchor dry run are preparation only.

## Remaining completion gates

Finish the unconditional paper route and terminal wiring; replay the combined source on rc3; qualify the actual Linux package with the current Palomar tools; regenerate the complete source-linked review bundle; update version citations; and publish a new signed release with a verified Zenodo archive. No new formal or supplementary release, tag or DOI was created by this checkpoint.

The controller owns integration and promotion. Worker worktrees remain available for resumption with no live jobs. See [the route map](docs/paper-route-alignment.json), [definition owners](docs/definition-owners.md) and [proof-source provenance](docs/proof-source-provenance.md). The earlier [stopped-state archive](docs/audits/stopped-2026-10-02/README.md) retains its source packets and the incoming cleanup provenance annotations. The new archive records the later completed and interrupted results.
