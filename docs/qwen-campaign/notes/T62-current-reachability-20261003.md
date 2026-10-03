# T62 current geometry reachability and statement-owner report

## Frozen scope

This is a static source-graph and statement-signature review only. It does not authorize deletion or claim kernel/dependency acceptance. Source checkout is `/home/ert/proj/stafford38-formal`, MAIN `5fd1ffedf2b3e69b5f13be1786aac89040827527`. Tracked worktree patch SHA256 is `85239aac6bc2fa94a2f25f65e6ccb88daf1bfa703f8d92dcf4189798ac371ee4`; the tracked dirty files were the guard core, guard runner and a release-draft note. No Lean source file is untracked. The full Lean-source SHA256 manifest is `T62-current/source-manifest.sha256` (580 entries), SHA256 `4c09893f9390572dc87e07ad3a9090befea00be321acdf6823e6c10778868c1c`; its accompanying module/import inventory is `T62-current/import-inventory.tsv`, SHA256 `6db6c00a6c8e8a0c41f8ee0549d8d29b8947567f97da3ae2f391b7b358d04502`.

The traversal follows local `import` and `public import` edges among the 580 project `.lean` sources. Roots are the five roots prescribed by PLAN T62 (`Stafford38`, `Solution`, `FixedSourceSolution`, `CorollaryChallenge`, `PaperPairChallenge`) and all 131 `tests/**/*.lean` modules, plus `AlternativeSolution` and `AlternativeFixedSourceSolution` as explicitly labeled extra package roots. All 138 roots exist. The graph has 1,169 local import edges and reaches 572 modules. Of 246 `Stafford38/Geometry` sources, 244 are reachable and two have no direct importers:

- `Stafford38.Geometry.PaperLaurentArcTangency` — SHA256 `4ba9e39692b6af8c5aa9b5c24d9c4bc732796ef7e6962cb797ead38541899b98`. This contains generic Laurent tangency results for derivations of a retained power-series arc; it is relevant mathematical material for the preserved alternative route.
- `Stafford38.Geometry.PrescribedCompletionNonzeroConsumer` — SHA256 `c0fcc2624abfa96b399a173ab33fa2470d0b4fd832d46484f5eb6f11d773292a`. This proves a centered coordinate can vanish at the chosen residue point while its completed local chart series is nonzero; it is a concrete completion edge-case consumer.

The previously reported `CommonOpenEvaluation` is now reachable, and `SameWitness/CommonOpenColumns.lean` is present. These facts supersede the old `0340cf2` T62 snapshot, which listed three unreachable files and described the columns source as absent. `scripts/verify.sh` explicitly feeds every `Stafford38/**/*.lean` source to `lake build`; the two unimported modules are therefore retained and compile-covered by that full verifier. This report finds no deletion candidate.

## Similar or repeated statements, reviewed by signature

These are statement-level source comparisons, not claims that the proofs have identical dependencies. The public endpoints and adapter layers remain in place; no deletion is proposed.

1. The original-prime coordinate-axis closure proposition is stated by `Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure` (line 32), `Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure` (`SameWitness/OriginalPrimeAxis.lean:22`), and `Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure` (line 33). The first two are the selected main terminal and its SameWitness route adapter; the third is the explicitly labeled generic/Laurent alternative. Keep all three names and routes distinct. The main terminal remains the public `Solution` endpoint.

2. Several results conclude that the coordinate axis lies in a smooth conormal-fibre closure but have different inputs and roles: `GeneralConstantCoordinateAxis.coordinate_axis_mem_smooth_fibre_closure_of_coordinate_algebraic` handles the algebraic-coordinate branch; `ActualSameWitnessAffineFibreEndpoint.axis_mem_smoothConormalFibreProjection_closure_of_actual_columns` takes the concrete retained-column data; `SameWitness.EndpointOfAlgHoms.axis_mem_smoothConormalFibreProjection_closure_of_algHoms` is its abstract ring-map adapter; `SameWitness.AffineFibreClosure.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput` packages the same-witness data bridge; and `GeneralTangentLimitCriterion.tangent_limit_affine_fibre_closure_of_directSummand` takes direct-summand tangent-limit input. Keep the layer boundaries and registered endpoint owner `ActualSameWitnessAffineFibreEndpoint`; none replaces the others' contract.

3. `AffineConormalSpan.differentialCovector_mul` and `CanonicalVisibleDivisorFrameProduction.differentialCovector_mul` have the same product-rule conclusion. The latter delegates to the former. Keep `AffineConormalSpan` as reusable owner and the latter as compatibility wrapper.

4. `CoisotropicTranslation.eval_affineFibreLinePolynomial` and `PaperHamiltonianFlow.eval_affineFibreLinePolynomial` have the same evaluation identity; the paper-flow declaration delegates to `CoisotropicTranslation`. Keep the former as owner and retain the latter where its manuscript-facing API is used.

5. `AffineConormalSpan.affineConormal_coordinatePoint_isCommonZero` and `PaperHamiltonianFlow.affineConormal_coordinatePoint_isCommonZero` have matching binders and conclusion. Their arguments differ: one uses a finite differential combination; the other constructs finite successive Hamiltonian flows. Keep the algebraic span result as reusable owner and retain the flow proof as a separate paper-route implementation.

The `SameWitness` chart/presentation/common-open/arc/position/étale/column structures store data at successive stages of one retained witness construction. Their fields and construction inputs differ. The `CoordinatePresentation` equalities `hzero` and `haxis` are reflexive in the accepted adapter; possible simplification is only a future tidy-up question, not a correctness or cleanup action.

## Limits and decision

No Lean command was run. Reachability is only a source-import graph, not the declaration-level dependency guard or kernel proof. Signature comparison does not certify theorem correctness or whole-paper correspondence. Preserve the historical receipts, both isolated solution variants, both unchanged challenge files and both unreachable mathematical modules. The full verifier, strict terminal/route dependency guard and four actual Palomar comparisons remain separate acceptance gates.
