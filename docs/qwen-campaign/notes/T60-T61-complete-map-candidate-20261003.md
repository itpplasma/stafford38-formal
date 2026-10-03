# T60–T61 complete map candidate (2026-10-03)

Candidate artifacts are under `/tmp/stafford-final-map-luna/`: `candidate-map.json` (the current 55-card map plus two challenge-comparison cards), `docs/paper-route-alignment.json` (the proposed SameWitness declaration locators), `definition-owners.patch` (review-only owner additions), and `source-hashes.txt`. Nothing here edits the authoritative map, registry, paper, or state. No Lean or verifier was run.

## Pins and scope

- Selected paper: `itpplasma/stafford38-paper`, current candidate `daf43041f8363f39f35b3c894e6a7e3cd72cd3cc`, `human_readable_main.tex` SHA-256 `c792f4b651740c3fe94ddbb8ebf8ee7c552637dd52b06746c0b79ec3e2057485`. The locator-only edits are present in this candidate input; controller acceptance/final proof-source freeze is pending. Current line anchors below refer to these bytes.
- Formal source: shared WT base `1a3fcfd7028df83b86cbd9da9e608ca98c03385c`; the WT has uncommitted changes. Final formal commit and complete patch digest remain pending the controller’s freeze. Individual current source hashes are in `source-hashes.txt`.
- The candidate JSON retains all 55 stable IDs and inserts `challenge-main` and `challenge-fixed-source` immediately after `thm:main` (57 unique IDs). SameWitness row/compiler validation and final formal pins remain pending. The paper’s original proof remains visible; the map does not claim proof correspondence or whole-paper coverage.

## T60 definition-owner proposal

`definition-owners.patch` adds four SameWitness owners after checking the current registry for an existing owner of the combined retained contracts: `ChartSetup` (smooth principal open, chart, away data, numerator), `CoordinatePresentation` (finite option-coordinate map and selected rows tied to the retained ground-point output), `CommonOpenArcData` (common-open data with the same-witness point-local arc and transport identities), and `CommonOpenEtaleData` (the two common-open k-algebra maps with formally-etale certificates). These packages combine existing components; they do not replace owners for normalization/localization maps, prescribed charts, or visible-frame witnesses. T32/T33/T35 producer/helper wrappers are not additional owners. The existing `new-definitions.md` lists `ChartSetup` alone while the prior interface proposal and patch name these four newly retained contracts; this ledger discrepancy is flagged for controller resolution. The patch is a candidate for controller review, not registry acceptance.

## Challenge comparison cards

Both cards point to the Theorem 1.1 discussion (current manuscript lines 102–114), compare the unchanged challenge proposition with the primary and alternative proof entrypoints, and keep routes distinct. Main: `Stafford38Challenge.UniversalStatement` (`Stafford38/ChallengeDefinitions.lean:78`), proved by `Solution.lean:12` via `Stafford38.universalStatement` and by `AlternativeSolution.lean:17` via `Stafford38.GenericLaurentVariant.universalStatement`. Fixed-source: `Stafford38FixedSourceChallenge.UniversalFixedSourceStatement` (`Stafford38/ChallengeDefinitions.lean:193`), proved by `FixedSourceSolution.lean:24` via `Stafford38.universalFixedSourceStatement` and `AlternativeFixedSourceSolution.lean:20` via `Stafford38.GenericLaurentVariant.universalFixedSourceStatement`. The same declaration spelling in the solution files is resolved by file/module. No proof-route equivalence is asserted; final `#check` validation remains pending.

## SameWitness declaration locators

Paper anchors are the current selected manuscript: local point/chart setup at lines 1147–1189; tilt and divisor orders at 1192–1217; coordinate rows, arc columns, and tangent-lattice calculation at 1219–1293; Theorem 8.2 statement at 1133–1144. A “no direct counterpart” label means technical formal plumbing, not an omission to be hidden. The endpoint is conditional on retained ground-point output and a smooth-open witness; the original-prime wrapper and unconditional theorem remain distinct. All entries below are candidate locators, pending final source freeze/compiler checks.

| Lean declaration | Current source line | Paper location / relation |
| --- | --- | --- |
| `Stafford38.Geometry.SameWitness.factorization_to_atPrime` | `Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean:17` | No direct paper counterpart; nearest use is the local order-factorization discussion at lines 1164-1166. |
| `Stafford38.Geometry.SameWitness.pair_factorizations_to_atPrime` | `Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean:49` | No direct paper counterpart; nearest passage is lines 1214-1217, where the two selected coordinates are written as powers times units. |
| `Stafford38.Geometry.SameWitness.exists_axis_lift_of_groundPointChartOutput` | `Stafford38/Geometry/SameWitness/AxisLiftFromGroundPoint.lean:26` | Lines 1192-1217: choose the tilted formal axis and record the selected coordinate orders. |
| `Stafford38.Geometry.SameWitness.originalAffineChartToCommonOpen_groundMap` | `Stafford38/Geometry/SameWitness/ChartGroundMap.lean:28` | No direct paper counterpart; the manuscript uses affine chart coordinates near lines 1157-1166 without stating this ring-map identity. |
| `Stafford38.Geometry.SameWitness.nonempty_chartSetup` | `Stafford38/Geometry/SameWitness/ChartSetup.lean:68` | Lines 1147-1166: normalization, choice of a nonzero projective chart, and the two order factorizations. |
| `Stafford38.Geometry.SameWitness.nonempty_coordinatePresentation` | `Stafford38/Geometry/SameWitness/CoordinatePresentation.lean:130` | Lines 1177-1189 and 1228-1236: choose the closed point, local parameters, and tangential coordinate rows. |
| `Stafford38.Geometry.SameWitness.exists_selected_chart_coordinate_data` | `Stafford38/Geometry/SameWitness/CommonOpen.lean:492` | Lines 1157-1163: choose a nonzero projective chart and write its affine coordinates and divisor orders. |
| `Stafford38.Geometry.SameWitness.exists_common_open_map_data` | `Stafford38/Geometry/SameWitness/CommonOpen.lean:520` | No direct paper counterpart for the localization maps; the closest coordinate use is the chart parametrization at lines 1219-1222. |
| `Stafford38.Geometry.SameWitness.nonempty_commonOpenData` | `Stafford38/Geometry/SameWitness/CommonOpen.lean:691` | Lines 1164-1189 and 1214-1217: local divisor parameter, selected closed point, local coordinates, and unit factors. |
| `Stafford38.Geometry.SameWitness.exists_commonOpenArcData` | `Stafford38/Geometry/SameWitness/CommonOpenArc.lean:260` | Lines 1201-1217: choose the tilt, obtain the formal arc, and retain the selected coordinate orders. |
| `private CommonOpenEtale.originalChartToCommonOpen_groundMap_k` | `Stafford38/Geometry/SameWitness/CommonOpenEtale.lean:98` | No direct paper counterpart; this is a formal ring-map compatibility step. |
| `Stafford38.Geometry.SameWitness.nonempty_commonOpenEtaleData` | `Stafford38/Geometry/SameWitness/CommonOpenEtale.lean:150` | Lines 1182-1189: identify the completed local ring with a power-series ring and choose formal coordinates. |
| `private CommonOpenPositions.commonOpen_position_of_pointColumns` | `Stafford38/Geometry/SameWitness/CommonOpenPositions.lean:56` | Lines 1219-1225 and 1232-1245: write the projective-coordinate columns and correct the transverse entries along the tilted arc. |
| `Stafford38.Geometry.SameWitness.commonOpenPositionData_of_arc` | `Stafford38/Geometry/SameWitness/CommonOpenPositions.lean:171` | Lines 1219-1245: projective-coordinate columns and the tilted transverse-row correction. |
| `Stafford38.Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_algHoms` | `Stafford38/Geometry/SameWitness/EndpointOfAlgHoms.lean:27` | Closest statement is Lemma tangent-limit, lines 1068-1085; its proof's tangent-space conclusion appears at lines 1270-1293. |
| `Stafford38.Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput` | `Stafford38/Geometry/SameWitness/AffineFibreClosure.lean:63` | The target matches the conormal-direction limit in Lemma tangent-limit, lines 1068-1085, and the visible construction at lines 1192-1293. |
| `Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure` | `Stafford38/Geometry/SameWitness/OriginalPrimeAxis.lean:22` | Statement of Theorem asymptotic-conormal, lines 1133-1144. |

### Exact T36 endpoint contract

```lean
theorem axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hpoint : actualSameWitnessGroundPointOutput hm P w)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal))
```

The only hypotheses beyond the field and prime/witness data are exactly `hpoint` and `hsmoothOpen`; they remain in the theorem statement. Its body retains `ChartSetup`, `CoordinatePresentation`, `CommonOpenData`, `CommonOpenArcData`, `CommonOpenEtaleData`, `CommonOpenPositionData`, and `CommonOpenColumnsData`, then calls `axis_mem_smoothConormalFibreProjection_closure_of_algHoms`. Supporting statements and definitions are source-linked in the JSON `same_witness_declaration_map_candidate.rows`; each row also carries its exact declaration header (`lean_signature`). The endpoint is a technical analogue to the visible tangent-limit construction (lines 1068–1085 and 1192–1293), not a line-by-line proof map. The terminal original-prime theorem is `coordinate_axis_mem_smooth_fibre_closure` at `OriginalPrimeAxis.lean:22`; its manuscript statement counterpart is Theorem 8.2, lines 1133–1144. The alternative generic/Laurent endpoint remains separately labeled in the existing map.

Private helpers stay source-only and are not definition owners: `pointLocalArc_unit_of_not_mem` and `exists_commonOpenArcTransport` (`CommonOpenArc.lean:71,88`); `coordinateMapToOpen` and `formallyEtale_coordinateMapToOpen` (`CommonOpenEtale.lean:26,36`); `originalChartToCommonOpen_groundMap_k` (`CommonOpenEtale.lean:98`); `commonOpen_position_of_pointColumns` (`CommonOpenPositions.lean:56`); and `retainedClosureChartData` (`AffineFibreClosure.lean:28`). They are not paper claims.

## Source-owner correction and remaining gates

The map’s canonical right-torsion predicate owner is `Stafford38.TorsionCyclicity.IsRightTorsion` in namespace `Stafford38.TorsionCyclicity`, defined in `Stafford38/ChallengeDefinitions.lean:203`. Any stale map locator to `Stafford38/TorsionCyclicity.lean:18` is corrected in the scratch candidate; that module is a compatibility import/re-export. No declaration named `CanonicalIsRightTorsion` is present in the current WT.

Unresolved before acceptance: final formal/paper source pins, compiler-checked exact declaration names for every map item, controller review of the owner additions, and human assessment of correspondence. The conditional same-witness endpoint must not be presented as proving its own ground-point/smooth-open inputs; the direct conormal proof correspondence remains open.
