# T43 source-level terminal route audit

Status: read-only textual audit only. No Lean executable or dependency checker
was invoked. This note does not establish declaration-level dependency
acceptance; only the strict guard can do that.

## Guard contract

`DependencyClosureCore.lean` checks four terminal roots:
`Stafford38.universalStatement`, `Stafford38Challenge.universalStatement`,
`Stafford38.universalFixedSourceStatement`, and
`Stafford38FixedSourceChallenge.universalFixedSourceStatement`. It rejects
references to the owner module `Stafford38.Geometry.GeneralAsymptoticLaurentAxis`
and these exact declarations:

- `Stafford38.Geometry.GeneralConormalAxis.exists_groundConormalAxis_of_minimalPrime_unit_transcendental`
- `Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof.exists_groundConormalAxis_of_regularizedOneRowConormalData`
- `Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction.exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame`
- `Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof.finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData`
- `Stafford38.Geometry.FiniteGradientResidueExtension.exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver`

The checker expands opaque body owners and fails closed if a needed body is
unavailable. Import reachability by itself is not its criterion.

## Source trace

The rewired terminal theorem calls `SameWitness.coordinate_axis_mem_smooth_fibre_closure`.
That wrapper calls `OriginalPrimeCoordinateAvoidanceWitness.coordinate_axis_or_visible_frame_of_avoidance` and closes the two branches:

1. The algebraic-coordinate branch calls
   `GeneralConstantCoordinateAxis.coordinate_axis_mem_smooth_fibre_closure_of_coordinate_algebraic`.
   Its visible source body derives an affine conormal point and applies
   `fibreLift_mem_vanishingIdeal_equationConormal`; no exact banned declaration
   is named in this proof path.
2. The transcendental branch calls
   `exists_inverse_and_visible_frame_of_coordinate_avoidance`, which obtains
   an inverse and calls
   `GeneralDivisorialVisibleFrame.generalDivisorialVisibleFrameWithResidueAlgebraicity`.
   The visible producer body begins from `LaneC.divisorialVisibleFrameExistence`
   and constructs the retained witness. No exact banned declaration is named
   in these visible source bodies.

A repository search finds all five exact banned names in their legacy
production files, but finds no such name in the source bodies above, in the
T36 closure source, or in the T41 wrapper. The name
`generalDivisorialVisibleFrameWithResidueAlgebraicity` is not among the guard's
banned names. Source inspection therefore exposes no exact banned-declaration
path in the new same-witness route.

`GeneralAsymptoticConormal.lean` still publicly imports
`GeneralAsymptoticLaurentAxis.lean`, as it did for other declarations in that
module. The rewired theorem body itself calls the T41 wrapper. This import is
not proof that the terminal theorem depends on declarations owned by the old
module, but it remains a visible source-level risk for the guard's exact
owner-module check. The actual declaration closure is the decisive result.

## First bridge / action

No concrete banned-name bridge was found to repair textually. Do not edit the
new route based on import reachability alone. The controller should run the
strict production guard through the approved Lean guard after T36 and terminal
builds. If it reports a hit, retain its first complete path:

- If the path ends at `GeneralAsymptoticLaurentAxis`, first inspect whether the
  path begins in the rewired terminal declaration or in the separate projective
  endpoint; remove only the now-unused import if the dependency is import-only,
  then rerun the exact guard.
- If it ends at one of the five banned names through
  `coordinate_axis_or_visible_frame_of_avoidance`, the first actionable source
  ownership boundary is the split theorem in
  `OriginalPrimeCoordinateAvoidanceWitness.lean`. Replace/relocate only that
  proof path after Sol confirms the exact dependency edge; preserve the
  statement and direct algebraic branch. Do not weaken T41 or bypass the guard.
- If the path starts in another terminal declaration, report that root and
  path separately; changing the coordinate-axis route would not resolve it.

The prior controller report says the guarded fixture rerun passed in 18 s at
595 MiB. This audit does not repeat that run or claim production-guard success.
