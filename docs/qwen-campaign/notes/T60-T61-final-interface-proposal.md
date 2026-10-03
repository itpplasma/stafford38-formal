# T60/T61 owner and review-map proposal

This is an unintegrated proposal for the controller. It does not update
`docs/definition-owners.md`, `docs/paper-route-alignment.json`, manuscript
text, proof status, or the candidate map. Do not read it as an acceptance
receipt or as whole-proof correspondence.

## Frozen inputs and limits

- Lean worktree: `/home/ert/proj/stafford38-qwen`, base
  `ab9f76d47d811739a5cfbcab635efe2017953340`; frozen input packet
  `dcc4836c5da914fec83b297a67c79a55189a0689375cdcd2cc8fd56365b35b91`.
  Its recorded patch digest is
  `b5bed3d46f74802593e0028b998e5297a3ef2032888bf2c5d15438540ffbbb8d`.
  A fresh `git diff --binary` of the live worktree, hashed from subprocess
  bytes, is `5a6a342451a417e3e9e3e5f558120b8f57464d28152b6df022ff687de85f8a0d`;
  it is a later shared-worktree state and is not the frozen packet patch.
- Relevant declarations include T32 `CommonOpen.lean` SHA-256
  `8656c5e830bd4326493a866a7272f939aa5dcc0cedd0416a59a755a3fe10fa43`;
  T33 `CommonOpenArc.lean` `527a8716c913d71245d1affebc0780290f11dc1eba827fda682312f2122f140f`;
  T34 `CommonOpenColumns.lean` `e0f73029a8465f774e64ce4006ccf2364b015234c2ccbe5bfa9563f9532ef80d`;
  T35 `CommonOpenEtale.lean` `f30d41e2a4db4463c39925858cc8c3d03ed4d11c8d921149cad11f4635eedc93`;
  T34 positions `CommonOpenPositions.lean`
  `d470f322c3cb123eb269034efdfdcb2dd761bd4d799af82c7cd729aa78d88307`;
  T36 `AffineFibreClosure.lean`
  `f1bd490fe370a955699d132d5f3896397e515f5b32504e68d4e707d326a435a8`.
- Shared route inputs: `GeneralCoisotropicSets.lean`
  `a1b7acad72aead9ddfb6fa7c818a80e3f64ed5a1b4fda1ebf0fe719369e18e4e`;
  `GeneralCoisotropicExclusion.lean`
  `6ed7a44993cdc3a29bd804cd2b41f0642bc99106ab7deccd63a0e8720ccb118a`;
  `GeneralCoisotropicCanonicalAdapter.lean`
  `4dfd046eaf9178cc0f27638df1ce51aa47906c88a049a5c7c5dd78f5f1157c67`;
  `FoundationClosure.lean`
  `c476f050bf7467aaa86d6ea864ab60449531d3ff68e4419a278f45994ae144fc`;
  alternative endpoints `AlternativeSolution.lean`
  `5c04ea38945c3d8b6d13962276475a6535d21bd003e8e39f3b6aba058e260f18`,
  `AlternativeFixedSourceSolution.lean`
  `84cc87243901736558ba2e87c764ef873de94409ca8e116a64dcf1e6b6b5c3e5`,
  and `AlternativeAsymptoticConormal.lean`
  `dbe77240848663aed1351c01df92156cf44dad07acd24ec7e343d581c8ef7971`.
- Selected paper: `human_readable_main.tex` at
  `53882beb19c1491c43867fa78ee3b5bba3f18169` (SHA-256
  `fd707283bda604800400fd86cb31f9e3ab083f29a3fb8e556c230ccd83aaaa3b`).
  The diagnostic map under `/tmp/stafford-map-resolution-luna` is
  stale-pinned; its 55 IDs below are coverage input only, not a final map.

No Lean or verifier was run for this proposal. T35 and guard checks are queued
with the controller. The interfaces below are locator proposals pending those
checks and human review.

## Owner-registry proposal

Add the rows in `T60-T61-final-interface-proposal.patch` only after resolving
them against accepted sources and the existing registry. Public package owners
are distinct data contracts:

- T32 `Geometry.SameWitness.CommonOpenArcFactors` retains the nonvanishing
  factors needed to transport tilted-product avoidance;
  `CommonOpenPointData`, `CommonOpenChartData`, `CommonOpenMapData`,
  `CommonOpenArcCompatibility`, and `CommonOpenData` respectively retain
  the selected point, chart, maps, arc-factor compatibility, and composed
  common-open witness. Producer theorems construct these records; projection
  abbreviations do not create extra owners.
- T33 `Geometry.SameWitness.CommonOpenArcTransport` records the extended
  Laurent arc, restriction/ground-map equations, and nonzero transported
  factors. `CommonOpenArcData` binds this transport to the same retained
  normalization witness. It uses existing generic-open localization and
  Laurent-arc constructions; those maps are not new owners.
- T34 `CommonOpenPositionData` and `CommonOpenColumnsData` keep the
  point-local positions/common-open images, derivative columns, and selected
  numerator identities. They support the endpoint and are not separate
  printed-paper claims.
- T35 `CommonOpenEtaleData` retains the original-chart and selected
  coordinate `k`-algebra maps, their formally-etale properties, and the
  action equality needed to expose the existing algebra structure on the
  common-open localization.
- T36 public endpoint
  `Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput`
  places the coordinate axis in the smooth affine-conormal fibre projection
  closure given the retained ground-point output and smooth principal-open
  witness. Those premises are part of its contract; this is not the
  unconditional theorem for every prime.

Do not register private implementation helpers as public definitions:
`pointLocalArc_unit_of_not_mem`, `exists_commonOpenArcTransport`,
`coordinateMapToOpen`, `formallyEtale_coordinateMapToOpen`, and
`retainedClosureChartData` are source-level support only. Link them as
file/line references and show their private visibility. Likewise
`CoordinateAxisClosureInput` is a proposition/contract, not a new geometric
theorem owner. Avoid duplicating existing owners for generic-open
localization, prescribed power-series charts, tangent-limit inputs, or the
visible-frame witness.

## Paper-order review coverage

Carry forward and re-anchor every diagnostic entry ID in the JSON proposal,
preserving order and one claim per entry. The 55-item base sequence spans the
abstract and Theorem 1.1; global extension, proof sketch and prior art;
formalization scope; Weyl/cotangent/filtration/characteristic definitions;
Gabber and componentwise involutivity; monic reduction and Euler argument;
surjectivity, length/support inequalities and characteristic avoidance;
conormal direction, tangent-limit criterion and Theorem 8.2; fibre-conical
exclusion and Theorem 1.1 proof; cyclicity, outlook/provenance, and appendices.
The exact IDs and two added challenge-comparison rows are in the JSON.

Insert `challenge-main` after `thm:main`: compare unchanged
`Stafford38Challenge.UniversalStatement` to
`Stafford38Challenge.universalStatement` in `Solution.lean` and its
alternative proved entrypoint in `AlternativeSolution.lean`. Insert
`challenge-fixed-source` immediately after: compare unchanged
`Stafford38FixedSourceChallenge.UniversalFixedSourceStatement` to
`FixedSourceSolution.lean` and `AlternativeFixedSourceSolution.lean`
entrypoints. Both variants retain the exact challenge proposition. The
identical exported names are disambiguated by their source module and proof
route. Show routes separately; no comparative proof equivalence is asserted.

For conormal entries, distinguish the printed argument at
`thm:asymptotic-conormal` and its proof (paper lines 1133–1316) from the
formal paper-conforming route: its public endpoint is
`GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure`, which
now delegates to the SameWitness original-prime wrapper and its conditional
ground-point closure construction. The selected paper explicitly marks
complete proof correspondence as open. T32–T36 describe this same-witness
route's inputs and endpoint; they are not line-by-line translations of
Johanna's printed arc proof. The generic/Laurent conormal endpoint is the
separately named alternative route. Corrections marked in the paper remain
proposals with their correction IDs and visible text.

## Verification and boundary

Keep proof receipts, correspondence evidence, and Max's human review status
as separate fields. Every build-site source link should point to a frozen
revision. Current declarations remain candidates until queued checks finish;
successful module/consumer checks establish only their checked statements,
not full paper correspondence or author acceptance.
