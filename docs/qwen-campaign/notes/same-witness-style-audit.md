# SameWitness style and ownership audit

Read-only audit of `WT/Stafford38/Geometry/SameWitness/*.lean` against
PLAN.md sections 2.6, 2.5 and 6. The snapshot is WT base
`03c6915930e2c3d9370d6fb9720ef07a5c0779d4`; the whole-worktree patch SHA-256
was `6c9362f08f3c4003d57348844112145b49caae1b6f921afbb1a6a3305e7a1150`.
At capture, the patch included four modified SameWitness modules and an
unrelated concurrent edit to `scripts/build-review-site.py`. The canonical
SameWitness file hash list below has aggregate SHA-256
`4c1f8fe45064345fd347cba38cc772f2098fa0fcab16d24783b1c418ecb4d8a7`.

## Findings

- Two theorem proof bodies exceed the PLAN's approximate 60-line split
  threshold: `nonempty_commonOpenData` in `CommonOpen.lean` (69 lines from
  `:= by` to the next declaration) and `nonempty_coordinatePresentation` in
  `CoordinatePresentation.lean` (64 lines). These are the concrete readability
  violations. Other detected top-level proofs are at or below 60 lines.
- All top-level theorem declarations have mathematical docstrings. Structures
  and task-owned data packages are also documented. The short projections
  `CommonOpenData.g`, `.Cq`, `.U`, `.qU`, `.qT`, and `.φ` do not each have
  separate docstrings; PLAN 2.6 requires docstrings for theorems, so this is
  not a violation.
- `CoordinatePresentation.coeff` duplicates the canonical function
  `actualSelectedNormalizationCoefficients P w`, and `hcoeff` records that
  equality. PLAN 6.2 says objects already functions of `P,w` should be used
  directly instead of copied into a step structure. These fields are used by
  downstream T32–T35 candidates, so changing them would require coordinated
  consumer updates; document as a real ownership/style exception or remove
  them with those updates. `fFin`, by contrast, depends on the chosen row
  equivalence and retained `fOption`, and is used downstream.
- No second owner for `ChartSetup`, `CoordinatePresentation`,
  `CommonOpenData`, `CommonOpenArcData`, `CommonOpenEtaleData`,
  `CommonOpenPositionData`, or `CommonOpenColumnsData` was found in the
  repository owner inventory or by declaration search. The `CommonOpenData`
  projections for `g`, rings, and coordinate maps are derived definitions,
  not duplicated structure fields. Chosen witnesses such as chart setup,
  rows, point, arc, and maps are retained in their step package as intended.
- Concrete proof bodies contain no new Algebra/SMul/Module/scalar-tower/
  FormallyEtale instance installation. Local binders in `CoordinatePresentation`
  preserve `w.ambientAlgebra` and the valuation local-ring instance while
  unfolding the exact ground-point output. The `letI` binders in
  `EndpointOfAlgHoms`, `AxisLiftFromGroundPoint`, `CommonOpenPositions`, and
  `CommonOpenColumns` occur in adapters over abstract ring variables or in
  retained dependent field types; they do not install competing actions on
  the concrete common-open ring. `ChartGroundMap` contains two
  `Algebra.compHom` binders for `Q → U`; this is the explicit T13
  ground-map task exception, and should not be copied into later concrete
  proofs. No other `compHom` occurrence was found.
- Every SameWitness file sets `maxHeartbeats` to `1,600,000` or lower. No
  limit increase was found; the special T13 limit exception is not needed.

The audit was static and ran no Lean commands. It does not alter any Lean
source or promotion status.

## Frozen SameWitness source hashes

```text
a867ef9abd0f7a970dc0b5e18eb5fef15c30d8ab381b0ba03e7752679e082e17  Stafford38/Geometry/SameWitness/AffineFibreClosure.lean
95263b7f01c0139900c0b53742c2cc5d44f4892dd9fec88332c66dcbcc8a23fd  Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean
f691c640061933ac4938bca2b9ee354a8936f3759edd93b9c09e6f385e003727  Stafford38/Geometry/SameWitness/AxisLiftFromGroundPoint.lean
72295254fb508f4381b4f56b3d0de79fbe4cd096b0579f8f1bbd612cb9cad2fa  Stafford38/Geometry/SameWitness/ChartGroundMap.lean
a8107782808a6839e9dcddf85e0b364cca92675a84d442220d4b68287a85323a  Stafford38/Geometry/SameWitness/ChartSetup.lean
e11081bfe3d6031ece39445ca51756a23dd87646a0b2a1394d1be90d55ac6d4f  Stafford38/Geometry/SameWitness/CommonOpen.lean
2533f9acaef04f978fc73b2f542f31b24b86d4bbb7d2db591c790ae33dcad98e  Stafford38/Geometry/SameWitness/CommonOpenArc.lean
e0f73029a8465f774e64ce4006ccf2364b015234c2ccbe5bfa9563f9532ef80d  Stafford38/Geometry/SameWitness/CommonOpenColumns.lean
604f82d5da0e13f9eb86b4a316911f92941e94d57b309abbe0c12b8a6ff336a9  Stafford38/Geometry/SameWitness/CommonOpenEtale.lean
d470f322c3cb123eb269034efdfdcb2dd761bd4d799af82c7cd729aa78d88307  Stafford38/Geometry/SameWitness/CommonOpenPositions.lean
0c9137eace6de450ab6c0aaa1957f257c58cb1033bdb19576830b2ef9a900bb2  Stafford38/Geometry/SameWitness/CoordinatePresentation.lean
690f8008bee2e7105d208306c91208f46c60d5e32de6040a9cfcda879d91a720  Stafford38/Geometry/SameWitness/EndpointOfAlgHoms.lean
b117060a59dc58e5aac5b59ece0974127354c3ceadaab63cbd8293a76b89b695  Stafford38/Geometry/SameWitness/OriginalPrimeAxis.lean
```
