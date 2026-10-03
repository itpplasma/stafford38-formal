# T31 Linux resume review

Base WT commit: `c3dccd4b3f931d15df623229771126f6500fb6ea`.

Current candidate hashes:

- `Stafford38/Geometry/SameWitness/CoordinatePresentation.lean`: `6a1496bf9fff9751bbd4268e4bb1ddb164466c07f08a4685355df3bf8cb8ca5c`
- `tests/SameWitness/CoordinatePresentationConsumer.lean`: `bfa1d18843c80f023f0c615d1a9ec43a3da62d7b90477247e2706a3d7bc0b5e1`

The prior final guarded attempt, recorded in `T31-check.md`, failed at
instance synthesis for `Algebra (RelativeCoefficientDVR.SourceDVR
w.column.W.coefficientField) (ComponentFractionField P)` and the retained
valuation-ring `IsLocalRing`, followed by dependent elaboration failures. The
original log is not present in this Linux checkout, so those diagnostics are
available only through the saved report. No Linux acceptance check has been
run yet; await the controller's guarded slot grant.

Static interface review of T32 confirms it defines `qB` directly as
`actualNormalizedProjectiveColumnInIntegralClosure` and supplies `rfl` for
the two axis equations. Thus T31 does not need a `qB` field; its reflexive
`hzero`/`haxis` fields are redundant but do not block that consumer. T34 and
T35 depend on `coeff`, `fFin`, `hcoeff`, and `t`/`htFinite`; these names are
preserved.

## Escalation packet

The bounded T31 assessment did not attempt source repairs. The exact first
reported failure in guarded attempt 3 was synthesis of
`Algebra (RelativeCoefficientDVR.SourceDVR w.column.W.coefficientField)
(ComponentFractionField P)` while elaborating the selected center prime and
ground-point output. Other reported errors were missing
`IsLocalRing w.column.W.place.valuation.toSubring`, `Algebra k B` for `fFin`,
and a `Set κ` universe mismatch for `t : Type`. These interact with dependent
instance binders in `actualSameWitnessGroundPointOutput`. See
`T31-check.md` for hashes and the guard receipt. No source hash changed.
