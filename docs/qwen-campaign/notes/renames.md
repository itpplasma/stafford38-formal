# Renames and reused declarations

Old archived name → new name in `WT` on `qwen/paper-route`. Only names that
rule 2.6 forbids, or that the namespace change forces, are listed.

## T11 — AwayFactorToAtPrime

Archived `Stafford38/Geometry/AwayFactorToAtPrime.lean` →
`Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean`.

| Archived | New |
| --- | --- |
| `Stafford38.Geometry.AwayFactorToAtPrime.factorization_to_atPrime` | `Stafford38.Geometry.SameWitness.factorization_to_atPrime` |
| `Stafford38.Geometry.AwayFactorToAtPrime.pair_factorizations_to_atPrime` | `Stafford38.Geometry.SameWitness.pair_factorizations_to_atPrime` |

Declaration names unchanged (rule 2.6 clean); only the namespace follows the
new path. Statements are byte-identical to the archived text (`diff` of the
`theorem` signature blocks, exit 0).

Later phases import `Stafford38.Geometry.SameWitness.AwayFactorToAtPrime`
wherever the archived files said `Stafford38.Geometry.AwayFactorToAtPrime`.

Reused from Mathlib (no port needed for these):

- `IsLocalization.Away.lift` — the induced hom `Localization.Away f →+* P`.
- `IsLocalization.Away.lift_comp` — replaces the archived hand-written
  `ext b; simp [ψ]` proof that `ψ.comp (algebraMap B _) = algebraMap B _`.
  Lean needs `R`/`S`/`P`/`x` given explicitly, otherwise the
  `IsLocalization.Away ?m ?m` instance problem is stuck.
- `IsLocalization.map_units`, `IsUnit.map`, `map_mul`, `map_pow`.

No new `def`/`structure`/`abbrev`, so no `new-definitions.md` entry.

## T12 — AxisLiftFromGroundPoint

Archived `Stafford38/Geometry/GroundPointAxisLiftFromOutput.lean` →
`Stafford38/Geometry/SameWitness/AxisLiftFromGroundPoint.lean`.

| Archived | New |
| --- | --- |
| `Stafford38.Geometry.GroundPointAxisLiftFromOutput.exists_axis_lift_of_groundPointChartOutput` | `Stafford38.Geometry.SameWitness.exists_axis_lift_of_groundPointChartOutput` |
| `...Consumer.<same name>` (in `tests/SameWitness/AxisLiftFromGroundPointConsumer.lean`) | `Stafford38.Geometry.SameWitness.AxisLiftFromGroundPointConsumer.exists_axis_lift_of_groundPointChartOutput_consumer` |

Declaration name of the ported theorem unchanged (rule 2.6 clean); only the
namespace follows the new path. Docstring and full theorem signature are
byte-identical to the archived text (`diff` of the docstring+statement blocks,
exit 0; see `notes/T12-check.log`). Import of the T11 module becomes
`Stafford38.Geometry.SameWitness.AwayFactorToAtPrime`.

Reused from the repository (nothing re-proved):

- `Stafford38.Geometry.ActualPointAxisLift.exists_actual_point_axis_lift` —
  the tilted-axis certificate, applied with the transported data.
- `Stafford38.Geometry.SameWitness.pair_factorizations_to_atPrime` (T11) —
  moves both divisor-order factorizations from the away open to `AtPrime M`.
- `Stafford38.Geometry.ActualOptionGroundPointCompletion.GroundPointChartOutput`
  — input abbrev, unfolded only at the hypothesis `hOutput`.
- `Stafford38.Geometry.PrescribedGroundPointUnitPowerChart.localToFinSuccPowerSeries`,
  `Stafford38.Geometry.PrescribedAffineResidueCompletion.residueCoordinates`.
- Mathlib `MvPolynomial.renameEquiv`, `MvPolynomial.rename_X`,
  `RingHom.algebraMap_toAlgebra`.

No Mathlib or AlgebraicAnalysis counterpart exists (grep for `tiltedArc`,
`axis_lift`, `AxisLift`: 0 hits in both package trees).
No new `def`/`structure`/`abbrev`, so no `new-definitions.md` entry.

## T13 — ChartGroundMap

Archived `Stafford38/Geometry/A0ChartFormalEtale.lean` lines 280-328
(repair4 addition only) → `Stafford38/Geometry/SameWitness/ChartGroundMap.lean`.

| Archived | New |
| --- | --- |
| `Stafford38.Geometry.A0ChartFormalEtale.originalAffineChartToCommonOpen_groundMap` | `Stafford38.Geometry.SameWitness.originalAffineChartToCommonOpen_groundMap` |
| (consumer of the archived helper in the repair3 audit) | `Stafford38.Geometry.SameWitness.ChartGroundMapConsumer.originalAffineChartToCommonOpen_groundMap_consumer` |

Declaration name unchanged (rule 2.6 clean); only the namespace follows the new
path, so `$WT/Stafford38/Geometry/A0ChartFormalEtale.lean` stays untouched.
The theorem signature is byte-identical to the archived text
(`diff` vs `SCR/T13-statement.lean`, exit 0); the docstring was rewritten to
say what the lemma proves and drops the word "canonical".

Later phases import `Stafford38.Geometry.SameWitness.ChartGroundMap` and use
the equation
`(originalAffineChartToCommonOpen …).comp (algebraMap k _) = algebraMap k _`
instead of installing a second `Algebra` on the common open (rule 6.2.2).
