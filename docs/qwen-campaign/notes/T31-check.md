# T31 CoordinatePresentation candidate

Status: candidate; the final module build failed. The literal consumer check
was not run because the module did not build.

The source packages the retained finite row indexing, Option-coordinate
algebra maps, row correspondence, chart/axis coordinate identities, and
`GroundPointChartOutput`. The existence theorem takes the accepted T30
`ChartSetup` and the exact `actualSameWitnessGroundPointOutput`; its proof
destructs only the latter and adds no geometric premise. The output carries
the coefficient map, finite-type witness, and prime witness explicitly so
the dependent `GroundPointChartOutput` type does not require local concrete
Algebra instances. `fOption` and `fFin` are explicit `AlgHom`s over that map.

Reused declarations: `actualSelectedNormalizationRows`, `actualOptionMap`
and its generator equations, `GroundPointChartOutput`,
`chartAffineCoordinateEquiv`, and
`actualNormalizedProjectiveColumnInIntegralClosure`. Search found no prior
`CoordinatePresentation` owner in the repository or
`docs/definition-owners.md`.

Source SHA-256: `6a1496bf9fff9751bbd4268e4bb1ddb164466c07f08a4685355df3bf8cb8ca5c`
Consumer SHA-256: `bfa1d18843c80f023f0c615d1a9ec43a3da62d7b90477247e2706a3d7bc0b5e1`

Interface refinement: `CoordinatePresentation` now also retains `hsPB`, the
chosen `s`-in-prime fact required by axis lift, and `hcoeff`, the equality of
its coefficient map with `actualSelectedNormalizationCoefficients P w`.
Both are populated directly from the original witness/output construction.
The consumer still restates `nonempty_coordinatePresentation` literally;
its source hash is unchanged.

Stale-guard diagnostic 1: `lake build Stafford38.Geometry.SameWitness.CoordinatePresentation`
failed in 10 s (`.lake/qwen/logs/T31-local-module-1.log`). This used the stale
worktree guard and is not acceptance evidence. First errors were
missing `Algebra k B` for finite-type data, unresolved coordinate-column names,
and an `IsLocalRing` synthesis failure. The source was repaired with explicit
algebra-valued `FiniteType` data, the owning imports/namespaces, and the
retained valuation local-ring instance.

Stale-guard diagnostic 2: the same module build failed in 10 s
(`.lake/qwen/logs/T31-local-module-2.log`). This also used the stale worktree
guard and is not acceptance evidence. Remaining errors included an extra
explicit `AlgHom` instance argument, `Finite` passed where `Fintype` was
required, and use of the wrong prime-witness name. Those source issues were
repaired after the run; the resulting candidate has the hash above but has
not been checked.

Final guarded attempt 3 used the validated MAIN guard at SHA
`b6eebe8c6d0133f6dffccda31dd1ab14594b7b354908babd57705c6e8daa43d4`:
`lake build Stafford38.Geometry.SameWitness.CoordinatePresentation` failed
in 12 s (`.lake/qwen/logs/T31-local-module-3.log`; GUARD exit=1, peak RSS
2 GiB, 2 threads, 8 GiB cap). The remaining errors are synthesis failures for
`Algebra (RelativeCoefficientDVR.SourceDVR w.column.W.coefficientField)
(ComponentFractionField P)` while elaborating the selected center prime and
ground-point output, and `IsLocalRing w.column.W.place.valuation.toSubring`
in the retained output type. The `fFin` composition also reports missing
`Algebra k B`, and construction of the result reports that `Set κ` has the
wrong universe for the current `t : Type` field. The exact diagnostics are
in the log at lines 8117–8186. No fourth candidate repair was attempted;
the bounded task is handed to Sol. The literal consumer check was not run.

Acceptance checks still pending (through the validated MAIN guard only):

- `lake build Stafford38.Geometry.SameWitness.CoordinatePresentation`
- `lake env lean --trust=0 -M 32000 tests/SameWitness/CoordinatePresentationConsumer.lean`
- Inspect consumer axioms; allowed set is `propext`, `Classical.choice`,
  `Quot.sound`.

The static grep for `letI`/`haveI` followed by Algebra/SMul/Module/
IsScalarTower/FormallyEtale finds none; `compHom` finds none. The source has
local instance binders for the finite row index and retained valuation
`IsLocalRing`; neither changes a scalar action.
