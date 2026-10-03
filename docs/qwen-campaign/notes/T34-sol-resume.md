# T34 Sol source repair candidate

No Lean run is claimed; controller check slot and exact remote-source sync
are required. `git diff --check` passes for the current source candidate.

## Repair and retained facts

`CommonOpenPositions.lean` now exposes `pointLocalPowerSeriesChart`, a
ring-hom wrapper of the existing `localToFinSuccPowerSeries`. It installs
the coordinate algebra, tower, finite-type and formally-etale certificates
over an abstract ring B. The prior concrete qPre term lacked all four
required instances. Its finite-type certificate is the existing
`coords.hBfinite`, not a new geometric premise.

`CommonOpenPositionData.hqPre` retains equality with this exact prescribed
completion chart and its exact qT column. The producer proves it by rfl.
Previously qPre was an arbitrary field constrained only at the chart entry,
so the downstream universally quantified derivative theorem could not
possibly prove the derivatives of that qPre.

The position bridge now accepts the existing finite-type certificate before
calling `Algebra.EssFiniteType.of_comp`. The concrete producer never installs
scalar actions. It uses the retained canonical arc equalities by rewriting
already elaborated facts, rather than reconstructing an instance-dependent
arc expression on the selected normalization.

`CommonOpenColumns.lean` now has a generic derivative bridge over abstract
B and Q. Its common open is the localization formed from these abstract
rings; only the given psi action is installed, with the existing hpsi
algebra-equality certificate used to transport the legacy raw column facts.
There is no compHom call in either source file. It reuses
`actual_option_columns` and `actual_option_columns_to_laurent`.

The selected numerator proof is a separate lemma. It uses the explicit
retained coefficient map and `eval_map_eq_arc_eval₂` with the corresponding
explicit algebra argument. It does not install another k-action on B.
The actual selected numerator and the public column theorem conclusion
remain unchanged.

## New definition ownership for controller integration

`pointLocalPowerSeriesChart` —
`Stafford38/Geometry/SameWitness/CommonOpenPositions.lean` — the existing
completion chart is an AlgHom requiring four coordinate scalar instances;
no existing ring-hom wrapper retains those instances behind an abstract
B interface. This wrapper exposes exactly the existing homomorphism.

## Frozen candidate and check request

Columns SHA-256:
`e0f73029a8465f774e64ce4006ccf2364b015234c2ccbe5bfa9563f9532ef80d`.
Positions SHA-256:
`d470f322c3cb123eb269034efdfdcb2dd761bd4d799af82c7cd729aa78d88307`.
Consumers remain unchanged and literally apply the public theorem statements.

Check positions, columns, then their two literal consumers after the T31,
T32, T33 and T35 source prerequisites pass. The exact first risky bridge is
`rw [hpsi] at hcols`: the legacy conclusion uses an Algebra.compHom action,
whereas hpsi states equality of the explicit composite ring-hom actions.
If the actions do not reduce definitionally in the guarded check, normalize
the legacy action over abstract B/Q before transporting it; never install
another concrete action or raise limits.
