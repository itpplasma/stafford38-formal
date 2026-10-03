# T40 import-cycle check

Status: preliminary only; T36 has not yet supplied `Stafford38.Geometry.SameWitness.AffineFibreClosure.lean`, so the required full-root check remains pending.

Source-graph precheck from the T41 wrapper’s other root, `Stafford38.Geometry.OriginalPrimeCoordinateAvoidanceWitness`: 147 Stafford38 modules traversed; none are `GeneralAsymptoticConormal`, `GeneralCoisotropicExclusion`, or `GeneralAsymptoticLaurentAxis`. The exact T40 traversal over both roots reported the closure source missing and `forbidden in existing source closure: []`.

After T36 lands, rerun the prescribed source-import traversal over both roots. Do not mark T40 done unless the closure file exists and the final result is `forbidden in closure: []`. No Lean process was run.
