# T44 literal route consumer preparation

The archived `.lake/qwen/archive/literal-route-consumers.patch` passed
`git apply --check` in WT and was applied without a failed hunk. The prepared
adapted patch is retained at
`/Users/ert/proj/stafford38-qwen/.lake/qwen/archive/literal-route-consumers-prepared.patch`.

Adaptation was limited to the two consumer files and their registration in
`scripts/check-consumers.sh`. The closure consumer imports
`Stafford38.Geometry.SameWitness.AffineFibreClosure`; it derives the ground
point output and smooth principal open from the retained witness, then calls
the closure theorem at its new `Stafford38.Geometry.SameWitness` path. Its
consumer statement remains the archived literal affine-conormal conclusion.
The original-prime consumer imports `SameWitness.OriginalPrimeAxis` and routes
its affine conclusion through the new wrapper. Its original-prime and
coordinate-avoidance binders and conclusion are unchanged. The separate
projective endpoint continues to use the existing terminal theorem. Both new
files use the rc3 module header and `maxHeartbeats 1600000`.

The checker registers both files and expects the axiom reports for the new
consumer declarations, the closure theorem, and the original-prime wrapper.
No other checker history was changed.

SHA-256 of prepared inputs:

| File | SHA-256 |
| --- | --- |
| `scripts/check-consumers.sh` | `6d28a4efa30dd9303838f7655ac81f289af479b1e77078b5458f42c2e73b4dfd` |
| `tests/ActualSameWitnessAffineFibreClosureConsumer.lean` | `b9a8dc7ffbbcfdad1a5b8c23fc4572a4502220b01656bae33ded5eb14a93eb96` |
| `tests/ActualSameWitnessOriginalPrimeConsumer.lean` | `a1ec060e16feac6436b79cbfed93a2f544929e95665881ff218f20e53c4cc3f1` |
| `literal-route-consumers-prepared.patch` | `05f462c1545a6b2db05c13150df0d111dd77e16f4977e5c6307487646b49a93c` |

Static checks passed: `bash -n scripts/check-consumers.sh` and
`git diff --check` on the three owned source files. No Lean command has been
run. Consumer acceptance remains pending the T22 controller queue and the
closure/wrapper module checks. The controller reports 25 GiB free RAM, below
the campaign guard's 60 GiB threshold, with foreign model services active;
there is no Lean process to run or interrupt. No build, axiom, or dependency
acceptance is claimed here.
