# T36–T44 resume assessment

Assessment only. The fixture behavior command below invoked the installed Lean compiler indirectly and was run without the campaign guard; its PASS is diagnostic only and does not satisfy T43 acceptance. The frozen WT checkout is
`/home/ert/proj/stafford38-qwen` at `c3dccd4b3f931d15df623229771126f6500fb6ea`.
Its starting worktree was clean. T36–T44 proof and consumer candidates are
present at that commit. No task status or release metadata was changed here.

## Source graph and guard fixture

The required T40 source traversal over `SameWitness.AffineFibreClosure` and
`OriginalPrimeCoordinateAvoidanceWitness` visits 270 Stafford38 modules and
reports `forbidden in closure: []`. Both root source files exist. This rules
out the import cycle at source level; T40 acceptance should still be tied to
controller review of this exact checkout.

Ran `python3 tests/dependency-guard-fixtures/test_behavior.py` directly, without `GUARD`, as a diagnostic behavioral oracle for T43. The test calls its `compile_module`/core path through the installed Lean executable. The command exited 0; tool wait intervals totaled about 10.6 seconds (initial 1.0-second yield, then 5.0 and 4.6 seconds). Its final line was:

`PASS: safe closure accepted; transitive opaque/private producer rejected after owner expansion; unapproved axiom fails closed; Solution roots reject the exact banned route; Challenge placeholder roots reject sorryAx`

This unguarded Lean-invoking run cannot count toward campaign acceptance. Both the fixture behavior check and strict production Lean guard remain pending controller reruns through the approved Linux guard against the final integrated roots.

## T36–T42 source assessment

The T36 theorem signature in `SameWitness/AffineFibreClosure.lean` is the
frozen PLAN.md statement; SHA-256 of its extracted signature is
`95342df3df1a3b2437855f89a6b3f536e7fd6913234cf2f42939476b476f5457`.
Its proof obtains chart setup from `hsmoothOpen`, coordinate presentation from
`hpoint`, the common open from that same output, then the arc, étale data,
positions and columns. It passes the resulting maps, endpoint identities and
setup numerator data directly to the T22 endpoint. The consumer introduces
neither `hpoint` nor `hsmoothOpen`; it supplies each from the existing
completion and smooth-open theorems. Static scans of the T36 proof found no
local `Algebra`/`SMul`/`Module`/`IsScalarTower`/`FormallyEtale` instances and
no `compHom`. This is a source-level assessment only; no bridge is accepted
until its Lean build and consumer/axiom check pass.

The original-prime wrapper matches PLAN.md's frozen statement by inspection
and uses the prescribed direct-or-visible-frame split. It does not mention
itself and imports no terminal theorem. The terminal theorem in
`GeneralAsymptoticConormal.lean` calls that wrapper; the existing following
projective theorem remains unchanged in this checkout. Historical T42 note
records a byte-identical statement check and signature digest
`c2c4b5117f933835399e3370528b960c7c831e0216a51d1a16a6242e668b262e`.
Build acceptance is pending.

The T36 dependency bridge remains unverified by Lean. No specific unsupported
mathematical bridge is exposed by static source inspection; first failure must
come from the queued module/consumer check, with exact Lean diagnostic retained
for escalation if it fails.

## T44 consumers

Both new literal consumers are present and route to the current theorem names.
The affine consumer is unconditional in `w` and derives the ground-point
output and smooth principal open. The original-prime consumer retains the
original avoidance binders and affine conclusion. The campaign checker
registers both. Their axiom output is pending Lean execution.

## Frozen input hashes

All hashes below are SHA-256 of the complete files in the frozen WT checkout:

| File | SHA-256 |
| --- | --- |
| `SameWitness/AffineFibreClosure.lean` | `a867ef9abd0f7a970dc0b5e18eb5fef15c30d8ab381b0ba03e7752679e082e17` |
| `SameWitness/OriginalPrimeAxis.lean` | `b117060a59dc58e5aac5b59ece0974127354c3ceadaab63cbd8293a76b89b695` |
| `GeneralAsymptoticConormal.lean` | `a285b9f9744b88e197d791ff5a6df9ca63495eb541de934d3cfcbc2fe91a7cb0` |
| `AffineFibreClosureConsumer.lean` | `abd7675321fc67fff024e800530810c9c17fa07b6334073fff6d2185d36c5f60` |
| `OriginalPrimeAxisConsumer.lean` | `354dd022b74277b277750fedf9cc91761bcbcfd6e4f51da3d00efd7313194118` |
| `scripts/dependency-guard/run_guard.py` | `80bbb21186f843aeea37b213bbe297add9b0efd2060b03098a69a2611cc553f7` |
| `scripts/verify.sh` | `0886c2a5deedb637c3e76c438cca1049adf292907a28c9c173948c262ef9c167` |
| `scripts/check-consumers.sh` | `6d28a4efa30dd9303838f7655ac81f289af479b1e77078b5458f42c2e73b4dfd` |

## Controller check queue

Run through the approved Lean guard after upstream acceptance, preserving each
log and the command's exact first error:

1. `lake build Stafford38.Geometry.SameWitness.AffineFibreClosure`
2. `lake env lean --trust=0 -M 32000 tests/SameWitness/AffineFibreClosureConsumer.lean`
3. `lake build Stafford38.Geometry.SameWitness.OriginalPrimeAxis`
4. `lake env lean --trust=0 -M 32000 tests/SameWitness/OriginalPrimeAxisConsumer.lean`
5. `lake build Stafford38.Geometry.GeneralCoisotropicExclusion Solution FixedSourceSolution`
6. `python3 scripts/dependency-guard/run_guard.py` (strict; no old-route override)
7. T44: run `scripts/check-consumers.sh` or individually compile the two
   registered consumers with `--trust=0 -M 32000` through the guard.

If one fails, freeze the exact base commit and the worktree patch digest before
asking Sol to repair it. Escalation packet: this assessment, the failing
command, complete guard log and first Lean error, the exact source file hashes
above, dependency acceptance state, and a request to repair only the first
unsupported bridge without changing any frozen statement, adding hypotheses,
raising `maxHeartbeats`, or adding forbidden axioms. No Qwen or protected-host
work is authorized by this assignment.
