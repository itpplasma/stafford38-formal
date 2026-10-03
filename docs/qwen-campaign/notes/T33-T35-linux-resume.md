# T33/T35 source assessment (Linux checks pending)

WT source base: `c3dccd4b3f931d15df623229771126f6500fb6ea` (`qwen/paper-route`).
T32 passed its guarded module and unchanged consumer checks. The bounded
resume addresses the missing retained point-local action context in T33/T35;
module and consumer checks for this revision are pending. An initial T33
compile exposed a missing open namespace for the already-imported canonical
point-local arc declarations; that namespace import is now explicit.

## T33: common-open Laurent arc

`CommonOpenArcData` retains the exact `CommonOpenData` and the selected point-local
arc, extends it through `genericArcToGenericOpenExtraAwayB`, and stores the
restriction, factor avoidance, and ground-map equations. Its proof of the
coefficient-to-common-open identity uses `CommonOpenData.hbaseMap` and
`CoordinatePresentation.hcoeff`; `hgroundU` is stated with the already-existing
`algebraMap k common.U`. The canonical arc field and its unit helper now carry
the action context reconstructed from retained `coords.coeff`, `coords.fFin`,
`coords.hBfinite`, and `common.hEtM`, including the associated tower and
essential finite-type structures. No scalar map is changed or duplicated.

Reused declarations: `commonOpen_factors_ne_zero_of_tiltedProduct`,
`genericArcToGenericOpenExtraAwayB`, `CoordinatePresentation.hcoeff`, and
`CommonOpenData.hbaseMap`.

| File | SHA-256 |
| --- | --- |
| `Stafford38/Geometry/SameWitness/CommonOpenArc.lean` | `78d5933e446812625dfc6229b662b9421abb291de4237264c5b84defe7ccc19b` |
| `tests/SameWitness/CommonOpenArcConsumer.lean` | `6a9bfc90f6ee3e971502659b6a522023659039eb37e6705e93ab93949479d9a7` |

## T35: common-open formally-etale maps

`CommonOpenEtaleData` packages `φk` and `ψU` as the two required `k`-algebra
maps, alongside the T22-shaped formal-etale facts. `φk` uses the T13 ground-map
identity; `ψU` is the selected coordinate map followed by the common-open map.
The explicit `hψAction` equality records the canonical scalar action used by
the formal-etale theorem and downstream coordinate derivations. The map and
its action equality now carry the retained coefficient and computed `fFin`
actions, tower, finite-type dictionary, and `common.hEtM` context in field
scopes. The producer reconstructs that same context from those retained
dictionaries; its only other local instance is proposition-valued maximality.

Reused declarations: `originalAffineChartToCommonOpen_groundMap`,
`formallyEtale_originalAffineChartToCommonOpen`,
`formallyEtale_genericOpenExtraAway_of_pointLocal`, and the T31 `fFin` map.
The T32 owner reports that `CommonOpenData` retains the fields this module
uses; the T31 owner reports no planned signature changes.

| File | SHA-256 |
| --- | --- |
| `Stafford38/Geometry/SameWitness/CommonOpenEtale.lean` | `5e5e780c022647a37da84e70681e495986ff865d2a49c5c12664c94ee0d33ea6` |
| `tests/SameWitness/CommonOpenEtaleConsumer.lean` | `04cf7171123196848753417fdffa3cdb3eb894fa2f2ca7b4ee8b584eae89131d` |

## Bounded T35 repair

A full projection audit found the private ground-map theorem had a stale
`CommonOpenArcData hm P w setup` binder (missing `coords`) and the body treated
arc data as though it directly exposed common-open fields. The package retains
those fields under `arc.common`; the repair updates those projections and uses
`arc.common.hbaseMap` for the Q-to-U identity while retaining the arc's own
`arc.hbaseMap` for the k-to-U identity. The public endpoint and consumer
statements are unchanged. The consumer remains byte-identical.

Updated T35 source SHA-256: `5e5e780c022647a37da84e70681e495986ff865d2a49c5c12664c94ee0d33ea6`.
The resumed T33 source supplies the required `coords` parameter to
`pointLocalArc_unit_of_not_mem` and unfolds `CommonOpenArcFactors` before
destructuring its stored factor and ground-map certificates. The resumed T35
source supplies the maximal-ideal proposition instance before requesting
`IsPrime`; retained coordinate and étale dictionaries are scoped with the
fields that use them. The consumers remain byte-identical. Lean evidence for
these frozen inputs is pending.

## Pending guarded evidence

Build each module alone, then run its literal consumer with `--trust=0 -M 32000`
and record `#print axioms` (allowed: `propext`, `Classical.choice`,
`Quot.sound`). Also record the required `letI`/`haveI` and `compHom` grep outputs.
The controller granted one exclusive Linux slot for these checks. These
candidates remain unaccepted until the guarded module and consumer checks pass
against the frozen WT input.
