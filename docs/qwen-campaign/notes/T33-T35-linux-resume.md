# T33/T35 source assessment (Linux checks pending)

WT source base: `c3dccd4b3f931d15df623229771126f6500fb6ea` (`qwen/paper-route`).
The candidate source and consumer files are committed at that base; no Lean
command has been run by this worker. Their current SHA-256 values match the
previous source notes.

## T33: common-open Laurent arc

`CommonOpenArcData` retains the exact `CommonOpenData` and the selected point-local
arc, extends it through `genericArcToGenericOpenExtraAwayB`, and stores the
restriction, factor avoidance, and ground-map equations. Its proof of the
coefficient-to-common-open identity uses `CommonOpenData.hbaseMap` and
`CoordinatePresentation.hcoeff`; `hgroundU` is stated with the already-existing
`algebraMap k common.U`. The module contains no local `Algebra`, `SMul`,
`Module`, or `IsScalarTower` installation and no `compHom`.

Reused declarations: `commonOpen_factors_ne_zero_of_tiltedProduct`,
`genericArcToGenericOpenExtraAwayB`, `CoordinatePresentation.hcoeff`, and
`CommonOpenData.hbaseMap`.

| File | SHA-256 |
| --- | --- |
| `Stafford38/Geometry/SameWitness/CommonOpenArc.lean` | `2533f9acaef04f978fc73b2f542f31b24b86d4bbb7d2db591c790ae33dcad98e` |
| `tests/SameWitness/CommonOpenArcConsumer.lean` | `6a9bfc90f6ee3e971502659b6a522023659039eb37e6705e93ab93949479d9a7` |

## T35: common-open formally-etale maps

`CommonOpenEtaleData` packages `φk` and `ψU` as the two required `k`-algebra
maps, alongside the T22-shaped formal-etale facts. `φk` uses the T13 ground-map
identity; `ψU` is the selected coordinate map followed by the common-open map.
The explicit `hψAction` equality records the canonical scalar action used by
the formal-etale theorem and the downstream coordinate derivations. Source
inspection finds no local `letI`, `haveI`, or `compHom` in this module.

Reused declarations: `originalAffineChartToCommonOpen_groundMap`,
`formallyEtale_originalAffineChartToCommonOpen`,
`formallyEtale_genericOpenExtraAway_of_pointLocal`, and the T31 `fFin` map.
The T32 owner reports that `CommonOpenData` retains the fields this module
uses; the T31 owner reports no planned signature changes.

| File | SHA-256 |
| --- | --- |
| `Stafford38/Geometry/SameWitness/CommonOpenEtale.lean` | `604f82d5da0e13f9eb86b4a316911f92941e94d57b309abbe0c12b8a6ff336a9` |
| `tests/SameWitness/CommonOpenEtaleConsumer.lean` | `04cf7171123196848753417fdffa3cdb3eb894fa2f2ca7b4ee8b584eae89131d` |

## Bounded T35 repair

A full projection audit found the private ground-map theorem had a stale
`CommonOpenArcData hm P w setup` binder (missing `coords`) and the body treated
arc data as though it directly exposed common-open fields. The package retains
those fields under `arc.common`; the repair updates those projections and uses
`arc.common.hbaseMap` for the Q-to-U identity while retaining the arc's own
`arc.hbaseMap` for the k-to-U identity. The public endpoint and consumer
statements are unchanged. The consumer remains byte-identical.

Updated T35 source SHA-256: `604f82d5da0e13f9eb86b4a316911f92941e94d57b309abbe0c12b8a6ff336a9`.
Static projection and forbidden-instance scans pass; Lean evidence is pending.

## Pending guarded evidence

Build each module alone, then run its literal consumer with `--trust=0 -M 32000`
and record `#print axioms` (allowed: `propext`, `Classical.choice`,
`Quot.sound`). Also record the required `letI`/`haveI` and `compHom` grep outputs.
The controller has not yet granted this worker a Lean slot. These candidates
remain unaccepted until those checks pass against a frozen WT input.
