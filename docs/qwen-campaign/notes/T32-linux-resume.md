# T32 common-open resume note

## Frozen candidate

- Worktree base: `c3dccd4b3f93` (`campaign/paper-route-20261003`).
- `Stafford38/Geometry/SameWitness/CommonOpen.lean`: SHA-256 `0d1c0cd2c03c91f352377cfdcc175c77d42c991ce51b4c753cf4203695594308`.
- `tests/SameWitness/CommonOpenConsumer.lean`: SHA-256 `fdd4982c7e63eca36b5c1bd6eed51957dbec7f698fa1b74f576af64e8169d757`.
- These hashes freeze the inspected saved candidate; no Lean check was run by this reviewer.

## Static review

`nonempty_commonOpenData` receives `hpoint`, obtains `CoordinatePresentation` from the corresponding constructor, and passes `coords.hOutput` to `exists_axis_lift_of_groundPointChartOutput`. This preserves the selected witness through the ground-point output; it does not assume the closure conclusion. It separately uses the accepted `ChartSetup` data for `bad = fB * rB` and its nonzero proof.

The package provides the requested maximal center, residue equivalence, units, tilted axis data, selected quotient coordinates, common-open map and factorization. The definitions `CommonOpenData.g`, `Cq`, `U`, `qU`, `qT`, and `φ` are computed from retained fields. `hbaseMap` records the single `Q → Cq → U` route. No second `Algebra Q U` or `Algebra.compHom` appears in this module. The consumer applies `nonempty_commonOpenData` to the literal `Nonempty (CommonOpenData ...)` conclusion and prints its axioms.

T33 and T34 workers confirmed their expected field names (`M`, `hM`, `eM`, `alpha`, `hEtM`, `hfactor`, `hbaseMap`, `qT`, `qU`, `hqUPoint`) are present. The T32 definition-entry draft records `CommonOpenData`; the computed namespace definitions also need registry entries if the controller treats each `def` as a separately owned declaration.

## Acceptance dependency and requested check

T30 was controller-accepted (module and literal consumer passed). T31 is still pending: its latest recorded final guarded module build failed on unresolved source-DVR algebra/local-ring instances and a universe mismatch; the consumer was not run. Therefore T32 acceptance must wait for a repaired, checked T31 source and consumer.

After the controller grants the guarded slot and T31 passes, request:

```sh
/Users/ert/proj/stafford38-formal/docs/qwen-campaign/guard.sh run --timeout 900 --log /home/ert/proj/stafford38-qwen/.lake/qwen/logs/T32-linux-module.log -- lake build Stafford38.Geometry.SameWitness.CommonOpen
/Users/ert/proj/stafford38-formal/docs/qwen-campaign/guard.sh run --timeout 900 --log /home/ert/proj/stafford38-qwen/.lake/qwen/logs/T32-linux-consumer.log -- lake env lean --trust=0 -M 32000 tests/SameWitness/CommonOpenConsumer.lean
```

Do not execute on a login node or outside the controller's guarded allocation. Verify that theorem and consumer axioms are only `propext`, `Classical.choice`, and `Quot.sound`; attach exact host/job and guard resource summaries to the acceptance receipt.

## Definition owner entries

- `Stafford38.Geometry.SameWitness.CommonOpenData` — `Stafford38/Geometry/SameWitness/CommonOpen.lean` — bundles the retained maximal center, axis lift, selected chart coordinates, and common-open maps; existing common-open owners describe localizations or different conditional chart data.
- `Stafford38.Geometry.SameWitness.CommonOpenData.g` — same file — derives the selected denominator from `hsel`; no existing owner binds this witness-specific chart element.
- `Stafford38.Geometry.SameWitness.CommonOpenData.Cq` — same file — names the generic open attached to this retained maximal center; the generic localization owner does not bind the center in the package.
- `Stafford38.Geometry.SameWitness.CommonOpenData.U` — same file — names the extra-away localization of `Cq` at this package's selected denominator.
- `Stafford38.Geometry.SameWitness.CommonOpenData.qU` — same file — derives all projective columns in this package's common open from its `qQ` and localization maps.
- `Stafford38.Geometry.SameWitness.CommonOpenData.qT` — same file — derives the retained columns in the point-local localization at this package's center.
- `Stafford38.Geometry.SameWitness.CommonOpenData.φ` — same file — derives the original affine-chart map into this package's common open from its selected chart and center.
