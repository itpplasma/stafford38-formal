# T34 columns, derivatives and numerator

## Source audit

The archived repair4 block at `.lake/qwen/archive/repair4/Stafford38/Geometry/ActualSameWitnessAffineFibreClosure.lean:321-395` supplies the derivation sequence. It is adapted from the same-witness output and the T30–T33 packages; no premise is added for a column identity, smooth chart, or numerator nonvanishing.

Existing declarations reused:

- `ActualOptionCommonOpenColumns.actual_option_columns` gives position, transverse derivative and raw derivative identities for the retained `qT` and `qU`.
- `ActualOptionCommonOpenColumns.actual_option_columns_to_laurent` promotes those derivatives to Laurent coefficients using the existing `algebraMap k U`.
- `CommonOpenEvaluation.eval_map_eq_arc_eval₂` transports evaluation through the common-open map and the same arc.
- `ActualWitnessCommonOpenColumnGlue.actual_witness_commonOpen_eq_pointLocal` and `ActualCommonOpenCompletionDerivation.pointLocalToCommonOpen_comp_algebraMap` identify the selected witness coordinates with their common-open image.
- `ActualNormalizedProjectiveColumnInIntegralClosure` and its specification retain the original witness columns; `ChartSetup.hrF` identifies the selected numerator in the component fraction field.

The proof order is: use the retained `qT/qU` for `actual_option_columns`; define `qPre` from that same `qT`; derive the chart coordinate value from the retained normalized column; prove `hcoords` from the same-witness common-open equality; derive `hpositionL`; use the common-open base-map equation to transport the arc ground equation; call `actual_option_columns_to_laurent`; prove the `B`-valued homogenized evaluation equals the selected numerator image using `hrF`; apply `eval_map_eq_arc_eval₂`; rewrite the evaluation and use the already-derived arc nonvanishing.

## Instance and witness constraints

The endpoint requires derivative identities under `ψU.toRingHom.toAlgebra` for `ψU : MvPolynomial (Option (Fin d)) k →ₐ[k] U`. The common-open ring already has its ground algebra from localization. Use the T31 map and the common-open base-map equation to construct `ψU`; do not install a second concrete `Algebra k U` or `Algebra R U`. Preserve the selected witness in `qB`, `qT`, `qU`, `qPre`, and the numerator evaluation.

## Candidate modules

- `Stafford38/Geometry/SameWitness/CommonOpenPositions.lean` and `tests/SameWitness/CommonOpenPositionsConsumer.lean` derive `qPre`, `qL`, the chart coordinate, and the common-open position identities from the arc's retained `common` value.
- `Stafford38/Geometry/SameWitness/CommonOpenColumns.lean` and `tests/SameWitness/CommonOpenColumnsConsumer.lean` derive transverse/raw derivatives and the numerator evaluation from those positions, the T35 étale map, and `ChartSetup.hrF`.
- T33's finalized `CommonOpenArcData` has a `common : CommonOpenData` field; its arc maps remain direct fields. T34 consumers therefore use `arc.common.*` for chart, point-local and common-open data.

## Verification

Source and library search completed; `git diff --check` passed for the two source modules. No Lean command was run by this worker. The controller's exclusive Lean slot is required for the module and literal-consumer checks. Record the frozen paths and guarded logs after those checks.
