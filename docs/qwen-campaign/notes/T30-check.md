# T30 chart setup receipt

- Archived source: `.lake/qwen/archive/repair4/Stafford38/Geometry/ActualSameWitnessAffineFibreClosure.lean`, lines 96–166, read from the pinned WT archive. The candidate packages the smooth principal open and polynomial representative, successor chart, selected-normalization away equivalence, homogenized numerator and its two archived value formulas, and the injectivity/nonvanishing consequences used by the following blocks.
- Existing declarations reused: `exists_succ_chart_index`, `actual_selected_normalization_is_away_equiv`, `exists_nonzero_homogenized_numerator`, `chartSubalgebraToIntegralClosure`, and `coe_chartSubalgebraToIntegralClosure`.
- The constructor takes only the supplied smooth-open existence statement; it does not take or unpack the ground-point output. The numerator follows from that open's representative and nonzero quotient class.
- Initial frozen candidate: `ChartSetup.lean` `2dcb9b4f5e195cb1a24c4fc16f136f873ddfd48ae35e6d3dd130c48badbefc99`; `ChartSetupConsumer.lean` `dacfb08ad15a8b6cfa52760d4597d1ffc58226b822b3b862878cbd05e2b36f89`.
- Guarded build 1 failed in 4 s, peak RSS 1.9 GiB, exit 1 (`.lake/qwen/logs/T30-local-build-1.log`). The source needed namespace opens for existing owners of `ComponentFractionField`, `componentAffineGenericPointMap`, and the chart-to-integral-closure map. It also exposed that `Function.Injective` takes implicit points; the injectivity proofs now apply it to the equality directly.
- Guarded build 2 failed in 4 s, peak RSS 2.0 GiB, exit 1 (`.lake/qwen/logs/T30-local-build-2.log`): the chart-to-integral-closure map is owned by `SelectedResidueCoefficientLocalization`, not a same-named normalization namespace. The source open was corrected.
- Final candidate SHA-256: `ChartSetup.lean` `a8107782808a6839e9dcddf85e0b364cca92675a84d442220d4b68287a85323a`; consumer `dacfb08ad15a8b6cfa52760d4597d1ffc58226b822b3b862878cbd05e2b36f89`.
- Static hygiene after repair: `git diff --check` passed; mandated scans found no `letI`, `haveI`, or `compHom` in the candidate module.
- Guarded build 3 passed: `lake build Stafford38.Geometry.SameWitness.ChartSetup` → exit 0, 7 s, peak RSS 2.1 GiB (`.lake/qwen/logs/T30-local-build-3.log`).
- Literal consumer passed: `lake env lean --trust=0 -M 8000 tests/SameWitness/ChartSetupConsumer.lean` → exit 0, 3 s, peak RSS 0.9 GiB (`.lake/qwen/logs/T30-local-consumer.log`). Both the theorem and consumer print only `[propext, Classical.choice, Quot.sound]`.
- Both successful guard summaries used RSS cap 8 GiB and two Lean threads; no resource guard fired.

## Controller acceptance

The controller checked the final source and accepted build/consumer evidence. Source, logs and the literal consumer are archived in `T30-accepted-checks.tar.gz` (SHA-256 `d76f1db20b80596f3e0975e5827737ca46984eb87027653074552e1db739d541`). These checks establish this helper's recorded scope; full route and repository verification remain separate gates.
