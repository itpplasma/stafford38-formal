# T34 static resume assessment

Base inputs: MAIN `3214f5c8f336de67d3e90af0594f420a41e9056b`; WT
`c3dccd4b3f931d15df623229771126f6500fb6ea` (`campaign/paper-route-20261003`).
No Lean command was run; no controller Lean slot was granted.

## Interfaces

The current T34 source matches the T32/T33 interface reported by their
owners: `CommonOpenArcData.common` retains `M`, `eM`, `alpha`, `qT`, `qU`,
`hEtM`, and `hqUPoint`; the arc retains `rhoU`, `hcanonicalRhoA`,
`hcanonicalRhoU`, `hgroundU`, `hgroundB'`, and `hrU`. T34 position and
column consumers use `coords.t`, `htFinite`, `coeff`, `fFin`, `hcoeff`, and
`setup.j`, `p`, `r`, `hrF`. T35 supplies `etale.ψU`, `hψEtale`, and
`hψAction`; T34's endpoint derivative binders use `etale.ψU.toRingHom.toAlgebra`
and `etale.ψU.comp_algebraMap.symm`.

## Mathematics audit

`CommonOpenPositions` follows the retained qT/qU witness: `actual_option_columns`
provides the point-local position; `hqUPoint` and
`pointLocalToCommonOpen_comp_algebraMap` identify qU with the same normalized
column; `actual_option_columns_to_laurent` transports its position through
`rhoU`. `CommonOpenColumns` obtains the transverse/raw identities from the
same qT/qU, proves the B-valued homogenized evaluation by `hrF`, then uses
`eval_map_eq_arc_eval₂` and `hrU` for the exact selected numerator. No new
geometric premise or statement weakening was found. The actual selected
numerator is preserved.

## Failed bounded-task condition

Static review found a concrete violation of PLAN 6.2.8 in
`CommonOpenColumns.lean`: the proof installs `Algebra R U` with `Algebra.compHom`
on the concrete common-open ring (`letI` near line 137), even though
T35 supplies the `R →ₐ[k] U` action and `hψAction` records its equality with
the common-open composite. That is the exact duplicate-action risk that the
plan forbids. Earlier the two endpoint derivative binders also installed a
second `Algebra k U`; this was removed in the current candidate so that the
endpoint fields use the inherited k-action and T35's ψ tower. The remaining
proof-local action cannot safely be accepted without adapting the generic
column transport across `hψAction`. Its current local instances on B, its
localization, and U also fail the concrete-heavy-type rule; the position file
avoids this via its abstract `commonOpen_position_of_pointColumns` theorem.

Required Sol repair: move the derivative/column transport into an adapter
whose ring parameters are abstract (PLAN 6.2.4), take the T35 ψ action and
its map-equality certificate as inputs, and prove the output under exactly
that action. Do not add any `Algebra k U`/`Algebra R U` compHom instance or
extra hypothesis. If the adapter cannot be stated using the existing
`actual_option_columns` and `actual_option_columns_to_laurent` conclusions,
return the exact first elaboration obstacle for controller review. No Lean
attempt is recorded, so this is a static task failure, not a compiler failure.

`git diff --check` passed after removing the redundant `Algebra k U` binders.
The four source/consumer SHA-256 values are recorded in the controller
message; source candidates remain unaccepted and unpromoted.
