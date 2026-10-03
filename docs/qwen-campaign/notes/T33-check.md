# T33 arc into Laurent series

## Scope

Prepare `Stafford38/Geometry/SameWitness/CommonOpenArc.lean` and
`tests/SameWitness/CommonOpenArcConsumer.lean`. No Lean command has been run;
the controller has reserved Lean while T22 uses the exclusive slot. The
T32's frozen interface is `CommonOpenData hm P w setup coords`, constructed
by `nonempty_commonOpenData hm P w setup coords hpoint`.

## Archived mathematical step

The repair4 proof at lines 294–320 defines
`rhoA := originalToPointLocalFinSuccArcLaurentSeries`, proves that every
element outside `M` maps to a unit by localization at `M`, and defines
`rhoU := genericArcToGenericOpenExtraAwayB ...`. Its factor-avoidance result
provides `hf`, `hg`, `hcomp`, and `hgroundB`. The proof then obtains
`hcomp'`, the ground equation along `B`, and finally the ground equation
along `U` using the common-open base-map equation from line 368. The target
is `rhoU.comp (algebraMap k U) = algebraMap k (LaurentSeries k)`.

## Instance constraint

The accepted T20 inventory records that the common-open localization `U`
already synthesizes `Algebra k U`. It also classifies the archived
`Algebra.compHom` installation at line 311 as a duplicate and disallowed by
PLAN section 6.2.8. T33 must use that existing `algebraMap k U`; it must not
install another `Algebra k U`, `SMul k U`, or tower on the concrete carrier.
The planned proof derives `hgroundB'` from the factor theorem and rewrites
back along
`hbaseMap : (genericOpenExtraAwayBMap M f e g).comp (algebraMap k B) =
  algebraMap k U`.

## Consumer interface requested

T34 needs a named arc package retaining the whole `CommonOpenData` so its
`alpha`, `qT`, and `qU` remain available. The drafted package
`CommonOpenArcData hm P w setup coords` stores it in `common` and exposes
`rhoU`, `hgroundU`, and `hbaseMap`, as well as `rhoA`, `hunitM`, `hf`, `hg`,
`hcomp'`, and `hgroundB'`. The fields `hcanonicalRhoA` and
`hcanonicalRhoU` record that these maps are exactly the retained point-local
arc and its generic-open extension. It also retains `hbadU`, `hrU`, `hq0U`,
and `hq1U` for the downstream numerator argument. Its constructor is
`exists_commonOpenArcData hm P w setup coords common`. T34, T35, and T36 have
received this interface.

## Reused declarations

- `Stafford38.Geometry.ActualCommonOpenArcCompatibility.commonOpen_factors_ne_zero_of_tiltedProduct` supplies the unit, arc-composition, ground-composition, and nonzero-factor data already retained by T32's `hfactor`.
- `Stafford38.Geometry.EtaleGenericOpenTransport.genericArcToGenericOpenExtraAwayB` extends the selected point-local arc to the common open.
- `CommonOpenData.hbaseMap` gives the existing Q/Cq/U localization map identity; T33 composes it with the retained coefficient map `coords.coeff` to obtain the required k/B/U identity.
- `CoordinatePresentation.coeff` is the canonical coefficient map `k →+* B`; its `toAlgebra` instance is already used by the retained `hfactor` field and is also used explicitly in T33's ground-map statements.
- T31 added `CoordinatePresentation.hcoeff` to state the canonical coefficient map equality explicitly; T33 uses that equation when it composes T32's Q/Cq/U map identity with `k → Q`.

## Frozen candidate inputs

The WT base commit when these candidate hashes were last checked is
`5228a6d3f372552e887190b86ff2eafdf7fc8a80`.
Current candidate file SHA-256 values after adding canonical map equalities
and switching to the explicit `common` field:

| Path | SHA-256 |
| --- | --- |
| `Stafford38/Geometry/SameWitness/CommonOpenArc.lean` | `2533f9acaef04f978fc73b2f542f31b24b86d4bbb7d2db591c790ae33dcad98e` |
| `tests/SameWitness/CommonOpenArcConsumer.lean` | `6a9bfc90f6ee3e971502659b6a522023659039eb37e6705e93ab93949479d9a7` |

These inputs remain candidates only: neither a Lean module check nor its
consumer axiom report has run.

The only new mathematical definition is the requested package structure.
No closure assumption, smoothness assumption, column identity, or avoidance
premise is added to the arc construction.
