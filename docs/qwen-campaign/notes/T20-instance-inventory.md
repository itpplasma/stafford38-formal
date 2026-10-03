# T20 instance inventory

This is a diagnostic inventory of the archived proof, not a proof of its
closure theorem or manuscript correspondence. No production Lean source,
pin, verifier, or historical receipt was changed.

## Frozen evidence and interpretation

WT base: `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`.
Tracked WT patch SHA-256 (empty):
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
All paths below are relative to `/Users/ert/proj/stafford38-qwen`.
Each scratch is frozen under its own filename; negative `#synth` results are
intentional diagnostics and make the Lean command exit 1. There are no
failing `example` proofs and no synthetic `sorry` proof diagnostics.
No heartbeat or recursion budget was raised; typeclass timeouts retain the
default 20,000-heartbeat limit. “Missing” below means failed synthesis in the
specified context; a timeout does not prove mathematical nonexistence.

All checks used this command, serially, from WT:

```text
/Users/ert/proj/stafford38-formal/docs/qwen-campaign/guard.sh run --timeout 900 --log .lake/qwen/logs/T20-sol-N.log -- lake env lean -M32000 .lake/qwen/FILE.lean
```

| Run | Frozen scratch | SHA-256 | Guard result |
|---|---|---|---|
| 1 | `T20SolRings01.lean` | `db9c980da6228e5a6c89bbce03fdaa7e72563687e2e4f7d0acd96ab241fe1ba7` | exit 1, finished, 11 s, peak 0 GiB |
| 2 | `T20SolOpenRaw02.lean` | `62e0b1fea8ec60231a69fdfab3b6a233bf7208e6a5bfb6c5a9e7af4ddf2d58d9` | exit 1, finished, 21 s, peak 3 GiB |
| 3 | `T20SolOpenStaged03.lean` | `7974c6919e70ac9e983a3e2cfe0971b1851c618084e925e72ccfba0480c46bbb` | exit 1, finished, 20 s, peak 3 GiB |

Scratch filenames in the table live in `.lake/qwen/`; each run's log is
`.lake/qwen/logs/T20-sol-N.log`. Guard reported 85 GiB free memory,
553 GiB free disk, zero swap, and no resource refusal for these runs.

The imports are the archived import surface, with both unavailable
`GroundPointAxisLiftFromOutput` imports replaced by the accepted source
`SameWitness.AxisLiftFromGroundPoint`. The recursive source-resolution
inventory `.lake/qwen/T20-sol-source-imports.json` initially checked 264
files and found zero missing Stafford38 source imports. Cached archived
modules are not used as substitutes for absent sources.

Run 1 uses actual `P,w` throughout. It first checks F,Q,B,R,A₀ without
any added algebra, then installs the unavoidable witness ambient algebra
(archived line 105) to express V. It checks V before its DVR and coefficient
fields, then checks κ after DVR installation and before ground-algebra
installation. Installing the actual coefficient/V algebra is a separate
stage. No ground action on V or κ is assumed to get green results.

Run 2 uses the actual Q and B, a prime ideal M of that B, and a localization
equivalence e of the exact archived type. M,f,g,e are data parameters,
not claims that the later producer has already returned them. It adds no
algebra or tower assumptions. Run 3 repeats the checks after installing
only the actual `actualSelectedNormalizationCoefficients` k/B algebra and
its explicit k/Q/B tower. Both raw and staged checks synthesize k/U.

The older Luna concrete-final probe, SHA-256
`3827e650ba779e312c14f900f84d7ed74f82698b7f57a71500c8d15127ac65cd`,
with log `.lake/qwen/logs/T20-luna-concrete-final.log` (exit 0, 20 s,
3 GiB), remains valid conditional evidence after its k/B and k/Q/B
installations. Its abstract opening section and the earlier abstract
inventory are not evidence for an unconditional witness-ring inventory.
The earlier mutable-filename probes are not used to support this table.

## Concrete ring inventory

Line numbers refer to the 446-line archived
`.lake/qwen/archive/repair4/Stafford38/Geometry/ActualSameWitnessAffineFibreClosure.lean`.
Let S denote `MvPolynomial (Fin m) k`, and K denote `W.coefficientField`.
“Duplicate” classifies a same-base instance already available; it does not
assert definitional equality between two implementations of that instance.

| Ring | Archived definition and source owner | Available before the corresponding additions; real evidence | Added instances and classification |
|---|---|---|---|
| F | `ComponentFractionField P` (103), `ComponentProjectiveClosure.lean:32`: `FractionRing (S ⧸ P.asIdeal)` | Run 1: k/F = `OreLocalization.instAlgebra`; Q/F = `(actualSelectedChartAlgebra P w).toAlgebra`. Local-coefficient/F fails before line105. | 105 local-coefficient/F: **new**, supplied by `W.ambientAlgebra`. 129 Q/F via `Q.val.toAlgebra`: **duplicate**. |
| V | `U := W.place.valuation` (106), `V := U.toSubring` (107); this U is the valuation, not the later common-open ring | Run 1 after105: k/V and K/V fail; DVR/V fails before108. After108, local-ring/V synthesizes. | 108 DVR: **new**, witness field. 109 local-ring: **duplicate** after108. 110–111 K/V: **new**, actual `relativeCoefficientMap`. No k/V is installed. |
| κ | `ResidueField V` (112), Mathlib `IsLocalRing.ResidueField` | Run 1 after108: V/κ = `ResidueField.algebra`; k/κ and K/κ fail. After110, K/κ synthesizes via `ResidueField.algebra`, but k/κ still fails. | 113 k/κ: **new**, supplied by `retainedResidueGroundAlgebra`. |
| Q | `actualSelectedChartAlgebra P w : Subalgebra k F` (114), `ActualSelectedNormalizationDivisorEtale.lean:85`, from `chartGenericPointSubalgebra` | Run 1: k/Q = Q's `.algebra`. Q/F is already inherited, as above. | No algebra targeting Q is installed. |
| B | `actualSelectedNormalization P w` (115), `ActualSelectedNormalizationDivisorEtale.lean:93`: integral closure of `Q.toSubring` in F, bundled as a subalgebra | Run 1: Q/B = B's `.algebra`; k/B fails. k/Q/B cannot elaborate before k/B (missing `SMul k B`). | 116 domain: **duplicate**, inherited subalgebra domain. 123 k/B: **new** from `coeff`. 124 Q/B: **duplicate**, intrinsic normalization algebra already exists. 125–128 k/Q/B: explicit coherence, **new** (default synthesis times out after123). 174 finite type: witness certificate, **new**. 177 Q/B: **duplicate** of124 and intrinsic action. 203 R/B and204–209 k/R/B: see staged action audit below. |
| R | `d := Fintype.card t` (199), `MvPolynomial (Option (Fin d)) k` (200), Mathlib `MvPolynomial` | Run 1: k/R = `AddMonoidAlgebra.algebra`, before any R/B action. d is a natural-number parameter in diagnostics; the instance holds for every d, including the actual cardinality. | No algebra targeting R is installed. 203–210 concern its action and finite-type structure on B. |
| Cq | `genericOpenRing M f e` (259), `EtaleGenericOpenTransport.lean:34`: localization of `Localization.Away f` at `genericOpenDenominators` | Run 2: Q/Cq and k/Cq = `OreLocalization.instAlgebra`; B/Cq = `instGenericOpenBAlgebra`. | 262 Q/Cq via `inferInstance`: **duplicate**. 308–309 R/Cq: **new** map through B (see staged audit). |
| U | `genericOpenExtraAwayB M f e g` (261), `EtaleGenericOpenExtraAwayB.lean:13`: away localization of Cq at the B-image of g | Run 2, without k/B: Cq/U, Q/U, k/U = `OreLocalization.instAlgebra`; B/U = `instGenericOpenExtraAwayBAlgebra`. Run3 confirms these after upstream scalar coherence. | 263 Cq/U: **duplicate**. 264 Q/U via `Algebra.compHom`: **duplicate**, violates rule6.2.8. 311 k/U via `Algebra.compHom`: **duplicate** and **needed by endpoint**. Later action, SMul, tower and étale additions are listed individually below. |
| A₀ | `S ⧸ P.asIdeal` (396), Mathlib ideal quotient | Run 1: k/A₀ and S/A₀ = `Ideal.instAlgebraQuotient` for their respective bases. | No algebra targeting A₀ is installed. 413–426 concern its action on U and endpoint towers. |

## Endpoint prerequisites at the raw common-open stage

The exact endpoint telescope is
`ActualSameWitnessAffineFibreEndpoint.lean:35–51`.
Run 2 checks all ten U prerequisites individually before installing them:

| Endpoint prerequisite | Raw concrete result | Run2 scratch line |
|---|---|---|
| `Algebra k U` | **available**, `OreLocalization.instAlgebra` | 55 |
| `Algebra A₀ U` | failed synthesis | 59 |
| `Algebra S U` | failed synthesis | 61 |
| `Algebra R U` | failed synthesis | 63 |
| `IsScalarTower k A₀ U` | missing A₀/U scalar action; default 20,000-heartbeat timeout | 65 |
| `IsScalarTower k S U` | missing S/U scalar action; default timeout | 67 |
| `IsScalarTower k R U` | missing R/U scalar action; default timeout | 69 |
| `IsScalarTower S A₀ U` | missing A₀/U scalar action; default timeout | 71 |
| `Algebra.FormallyEtale A₀ U` | prerequisite A₀/U algebra missing | 73 |
| `Algebra.FormallyEtale R U` | prerequisite R/U algebra missing | 75 |

Thus only k/U among the ten endpoint prerequisites synthesizes at this
stage. The other nine are not established by this inventory. In particular,
failed prerequisite elaboration is not an independent proof of failure of
a formal-étale proposition. Run3 gives the same endpoint diagnostics after
the actual k/B and k/Q/B installations. Its additional k/Q/Cq and k/Q/U
tower checks time out while seeking the Q scalar action; a tower assumption
on B is not a receipt for those concrete tower syntheses.

## Additions after the option and quotient maps

Two further frozen diagnostic runs check the staged instance mechanism on
the actual witness-dependent B,Cq,U,A₀ carriers. These are **conditional**
stages, not evidence that the witness producer has already supplied the
maps or endpoint certificates. Run6 takes an R/B algebra and then a k/R/B
tower as instance parameters after separately checking their absence or
search timeout. It constructs the exact line308 R/Cq composite. Run7 takes
an A₀/U algebra parameter, then constructs the exact polynomial composite
of line417. It does not prove that this parameter is φ's action.
The unconditional ring inventory and raw endpoint results above come from
runs1–2, which do not assume those extra actions.

| Run | Frozen scratch | SHA-256 | Guard result |
|---|---|---|---|
| 6 | `T20SolOptionStages06.lean` | `1c82c0d12e1799e2190e77a94eec81e5b5be43a0ca1a1d688d9eaf805bc00633` | exit1, finished, 21 s, peak3 GiB |
| 7 | `T20SolQuotientStages07.lean` | `dc68bbaf0b5d92adcd238f954877bdd6fc11a59985c0477055d3b761eb2231d8` | exit1, finished, 20 s, peak3 GiB |

Run4 (`T20SolOptionStages04.lean`, hash
`9ef1b24d0babc9991ec3f4d5571b1798f91ee89d367b244b29704521da1b8664`,
log `T20-sol-4.log`, exit1, 31 s, 3 GiB) had an uninferable ordinary
`fFin` parameter on a scratch local instance. Its downstream diagnostics
are excluded. Run6 replaces that invalid registration with an explicit,
clearly marked conditional instance parameter. `T20SolQuotientStages05.lean`
was prepared but never checked; no result is claimed for it.

The following table covers every remaining archived Algebra, SMul and
tower addition. All additions at105,110,113,123–129,174,177,262–264 have
already been classified in the nine-ring table. “Needed by endpoint” is a
role classification; it never substitutes for a checked instance.

| Archived lines | Addition | Classification and evidence |
|---|---|---|
| 203 | `Algebra R B := fFin.toRingHom.toAlgebra` | **new** upstream action. Run6:48 search times out before the R/B parameter is supplied; no intrinsic polynomial action is confirmed. The actual map is the `actualOptionMap` composed with the rename equivalence (194–202). |
| 204–209 | `IsScalarTower k R B` | **new** explicit coherence for fFin. Run6:51 times out (seeking `SMul R F`) before the tower parameter is supplied. The archived proof uses fFin's ground commutation equation. |
| 210 | `Algebra.EssFiniteType R B` | **new** explicit proof via `Algebra.EssFiniteType.of_comp k R B`; run6:76 fails before a finite-type certificate is installed. This diagnostic does not claim failure after174's hBfinite. |
| 252 | `Algebra.FormallyEtale R (Localization.AtPrime M)` | **new** certificate hEtM from the axis-lift producer; run6:57 fails even with the R/B parameter. Not a formal-étale instance on U and not inherited merely from localization. |
| 308–309 | `Algebra R Cq` from B | **new**. Run6:53 fails before installing the composite. |
| 310 | `Algebra R U := Algebra.compHom U (algebraMap R Cq)` | **duplicate after308**, **needed by endpoint**. Run6:61 synthesizes `OreLocalization.instAlgebra` after installing308's composite, before installing310. Thus310 also falls under rule6.2.8. At the earlier raw stage the R/U algebra was missing. |
| 311 | `Algebra k U := Algebra.compHom U (algebraMap k R)` | **duplicate**, **needed by endpoint**; raw run2:55 already synthesizes k/U. Equality of this R-route map with the inherited ground map requires coherence, not another algebra registration. |
| 312 | `SMul R U := (inferInstance : Algebra R U).toSMul` | **duplicate bundled projection** of the immediately installed310 algebra. It explicitly registers that action; run6:67 shows that direct automatic SMul search after308 can time out despite successful R/U algebra synthesis. Do not report an automatic SMul success. |
| 313 | `SMul k U := (inferInstance : Algebra k U).toSMul` | **duplicate bundled projection** of311; run6:69 also synthesizes the inherited k/U SMul (`OreLocalization.instSMulOfIsScalarTower`). |
| 314–318 | `IsScalarTower k R U` | **needed by endpoint**, explicit new coherence proof; run6:63 times out seeking R/U SMul. Its success under the archived explicit SMul registrations is not checked here. |
| 319–320 | `Algebra.FormallyEtale R U` | **needed by endpoint**, new explicit certificate from `formallyEtale_genericOpenExtraAway_of_pointLocal`; run6:65 fails even after R/Cq is installed. |
| 413 | `Algebra A₀ U := φ.toAlgebra` | **new**, **needed by endpoint**. Raw run2:59 fails; the proof's map φ is `originalAffineChartToCommonOpen` at285. |
| 414 | `SMul A₀ U := quotientAlgebra.toSMul` | **duplicate bundled projection** of413, explicitly registers its action. Run7:51 times out in automatic SMul search with an A₀/U algebra parameter; the timeout does not remove its bundled toSMul. |
| 417 | `Algebra S U := Algebra.compHom U (algebraMap S A₀)` | **new**, **needed by endpoint**. Run7:53 still fails after assuming an A₀/U algebra; generic transitivity does not synthesize an S/U algebra. |
| 418 | `SMul S U := polynomialAlgebra.toSMul` | **duplicate bundled projection** of417, explicitly registers its action. Run7:60 times out even after constructing417's composite, so no automatic SMul success is claimed. |
| 419–420 | `IsScalarTower k A₀ U` from hphiGround | **needed by endpoint**, new explicit coherence proof. Run7:55 times out seeking A₀/U SMul before installing that coherence. |
| 421–422 | `IsScalarTower S A₀ U` | **needed by endpoint**, new explicit composite-map coherence. Run7:62 times out seeking A₀/U SMul after installing the S/U algebra. |
| 423–424 | `IsScalarTower k S U` via `to₁₂₄` | **needed by endpoint**, new explicit tower derived from419 and421. Run7:64 times out before those two tower certificates are installed; no failure after their installation is claimed. |
| 425–426 | `Algebra.FormallyEtale A₀ U` | **needed by endpoint**, new certificate from `formallyEtale_originalAffineChartToCommonOpen`. Run7:57 fails after assuming the A₀/U algebra but before supplying the chart certificate. |

Other local facts are not scalar-action additions: Fintype t (175),
PB.IsPrime (176), and M.IsMaximal (251) expose finite/prime/maximal witness
fields. They are not endpoint algebra requirements. The finite-type k/B
certificate at174 fails synthesis before it is supplied (run6:74); domain/B
at116 synthesizes as `Subalgebra.isDomain` (run6:72).

## Acceptance and boundaries

The nine required ring rows, concrete baseline synthesis, all archived
Algebra/SMul/tower classifications, and all ten endpoint prerequisite
checks are recorded above. The expected k/U, Q/U and Cq/U actions are
confirmed directly on the actual witness carriers. The archive reinstalls
k/U and Q/U, and also R/U after R/Cq. Intrinsic Q/B and Q/F must likewise
be counted as duplicates. The concrete raw inventory does not need k/B
as an assumption to establish the localization ground action.

The SMul and tower timeouts are retained diagnostic evidence for T21/T22;
they are not repaired by raising budgets. This task establishes no new
endpoint coherence, formal étaleness, or closure theorem. The conditional
staged runs must not be promoted into unconditional witness facts.

Final recursive source receipt:
`.lake/qwen/T20-sol-source-imports-final.json`, SHA-256
`ce5149582b90ac2e6e2dbe438a6d014abf557a0ad724f754dfa42d33ed5289eb`.
It freezes the five accepted scratch sources, 259 project source files,
all five log hashes and guard summaries, toolchain/manifest hashes, and the
archived source hash. All 264 source paths exist in WT; zero Stafford38
imports are satisfied only by cache. The initial source receipt remains
historical; use this final receipt for review.

Worker ownership: only this note and `.lake/qwen/` scratch were changed.
No worker commit, ledger update, promotion or push was made. Controller
acceptance and authoritative state changes remain with the controller.

## Controller acceptance

The controller accepted the corrected inventory after reviewing all rows,
verifying the 264 source hashes and five diagnostic log hashes, and checking
the declared source-resolution scope. The frozen five scratch files, five
logs and final receipt are preserved in [T20-diagnostics.tar.gz](T20-diagnostics.tar.gz),
SHA-256 `b1fe72e22d5d236a0923944ed8fa2103ae32590609567e5f12cc63ac28250519`.
These are class-synthesis diagnostics with intentional failures, separate
from theorem and verifier receipts.
