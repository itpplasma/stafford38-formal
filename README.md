# Stafford's Conjecture 3.8 for Weyl algebras

For every characteristic-zero field `k`, every `n ≥ 0`, and every nonzero
`d ∈ Aₙ(k)`, there exist `F, R, S ∈ Aₙ(k)` such that

```text
1 = d R + F d S.
```

The [Lean theorem](Stafford38/FoundationClosure.lean) preserves this written
order. The [exact-degree strengthening](Stafford38/FixedSourceStatement.lean)
chooses, at positive rank, a linear Weyl coordinate `ℓ` and takes
`F = ℓ^(bernsteinDegree k d)`. Rank zero is the field case.

Commit **`219668ef77b4ffddc1a503fd1ce61dbd48aa4b17`** was verified from a fresh independent clone.
The checked scope includes both theorems, the manuscript's general geometric
theorems, and the corollaries below. The allowed foundational axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`; no project or literature
axioms are used. The [verification report](docs/verification-results.json)
records the checks: `df7c23125820af9a23e8c2f01e4fa9873341f2d29be6dc46eb833180d183166a`. Independent human expert review
and journal review are separate; neither is claimed complete.

| Dependency | Exact version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.1` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`) |
| [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) | `2fdc928835347a2638b6c85a4bfa770e3f70ed9e` |

From the checked-out commit with Lean installed through Elan:

```sh
lake exe cache get
lake build
scripts/verify.sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh
```

## Proof architecture

1. **Symplectic monicization.** A linear symplectic change makes a non-scalar
   element monic with degree equal to its Bernstein degree:
   [`scalar_or_normalized_symplectic_image`](Stafford38/Weyl/MonicNormalization.lean).
2. **Canonical quotient.** Form the right-ideal quotient
   `A/(dA + xᴺdA)` and retain the coefficient order through the presentation:
   [`canonicalRightIdeal`](Stafford38/Weyl/EulerResidue.lean)
   and the [quotient transport](Stafford38/Weyl/QuotientTransport.lean).
3. **Euler surjectivity.** The positive Euler residue and right division make
   multiplication by `x` surjective on the quotient:
   [`positiveEulerResidue_identity`](Stafford38/Weyl/EulerResidue.lean) and
   [`presentedCanonicalQuotient_rightMul_coordinate_surjective`](Stafford38/Weyl/EulerRemainder.lean).
4. **Characteristic support.** Opposing filtered Koszul length inequalities
   force the characteristic support away from `x = 0`:
   [`canonical_support_avoidance`](Stafford38/Characteristic/CanonicalKoszulContradiction.lean).
5. **Involutivity.** Prove the radical of the graded annihilator involutive
   for every cyclic Weyl quotient:
   [`weylAssociatedGradedRadicalInvolutivity`](Stafford38/Characteristic/GabberGlobalAssembly.lean).
6. **Asymptotic conormal geometry.** Construct the tangent lattice and boundary
   divisor, then obtain the projective conormal direction:
   [`tangent_limit_criterion_of_directSummand`](Stafford38/Geometry/GeneralTangentLimitCriterion.lean)
   and [`coordinate_axis_mem_projective_conormal_directions`](Stafford38/Geometry/GeneralAsymptoticConormal.lean).
7. **Coisotropic exclusion.** Apply the general fibre-conical set theorem with
   its self-involutive vanishing-ideal hypothesis:
   [`exists_zero_base_coordinate_of_isFibreConical`](Stafford38/Geometry/GeneralCoisotropicSets.lean)
   and the [canonical support application](Stafford38/Geometry/GeneralCoisotropicCanonicalAdapter.lean).
8. **Certificate extraction and transport.** Descend from an algebraic closure,
   extract membership of `1` in the right ideal, and undo the symplectic change:
   [`exists_fixedSource_certificate_of_orderCharacteristicSupport_eq_empty`](Stafford38/Characteristic/CanonicalCertificate.lean)
   and [`universalStatement`](Stafford38/FoundationClosure.lean).

The [proof guide](docs/proof-guide.md), [dependency graph](docs/proof-graph.yaml),
and [paper/Lean correspondence](docs/paper-lean-specification.md) explain these
interfaces and their exact hypotheses.

## Corollaries

The certificate passes to [right Ore localizations](Stafford38/LocalizationCorollaries.lean).
Formal adjoint gives the [left-handed identity](Stafford38/LeftHandedCorollary.lean)
`1 = R d + S d F`. The development also proves the result for
[intrinsic differential operators](Stafford38/LocalizedDifferentialCorollaries.lean)
on polynomial coefficient localizations, including principal opens, partial
Laurent rings, and fraction rings.

The [evolutionary and tensor results](Stafford38/EvolutionaryCorollary.lean)
have an independent algebraic proof. Each potential coefficient must commute
with the chosen Weyl pair; coefficients need not commute with one another.

## Stafford 1978

J. T. Stafford, *Module structure of Weyl algebras*, Journal of the London
Mathematical Society (2) 18 (1978), 429–442, states Conjecture 3.8 on page 438.
That article is the source of the conjecture and its historical context. It
proves the conjecture for `n = 1` and for monomial `d`, not in general.

Gwyn Bellamy, *Module structure of Weyl algebras*, Journal of the London
Mathematical Society **113** (2026), no. 1, e70373,
[10.1112/jlms.70373](https://doi.org/10.1112/jlms.70373), surveys the area. Its
Section 3 states the weaker cyclicity form as Conjecture 3.4, observes that
Stafford's formulation is stronger, and reports the problem as open. That is
the state of the art this development is measured against.

This repository supplies a new proof of the general case, together with the
exact Bernstein-degree fixed-source strengthening. The literature search behind
that reading covers Stafford's article, Bellamy's survey, and the D-module and
Stacks Project sources named in the [proof guide](docs/proof-guide.md); it found
no earlier proof of Conjecture 3.8 in general. Whether the argument is genuinely
new is therefore unknown rather than established: the search was not exhaustive,
no expert has confirmed it, and priority is not claimed. Kernel verification
establishes that the Lean proof is correct, and nothing about novelty or
significance.

## Palomar

[`Challenge.lean`](Challenge.lean) states the ordinary theorem using a small
Mathlib presentation of the Weyl algebra. [`Solution.lean`](Solution.lean)
transports the substantive theorem to that presentation.
[`comparator.json`](comparator.json) compares
`Stafford38Challenge.universalStatement` with only the three permitted axioms.
The independent check uses Comparator, NanoDa, and Lean's kernel; see
[verification](docs/verification.md) for the pinned tools and sandbox boundary.

The [challenge dossier](docs/dossier/stafford38-challenge-dossier.tex) defines
every object before the statement, in the manuscript's words and in Lean's, and
lists the Challenge, the Solution and the Comparator configuration from the
repository files.

This repository is not registered with Palomar and has no Palomar ID.
[Later release actions](docs/release-runbook.md) require separate human
authorization.

## Repository ownership

| Artifact | Canonical home |
| --- | --- |
| Reusable application-independent mathematics | Public [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis), an external immutable dependency |
| Stafford-specific formal proof, interface, and reproducibility documentation | Public [stafford38-formal](https://github.com/itpplasma/stafford38-formal), this repository |
| Manuscript, bibliography, and proof-map supplement | Overleaf authority, backed up in private [stafford38-paper](https://github.com/itpplasma/stafford38-paper) |
| Research history and provenance records | Private [stafford38](https://github.com/itpplasma/stafford38) |

The formal package contains no manuscript source and uses no research archive
as a build dependency. No public paper or arXiv identifier has been assigned.

## Authorship, assistance, and license

Christopher Albert is the recorded human author and maintainer. AI systems
assisted research, Lean development, counterexamples, and review under human
direction. [Structured metadata](formalization.yaml) records the corroborated
model identifiers and the limits of that disclosure; [provenance](docs/provenance.md)
records the source and dependency revisions.

Formal code and documentation are Apache-2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE). The separate manuscript and supplements are CC BY 4.0.
Cite this repository with [CITATION.cff](CITATION.cff). Release `v1.0.0` is
archived on Zenodo: the concept DOI
[10.5281/zenodo.22390721](https://doi.org/10.5281/zenodo.22390721) always
resolves to the newest version, and
[10.5281/zenodo.22390722](https://doi.org/10.5281/zenodo.22390722) cites that
exact release.
