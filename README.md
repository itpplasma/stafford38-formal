# Stafford's Conjecture 3.8 for Weyl algebras

This is a local preparation candidate. Its independent build, theorem consumers,
axiom audit, and Comparator replay passed. A fresh canonical-clone replay of
the final source bytes remains required before cutover. Its external
AlgebraicAnalysis dependency is pinned to
`2fdc928835347a2638b6c85a4bfa770e3f70ed9e`.

This repository contains a Lean proof of Stafford's Conjecture 3.8. Let
`Aₙ(k)` be the `n`th Weyl algebra over a field `k` of characteristic zero. The
main theorem states that, for every `n ≥ 0` and every nonzero `d ∈ Aₙ(k)`,
there are `F`, `R`, and `S` in `Aₙ(k)` such that

```text
1 = d R + F d S.
```

The order of the factors is part of the statement. In Lean the theorem is
[`Stafford38.universalStatement`](Stafford38/FoundationClosure.lean). Its type
is [`Stafford38.UniversalStatement`](Stafford38/Statement.lean), which
quantifies over every characteristic-zero field rather than fixing an
algebraically closed field or the complex numbers.

The repository also proves a stronger fixed-source theorem. At positive rank,
[`Stafford38.universalFixedSourceStatement`](Stafford38/FoundationClosure.lean)
chooses a linear Weyl coordinate `ℓ` and takes
`F = ℓ^(bernsteinDegree k d)`. The rank-zero case is the field case and is
handled separately. The exact statement is in
[`FixedSourceStatement.lean`](Stafford38/FixedSourceStatement.lean).

## Proof architecture

The formal proof follows eight mathematical steps. The links lead to the
modules that own the corresponding declarations.

| Step | Mathematical content | Lean endpoint |
| --- | --- | --- |
| 1 | Present `Aₙ(k)` by the standard symplectic commutator relations and fix the right-ideal statement. | [`Stafford38.WeylAlg`](Stafford38/Statement.lean), [`Stafford38.UniversalStatement`](Stafford38/Statement.lean) |
| 2 | Apply a linear symplectic change of variables so that a non-scalar `d` is monic in one momentum coordinate, with degree equal to its Bernstein degree. | [`scalar_or_normalized_symplectic_image`](Stafford38/Weyl/MonicNormalization.lean) |
| 3 | For the canonical quotient `A/(dA + xᴺdA)`, combine the positive Euler residue with right division to make right multiplication by `x` surjective. | [`positiveEulerResidue_identity`](Stafford38/Weyl/EulerResidue.lean), [`presentedCanonicalQuotient_rightMul_coordinate_surjective`](Stafford38/Weyl/EulerRemainder.lean) |
| 4 | Compare the two filtered Koszul terms at minimal support primes. Opposing length inequalities force the canonical order-characteristic support away from `x = 0`. | [`canonical_support_avoidance`](Stafford38/Characteristic/CanonicalKoszulContradiction.lean) |
| 5 | Prove the radical of the associated-graded annihilator involutive for every cyclic Weyl quotient. | [`weylAssociatedGradedRadicalInvolutivity`](Stafford38/Characteristic/GabberGlobalAssembly.lean) |
| 6 | Produce the coordinate conormal direction at infinity. The formal tangent lattice, asymptotic divisor, and projective conormal closure are explicit. | [`tangent_limit_criterion_of_directSummand`](Stafford38/Geometry/GeneralTangentLimitCriterion.lean), [`coordinate_axis_mem_projective_conormal_directions`](Stafford38/Geometry/GeneralAsymptoticConormal.lean) |
| 7 | Use fibre-conicality and Poisson stability to obtain a point above the coordinate hyperplane, then apply this general exclusion theorem to the canonical reduced support ideal. | [`exists_zero_base_coordinate_of_isFibreConical`](Stafford38/Geometry/GeneralCoisotropicSets.lean), [`algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic`](Stafford38/Geometry/GeneralCoisotropicCanonicalAdapter.lean) |
| 8 | Descend from an algebraic closure, turn empty support into membership of `1` in `dA + xᴺdA`, and undo the symplectic change of variables. | [`exists_fixedSource_certificate_of_orderCharacteristicSupport_eq_empty`](Stafford38/Characteristic/CanonicalCertificate.lean), [`universalStatement_of_canonicalSupportVanishing`](Stafford38/UniversalAssembly.lean), [`Stafford38.universalStatement`](Stafford38/FoundationClosure.lean) |

The [proof guide](docs/proof-guide.md) explains the interfaces between these
steps and records the main corollaries.

## Reproducing the formal checks

The project uses Lean `4.33.1`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and the signed 32-unit
AlgebraicAnalysis commit
`2fdc928835347a2638b6c85a4bfa770e3f70ed9e`. That public dependency passed
its package release checks and can be fetched anonymously by its exact SHA.

From a clean checkout with Lean installed through Elan:

```sh
lake exe cache get
lake build
scripts/verify.sh
```

`scripts/verify.sh` builds the theorem and every advertised consumer, runs the
key declarations with `--trust=0`, verifies dependency pins, rejects proof
holes outside the deliberate Palomar challenge, and checks that all reported
axioms belong to this set:

```text
propext
Quot.sound
Classical.choice
```

No project axiom or literature axiom is permitted in the release theorem.
Details and the final-result checklist are in
[`docs/verification.md`](docs/verification.md).

## Independent Palomar check

The Palomar package separates the public statement from its proof:

- `Challenge.lean` imports only the required Mathlib modules and contains the
  single deliberate theorem placeholder;
- `Solution.lean` imports the substantive Stafford proof and transports its
  theorem to the challenge statement;
- `comparator.json` permits only `propext`, `Quot.sound`, and
  `Classical.choice`.

The pinned bootstrap and comparison can be run with:

```sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh
```

Comparator checks that the Challenge and Solution declarations have the same
type, that the Solution uses only the permitted axioms, and that Lean's kernel
and NanoDa accept the exported proof. It does not assess novelty, exposition,
literature attribution, or manuscript fidelity.

## Corollaries

The main certificate is transported to right Ore localizations in
[`LocalizationCorollaries.lean`](Stafford38/LocalizationCorollaries.lean) and
to the left-handed identity `1 = R d + S d F` by formal adjoint in
[`LeftHandedCorollary.lean`](Stafford38/LeftHandedCorollary.lean). The
development also treats intrinsic finite-order differential operators on
polynomial localizations, Laurent rings, and fraction fields in
[`LocalizedDifferentialCorollaries.lean`](Stafford38/LocalizedDifferentialCorollaries.lean).

An independent argument for evolution operators, including the tensor product
with the first Weyl algebra, is in
[`EvolutionaryCorollary.lean`](Stafford38/EvolutionaryCorollary.lean). Its
coefficient hypotheses require each coefficient to commute with the chosen
Weyl pair; the coefficients need not commute with one another.

## Repository boundaries

This repository is intended to be the canonical home of the Stafford-specific
Lean proof, its proof documentation, and reproducibility scripts. Reusable
mathematics lives in the separately versioned
[AlgebraicAnalysis dependency](https://github.com/itpplasma/algebraic-analysis).

The mathematical paper, bibliography, figures, and proof-map supplement have
a separate private Overleaf authority. They are not duplicated here, and no
arXiv identifier has been assigned. The private
[paper repository](https://github.com/itpplasma/stafford38-paper) is the
synchronized backup; Overleaf remains authoritative. Failed routes, agent
records, reviews, and the complete research chronology remain in the private
[research repository](https://github.com/itpplasma/stafford38);
they are provenance, not build dependencies. See
[`docs/provenance.md`](docs/provenance.md).

## Verification status

The signed source revision is recorded in [provenance](docs/provenance.md).
The independent preparation build, complete consumer audit, and Comparator
replay passed. Six subsequent comment clarifications leave Lean code tokens
unchanged. Final canonical-clone replay and manuscript correspondence remain
required before cutover.

Kernel checking establishes the stated Lean theorem relative to Lean, Mathlib,
and the three standard axioms above. Independent mathematical review and any
later journal review address different questions and are recorded separately.

## Authorship and license

Christopher Albert is the human author and maintainer. Automated systems
assisted research, formalization, checking, and review under human direction;
the factual disclosure is in [`docs/provenance.md`](docs/provenance.md).

Code and formal proof documentation are licensed under Apache-2.0. The
separate manuscript and supplements are licensed CC BY 4.0 by their own
authority.
