# Stafford 3.8 formal proof

A Lean 4 and Mathlib formalization of Stafford's Conjecture 3.8 for Weyl
algebras (J. T. Stafford, *Module structure of Weyl algebras*, J. London
Math. Soc. (2) 18 (1978), 429-442, p. 438), following the proof of the
accompanying manuscript.

## The theorem

For every field `k` of characteristic zero, every rank `n >= 0` and every
nonzero `d` in the `n`th Weyl algebra `A = Aₙ(k)`, there are `F, R, S ∈ A`
with

```text
1 = d R + F d S.
```

The factor order is part of the statement: `1` lies in the right ideal
`dA + FdA`. (The printed conjecture omits `d ≠ 0`, which the surrounding text
assumes.) At rank zero `A` is the field. The fixed-source strengthening takes
`F = ℓ^N` for a linear Weyl coordinate `ℓ` and `N` the Bernstein degree of
`d`.

## Compared theorems

`Challenge.lean` states the results with Mathlib-only definitions
(`Stafford38/ChallengeDefinitions.lean`, `Stafford38/PaperClaimDefinitions.lean`);
each compared theorem there ends in a deliberate `sorry`. Comparator checks
these statements against the solution modules:

- `Stafford38Challenge.theorem_1_1 : PaperTheorem_1_1`, Theorem 1.1 of the
  manuscript as printed: `Aₙ(k) = dAₙ(k) + FdAₙ(k)`, equivalently
  `1 = dR + FdS`, and for `n ≥ 1` `F = Φ_g⁻¹(x₁)^{deg_B d}` for a linear
  `ω`-preserving `g`; and its identity form
  `Stafford38Challenge.universalStatement`.
- `Stafford38Challenge.corollary_6_3 : PaperCorollary_6_3`: every finitely
  generated torsion right `Aₙ(k)`-module is cyclic; and
  `Stafford38Challenge.corollary_6_3_stablyCyclic`: every such module is
  stably cyclic in Stafford's sense.
- The consequences of Section 7: the left-handed identity `1 = Rd + SdF`
  (`leftHandedIdentity`), Corollary 6.3 for left torsion modules
  (`corollary_6_3_left`), the identity for differential operators on
  localizations of `k[x₁, ..., xₙ]` (`localizedDifferentialIdentity`, with the
  principal-open, Laurent and fraction-field cases), and the identity with
  `F = x^r` for evolutionary operators (`evolutionaryIdentity`).
- `Stafford38FixedSourceChallenge.universalFixedSourceStatement`
  (`FixedSourceChallenge.lean`): the fixed-source form with the intrinsic
  Bernstein degree.

`Solution.lean` and `FixedSourceSolution.lean` prove these through
`Stafford38.Paper.theorem_1_1`, `Stafford38.Paper.theorem_1_1_fixedSource`,
`Stafford38.Paper.corollary_6_3` (`Stafford38/Paper/Main.lean`), the proof
along the manuscript's Sections 2–6 with one Lean declaration per numbered
statement and per paragraph of its printed proof, and the Section 7
consequences through `Stafford38.Paper.Section7`. `AlternativeSolution.lean` and `AlternativeFixedSourceSolution.lean`
prove the identity, Theorem 1.1, Corollary 6.3 and the fixed-source form along
an earlier route (`Stafford38.universalStatement`,
`Stafford38.universalFixedSourceStatement`). The four `comparator*.json` files
select the pairs.

The project contains no `axiom` declarations, and the only `sorry`s are the
placeholders of the compared theorems in `Challenge.lean` and
`FixedSourceChallenge.lean`. The verifier checks that the solution endpoints
depend only on `propext`, `Classical.choice` and `Quot.sound`, including
through the AlgebraicAnalysis dependency.

The proof normalizes `d` to be monic in one momentum variable, studies the
quotient `A/(dA + x^N dA)`, and excludes nonempty characteristic support using
filtered length estimates, Poisson involutivity (a formal Gabber argument) and
coisotropic geometry. The [proof guide](docs/proof-guide.md) gives the steps.

## Building and checking

Requires [elan](https://github.com/leanprover/elan). `lean-toolchain` pins
the Lean version; `lakefile.toml` pins Mathlib and
[AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis).

```sh
lake exe cache get
lake build
scripts/verify.sh
```

`lake build` builds `Stafford38`, `Solution` and `FixedSourceSolution`.
`scripts/verify.sh` builds every module and all solution roots and runs the
dependency, route, axiom and consumer checks. Comparator replay of the four
challenge/solution pairs is described in [docs/building.md](docs/building.md).

## Documentation

- [Proof guide](docs/proof-guide.md): structure of the formal proof.
- [Statement correspondence](docs/paper-lean-specification.md): manuscript
  objects and their Lean definitions.
- [Paper-route map](docs/paper-route-alignment.json): manuscript claims linked
  to Lean declarations, with the route differences.
- [Definition owners](docs/definition-owners.md): where shared objects are
  defined.
- [Building and verification](docs/building.md).
- [Literature](docs/literature.md).
- [Paper and Lean side by side](https://itpplasma.github.io/stafford38-supplementary/)
  ([stafford38-supplementary](https://github.com/itpplasma/stafford38-supplementary)).

The theorem is in the Palomar registry as
[PALOMAR-2026-09-05-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007).

## Related projects

- [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis):
  Lean library this proof depends on.
- [symplectic-stafford-formal](https://github.com/itpplasma/symplectic-stafford-formal):
  generalization to simple filtered algebras.

## Citing and license

Release metadata and DOIs are in [CITATION.cff](CITATION.cff). Christopher
Albert is the author and maintainer; AI systems assisted with research and
formalization under his direction. Code and documentation are licensed under
Apache-2.0 ([LICENSE](LICENSE), [NOTICE](NOTICE)).
