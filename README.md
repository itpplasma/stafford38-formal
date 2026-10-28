# Stafford 3.8 formal proof

A Lean 4 and Mathlib formalization of Stafford's Conjecture 3.8 for Weyl
algebras (J. T. Stafford, *Module structure of Weyl algebras*, J. London
Math. Soc. (2) 18 (1978), 429-442, p. 438).

Status: the formal proof is complete; human review of the correspondence
between the manuscript and the Lean proof is still pending.

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

## What is formalized

- `Stafford38Challenge.universalStatement` (`Challenge.lean`, proved in
  `Solution.lean`): the theorem above, stated with Mathlib-only definitions.
- `Stafford38FixedSourceChallenge.universalFixedSourceStatement`
  (`FixedSourceChallenge.lean`, proved in `FixedSourceSolution.lean`): the
  fixed-source form with the intrinsic Bernstein degree.
- `AlternativeSolution.lean` and `AlternativeFixedSourceSolution.lean`: the
  same two statements proved along an alternative route.
- Related results in `Stafford38/`: right Ore localization, formal adjoints,
  differential operators on polynomial localizations, evolutionary identities,
  torsion-module cyclicity, and the tangent-limit, asymptotic-conormal and
  coisotropic-exclusion theorems used by the proof.

The project contains no `axiom` declarations. The only two `sorry`s are the
intentional placeholders in `Challenge.lean` and `FixedSourceChallenge.lean`,
which state the theorems for independent comparison against the solutions.
The verifier checks that the solution endpoints depend only on `propext`,
`Classical.choice` and `Quot.sound`, including through the AlgebraicAnalysis
dependency.

The proof normalizes `d` to be monic in one momentum variable, studies the
quotient `A/(dA + x^N dA)`, and excludes nonempty characteristic support using
filtered length estimates, Poisson involutivity (a formal Gabber argument) and
coisotropic geometry. The [proof guide](docs/proof-guide.md) gives the steps.

## Building and checking

Requires [elan](https://github.com/leanprover/elan). `lean-toolchain` pins
`leanprover/lean4:v4.35.0-rc3`; `lakefile.toml` pins Mathlib and
[AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis).

```sh
lake exe cache get
lake build
scripts/verify.sh
```

`lake build` builds `Stafford38`, `Solution` and `FixedSourceSolution`.
`scripts/verify.sh` builds every module and all solution roots and runs the
dependency, axiom and consumer checks. Comparator replay of the four
challenge/solution pairs is described in [docs/building.md](docs/building.md).

## Documentation

- [Proof guide](docs/proof-guide.md): structure of the formal proof.
- [Definition owners](docs/definition-owners.md): where shared objects are
  defined.
- [Paper-route map](docs/paper-route-alignment.json): manuscript claims linked
  to Lean declarations, with recorded route differences.
- [Building and verification](docs/building.md) and the
  [verification record](docs/verification.md).
- [Literature](docs/literature.md).
- [Paper and Lean side by side](https://itpplasma.github.io/stafford38-supplementary/)
  ([stafford38-supplementary](https://github.com/itpplasma/stafford38-supplementary)).

The theorem is registered in the Palomar registry as
[PALOMAR-2026-09-05-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=3).

## Related projects

- [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis):
  Lean library this proof depends on.
- [symplectic-stafford-formal](https://github.com/itpplasma/symplectic-stafford-formal):
  generalization to simple filtered algebras.

## Citing and license

Release metadata and DOIs are in [CITATION.cff](CITATION.cff). Christopher
Albert is the author and maintainer; AI systems assisted with research,
formalization and review under his direction. Code and documentation are
licensed under Apache-2.0 ([LICENSE](LICENSE), [NOTICE](NOTICE)).
