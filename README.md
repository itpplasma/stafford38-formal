# Stafford 3.8 formal proof

> **Human review (recorded 2 November 2026):** Johanna Moser has reviewed the mathematical prose and the marked proposals of the manuscript, and Maximilian Philipp has reviewed the paper-to-Lean correspondence (as reported by Christopher Albert). Statements below that call these reviews pending are superseded; the review ledgers record the earlier state.

A Lean 4 and Mathlib formalization of Stafford's Conjecture 3.8 for Weyl
algebras (J. T. Stafford, *Module structure of Weyl algebras*, J. London
Math. Soc. (2) 18 (1978), 429-442, p. 438).

Status: the formal proof is complete; the human reviews of the manuscript
(Johanna Moser) and of its correspondence with the Lean proof (Maximilian
Philipp) are complete.

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

- `Challenge.lean` states, with Mathlib-only definitions
  (`Stafford38/ChallengeDefinitions.lean`), the paper's results as printed:
  `Stafford38Challenge.theorem_1_1 : PaperTheorem_1_1` (Theorem 1.1:
  `Aₙ(k) = dAₙ(k) + FdAₙ(k)`, equivalently `1 = dR + FdS`, and for `n ≥ 1`
  `F = Φ_g⁻¹(x₁)^{deg_B d}` for a linear `ω`-preserving `g`),
  `Stafford38Challenge.corollary_6_3 : PaperCorollary_6_3` (every finitely
  generated torsion right `Aₙ(k)`-module is cyclic), and the identity form
  `Stafford38Challenge.universalStatement` above.
- `Stafford38FixedSourceChallenge.universalFixedSourceStatement`
  (`FixedSourceChallenge.lean`): the fixed-source form with the intrinsic
  Bernstein degree.
- `Solution.lean` and `FixedSourceSolution.lean` prove these through
  `Stafford38.Paper.theorem_1_1`, `Stafford38.Paper.theorem_1_1_fixedSource`
  and `Stafford38.Paper.corollary_6_3` (`Stafford38/Paper/Main.lean`): the
  proof along the paper's Sections 2–6, one Lean declaration per numbered
  statement and per paragraph of its printed proof.
- `AlternativeSolution.lean` and `AlternativeFixedSourceSolution.lean` prove
  the same statements through the earlier route (`Stafford38.universalStatement`,
  `Stafford38.universalFixedSourceStatement`,
  `Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion`).
  Both use the equivalences of `Stafford38/ChallengeBridge.lean`.
- Related results in `Stafford38/`: right Ore localization, formal adjoints,
  differential operators on polynomial localizations, evolutionary identities,
  torsion-module cyclicity, and the tangent-limit, asymptotic-conormal and
  coisotropic-exclusion theorems used by the proof.

The project contains no `axiom` declarations. The only `sorry`s are the
intentional placeholders in `Challenge.lean` (three) and
`FixedSourceChallenge.lean` (one), which state the theorems for independent
comparison against the solutions.
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
