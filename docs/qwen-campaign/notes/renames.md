# Renames and reused declarations

Old archived name → new name in `WT` on `qwen/paper-route`. Only names that
rule 2.6 forbids, or that the namespace change forces, are listed.

## T11 — AwayFactorToAtPrime

Archived `Stafford38/Geometry/AwayFactorToAtPrime.lean` →
`Stafford38/Geometry/SameWitness/AwayFactorToAtPrime.lean`.

| Archived | New |
| --- | --- |
| `Stafford38.Geometry.AwayFactorToAtPrime.factorization_to_atPrime` | `Stafford38.Geometry.SameWitness.factorization_to_atPrime` |
| `Stafford38.Geometry.AwayFactorToAtPrime.pair_factorizations_to_atPrime` | `Stafford38.Geometry.SameWitness.pair_factorizations_to_atPrime` |

Declaration names unchanged (rule 2.6 clean); only the namespace follows the
new path. Statements are byte-identical to the archived text (`diff` of the
`theorem` signature blocks, exit 0).

Later phases import `Stafford38.Geometry.SameWitness.AwayFactorToAtPrime`
wherever the archived files said `Stafford38.Geometry.AwayFactorToAtPrime`.

Reused from Mathlib (no port needed for these):

- `IsLocalization.Away.lift` — the induced hom `Localization.Away f →+* P`.
- `IsLocalization.Away.lift_comp` — replaces the archived hand-written
  `ext b; simp [ψ]` proof that `ψ.comp (algebraMap B _) = algebraMap B _`.
  Lean needs `R`/`S`/`P`/`x` given explicitly, otherwise the
  `IsLocalization.Away ?m ?m` instance problem is stuck.
- `IsLocalization.map_units`, `IsUnit.map`, `map_mul`, `map_pow`.

No new `def`/`structure`/`abbrev`, so no `new-definitions.md` entry.
