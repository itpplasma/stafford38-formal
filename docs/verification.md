# Verification

The independent clone of commit `219668ef77b4ffddc1a503fd1ce61dbd48aa4b17` passed the checks recorded
in the [machine-readable report](verification-results.json):
`df7c23125820af9a23e8c2f01e4fa9873341f2d29be6dc46eb833180d183166a`. The report fixes the source commit, dependency pins,
tool revisions, commands, exit statuses, and evidence hashes. Kernel checking
and independent human mathematical review are separate assessments.

## Logical scope

The universal certificate, exact-degree strengthening, general geometric
theorems, and advertised corollaries use only `propext`, `Classical.choice`,
and `Quot.sound`. The audited declarations contain no project or literature
axioms, proof placeholders, or `Lean.ofReduceBool` dependency.

The ordinary result quantifies over every characteristic-zero field and all
ranks, including zero. The fixed-source result specifies the exact Bernstein
degree at positive rank. The geometric scope includes the tangent-limit
criterion, arbitrary relevant affine asymptotic conormals, component conormal
containment, and exclusion for closed fibre-conical coisotropic sets. Their
precise hypotheses are recorded in the [statement correspondence](paper-lean-specification.md).

## Reproduction

From the selected commit with Elan and the build tools installed:

```sh
lake exe cache get
lake build
scripts/verify.sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh
```

| Component | Pin |
| --- | --- |
| Project Lean | `leanprover/lean4:v4.33.1`, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`) |
| AlgebraicAnalysis | `2fdc928835347a2638b6c85a4bfa770e3f70ed9e` |

AlgebraicAnalysis is fetched from its public Git repository. Its source is
external to this package and subject to the same foundational-axiom boundary.
The build needs neither the private research repository nor the paper mirror.
Generated logs and tool builds remain under `.lake/` and are excluded from Git.

## Theorem and consumer gates

[`scripts/verify.sh`](../scripts/verify.sh) resolves every source import against
the checkout, Lean core, or its pinned dependencies. It builds every retained
Stafford module and the aggregate theorem, checks pins, scans for proof holes,
and audits 19 exact endpoint reports under `--trust=0`:

| Group | Reports |
| --- | --- |
| Universal and exact-degree theorems | 2 |
| Ore localization, formal adjoint, four intrinsic differential-operator results, and two evolutionary results | 8 |
| Tangent limit, asymptotic conormal, component containment, coisotropic exclusion, and canonical application | 5 |
| Independent tangent/coisotropic consumers and the involutive/non-Poisson negative control | 4 |

The separate [`check-consumers.sh`](../scripts/check-consumers.sh) is a required
step of that verifier. Its nine axiom reports come from literal statements in
[`CorollaryConsumer.lean`](../tests/CorollaryConsumer.lean) and
[`LocalizedDifferentialConsumer.lean`](../tests/LocalizedDifferentialConsumer.lean).
They check the exact exponent, multiplication order, Ore transport, potential
coefficient hypotheses, and actual intrinsic differential-operator types.

Two finite regression oracles supply independent computational checks:
1,792 filtered-page kernel/cokernel cases and 252 PBW projection cases, including
a wrong-sign control. These examples check behavior; the universal results
are established by their Lean proofs.

## Import separation and sandbox

[`check-import-closure.sh`](../scripts/check-import-closure.sh) asks Lean for
`env.header.moduleNames`, so it checks the actual loaded transitive environment.
The Challenge permits Lean core and the pinned Mathlib dependency closure,
and excludes Stafford and AlgebraicAnalysis. The Solution excludes Challenge.
The exact loaded-module counts are in the verification report.

The only deliberate proof placeholder is in [`Challenge.lean`](../Challenge.lean).
Its Weyl presentation uses `FreeAlgebra`, `RingQuot`, and the standard
symplectic matrix. [`Solution.lean`](../Solution.lean) transports the proved
Stafford theorem by an algebra equivalence.

Comparator exports and compares `Stafford38Challenge.universalStatement` in
separate environments, checks the permitted axioms, and submits the exported
proof to both NanoDa and Lean's default kernel. Its subprocesses use Landrun's
restricted sandbox. The adapted [wrapper](../scripts/landrun-wrapper.sh)
preserves a single outer command delimiter and rejects unrestricted flags.
The adaptation and upstream license are recorded in [NOTICE](../NOTICE).

## Verification tools

| Tool | Source revision | Build toolchain |
| --- | --- | --- |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` | Lean `4.34.0-rc1`, as fixed by its repository |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` | Project Lean `4.33.1` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` | Rust, locked Cargo dependencies |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` | Go, readonly module resolution |

The bootstrap builds these exact source revisions. Comparator's own Lean
version differs from the project/exporter version because its kernel API
requires that version. Palomar's documented stable-patch selection gives the
listed exporter revision for project Lean `4.33.1`.

## Source regression and review

The signed private source commit
`8cc7802cd4355d819d2df4f680ba26d4a339f80e` passed its full 229-checker
manuscript regression. That record supports extraction provenance; the
independent canonical-clone result above verifies this repository's own files.

The [paper/Lean specification](paper-lean-specification.md) records the
statement mapping. Automated and scoped agent reviews do not establish
independent human expert approval, journal acceptance, novelty, or priority.
Those statuses require their own human review records. Palomar registration
and all public release actions require separate authorization.
