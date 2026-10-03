# Stafford 3.8 formal proof

For every characteristic-zero field k, every rank n, and every nonzero element d of the n-th Weyl algebra A, the development proves that there are F, R, and S in A with

```text
1 = d R + F d S.
```

The factor order is part of the theorem: 1 lies in the right ideal dA + FdA. At rank zero the algebra is the field. At positive rank the fixed-source theorem takes F to be a linear Weyl coordinate raised to the intrinsic Bernstein degree of d.

## Proof architecture

The terminal Lean proof uses one route. A symplectic change of coordinates makes d monic in one momentum variable. The proof then studies the quotient by dA + x^N dA, where x is the paired coordinate and N is the Bernstein degree. An Euler identity makes right multiplication by x surjective on this quotient. Filtered support estimates and Poisson involutivity rule out nonempty order-characteristic support; coisotropic geometry supplies the contradiction. Scalar descent and quotient triviality produce the ordered certificate.

The main and fixed-source Challenge modules state the problems independently of their proofs. Separate Solution modules prove them and do not import challenge placeholders. The fixed-source comparison identifies its intrinsic ordered-word degree with the formal Bernstein degree. Derived corollaries include right Ore localization, formal adjoints, localized differential operators, evolutionary identities, and torsion-module cyclicity.

## Verification status

A clean-checkout receipt covers the terminal theorem at source revision f6915782d2281e3d3b51011b97ace866928053b9. The recorded commands, dependency pins, build counts, and logs are in verification.md and verification-results.json; this receipt applies to its named source and configuration.

A separate source checkpoint at base `b62f8cc0663a57d2baa51e333504a57da8fb5612` passed the integrated replay: 9,123 build jobs, 206 consumer and axiom reports, 111 retained paper-linked declarations, and 37 terminal declarations. Its exact patch and scope are in the [checkpoint](docs/audits/paper-route-checkpoints/completion-cone-source-checkpoint.json). Both Challenge/Solution comparisons also passed Palomar at the earlier post-coordinate checkpoint.

The printed proof's full correspondence remains open. The canonical completion maps, tilted arc, local matrix calculation, and tangent-limit consumers are checked, conditional on their geometric inputs. The actual divisor-center and chart-overlap maps, and their generic tangent-cone assembly, still need to supply those inputs. No full-correspondence release or handover is recorded.

## Source roles

The formal repository owns the Lean declarations and verification records. Overleaf is the manuscript editing authority; pinned paper revisions provide review provenance. The research archive retains development history. The Palomar entry [PALOMAR-2026-09-05-000007, version 2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2) certifies its named theorem and source only.

See the [proof guide](docs/proof-guide.md), [definition-owner registry](docs/definition-owners.md), [proof-source provenance](docs/proof-source-provenance.md), and [paper-route status](docs/paper-route-alignment.json) for the route, canonical definitions, review inputs, and scoped evidence. The [literature index](docs/literature.md) identifies the sources used by the formal development.

## Reproducing the recorded source

Use the source revision and toolchain in the verification receipt. From that checkout:

    lake exe cache get
    lake build
    scripts/verify.sh
    scripts/bootstrap-palomar-tools.sh
    scripts/verify-palomar.sh
    scripts/verify-palomar.sh comparator-fixed-source.json

The recorded toolchain is Lean leanprover/lean4:v4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, and AlgebraicAnalysis 4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8. A new source revision needs its own verification receipt.

## Ownership and licenses

Christopher Albert is the recorded human author and maintainer. AI systems assisted research, formalization, counterexamples, and review under human direction. The formal code and documentation use Apache-2.0; the manuscript and supplements use CC BY 4.0. See LICENSE, NOTICE, and CITATION.cff. Historical release records remain attached to their original sources.
