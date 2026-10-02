# Stafford 3.8 formal proof

For every characteristic-zero field `k`, rank `n`, and nonzero element `d` of the `n`th Weyl algebra `A`, the development proves that there are `F`, `R`, and `S` in `A` such that

```text
1 = d R + F d S.
```

The order is part of the result: `1` lies in the right ideal `dA + FdA`. At rank zero the algebra is the field. The fixed-source theorem chooses `F` as a linear Weyl coordinate raised to the intrinsic Bernstein degree of `d`.

## Formal proof

The terminal proof first changes symplectic coordinates so that `d` is monic in one momentum variable. It studies the quotient by `dA + x^N dA`, where `x` is the paired coordinate and `N` is the Bernstein degree. An Euler identity gives surjectivity of right multiplication by `x`. Filtered support estimates and Poisson involutivity constrain the characteristic variety; the coisotropic-exclusion argument yields the contradiction. Scalar descent and quotient triviality assemble the ordered certificate.

`ChallengeDefinitions` owns the problem statements and the single-element certificate predicate. The separate `Solution` modules prove those statements and do not import challenge placeholders. The fixed-source comparison connects intrinsic word degree to formal Bernstein degree. Derived results include right Ore localization, formal adjoints, localized differential operators, evolutionary identities, and torsion-module cyclicity.

## Verification and scope

Verification receipts apply to the exact source revisions and configurations they name. The prior terminal-proof checkpoint is linked from the [route record](docs/paper-route-alignment.json); it is not a verification claim about every later source edit, and its job counts are omitted here.

The current same-witness work has scoped green evidence for the frozen ground-point completion output and the selected-normalization formally-etale core. The existing `ActualPointAxisLift.exists_actual_point_axis_lift` is checked under its explicit ground-point, formally-etale, order, and chart inputs. The common-open direct-summand adapter and affine conormal endpoint are also checked under their stated column, smoothness, and closure inputs. The unconditional same-witness closure assembly and its original-prime endpoint remain open, so these components do not yet establish full manuscript correspondence or a new release.

The main and fixed-source Challenge/Solution comparisons passed Palomar at an earlier post-coordinate checkpoint; a new-release comparison remains required. The Palomar entry certifies its named theorem and source only.

## Source roles

The formal repository owns Lean declarations and verification records. Overleaf is the manuscript editing authority; pinned paper revisions provide review provenance. The archive retains development history. The Palomar entry [PALOMAR-2026-09-05-000007, version 2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2) certifies its named theorem and source only.

See the [proof guide](docs/proof-guide.md), [definition-owner registry](docs/definition-owners.md), [proof-source provenance](docs/proof-source-provenance.md), and [paper-route status](docs/paper-route-alignment.json) for proof structure, canonical owners, review inputs, and current scope. The [literature index](docs/literature.md) identifies sources used by the development.

## Reproducing the checkpoint

Use the source revision and toolchain named in the verification receipt. From that checkout:

    lake exe cache get
    lake build
    scripts/verify.sh
    scripts/bootstrap-palomar-tools.sh
    scripts/verify-palomar.sh
    scripts/verify-palomar.sh comparator-fixed-source.json

Historical terminal receipts used Lean `leanprover/lean4:v4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, and AlgebraicAnalysis `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`. The current paused checkpoint pins Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163`. Its retained baseline and consumer receipts are described in [STATUS.md](STATUS.md); full combined verification and current Palomar qualification remain pending. Each receipt applies only to its recorded source.

## Ownership and licenses

Christopher Albert is the recorded human author and maintainer. AI systems assisted research, formalization, counterexamples, and review under human direction. The formal code and documentation use Apache-2.0; the manuscript and supplements use CC BY 4.0. See `LICENSE`, `NOTICE`, and `CITATION.cff`. Historical release records remain attached to their original sources.
