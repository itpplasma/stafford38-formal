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

The v1.3.0 proof source at source commit `12ae3cc49152672a48a96f13994314b65ae38197` passed the complete pinned Linux verifier and all four Palomar comparator configurations. The run included a 4,475-job Lake build and strict dependency inspection of all four terminal roots with zero forbidden or unavailable dependencies. The T34, T35, T36, and T41 modules, literal trust-zero consumers, and shared main and alternative solution assemblies also passed with only the three permitted axioms. Receipts apply only to this source and its pinned configuration; they do not establish whole-paper proof correspondence.

Formal release [v1.3.0](https://github.com/itpplasma/stafford38-formal/releases/tag/v1.3.0) is archived at [10.5281/zenodo.23126868](https://doi.org/10.5281/zenodo.23126868); all 1,163 tagged files matched its Zenodo archive byte for byte. Supplementary release [v0.2.0](https://github.com/itpplasma/stafford38-supplementary/releases/tag/v0.2.0), commit `31aea05344c3fa35fb19a3ff35f7518d723e26ec`, is archived at [10.5281/zenodo.23127103](https://doi.org/10.5281/zenodo.23127103); all 24 tagged files matched. Their detailed receipts are [formal](docs/qwen-campaign/notes/T92-formal-v1.3.0-Zenodo-bytecheck-20261003.json) and [supplementary](docs/qwen-campaign/notes/T92-supplementary-v0.2.0-Zenodo-bytecheck-20261003.json).

The current selected comparison surface is `human_readable_main.tex` at paper P7 `760c68d2d79a8fd2c4b58f35f32dd90969591300`, public snapshot S7 `9f6ca3241edcf88da42a3a000f25514d105e2f30` (SHA-256 `f5699fde5961488d41fd631f67c55a4442b55001e2ba8776ebbf12bd568f5bb6`). Formal source R131 is `f9448d6307fa25aff9d9f94ce0a9c7f9b03e63ff`; its provenance correction changes no mathematics. The visible author proof and marked proposals are preserved. Main roots `Solution` and `FixedSourceSolution` follow the selected paper construction; `AlternativeSolution` and `AlternativeFixedSourceSolution` share the unchanged challenges as labeled variants. Johanna’s manuscript review and Max’s complete proof-correspondence review remain pending. The owner will resubmit R131 to Palomar after the metadata correction.

## Source roles

The formal repository owns Lean declarations and verification records. Overleaf is the manuscript editing authority; pinned paper revisions provide review provenance. The archive retains development history. The Palomar entry [PALOMAR-2026-09-05-000007, version 2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2) certifies its named theorem and source only.

See the [proof guide](docs/proof-guide.md), [definition-owner registry](docs/definition-owners.md), [proof-source provenance](docs/proof-source-provenance.md), and [paper-route status](docs/paper-route-alignment.json) for proof structure, canonical owners, review inputs, and current scope. The [literature index](docs/literature.md) identifies sources used by the development.

## Reproducing the checkpoint

Use the source revision and toolchain named in the verification receipt. From that checkout:

    lake exe cache get
    lake build
    scripts/verify.sh
    scripts/bootstrap-palomar-tools.sh
    scripts/verify-palomar.sh comparator.json
    scripts/verify-palomar.sh comparator-fixed-source.json
    scripts/verify-palomar.sh comparator-alternative.json
    scripts/verify-palomar.sh comparator-alternative-fixed-source.json

Historical terminal receipts used Lean `leanprover/lean4:v4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, and AlgebraicAnalysis `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`. The v1.3.0 proof source pins Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163`. The final candidate receipt bundle is recorded in [verification.md](docs/verification.md); each result applies only to its recorded source and configuration.

Formal [v1.3.1](https://github.com/itpplasma/stafford38-formal/releases/tag/v1.3.1), DOI [10.5281/zenodo.23127367](https://doi.org/10.5281/zenodo.23127367), matches all 1,172 files in its Zenodo archive and corrects verification provenance: the historical cbb2396 fields now link to the matching archived report, and the later completed replays have separate source scope. The proof, statements and dependency pins are unchanged; see [release notes](docs/releases/v1.3.1.md). The owner will rerun Palomar on this release.

## Ownership and licenses

Christopher Albert is the recorded human author and maintainer. AI systems assisted research, formalization, counterexamples, and review under human direction. The formal code and documentation use Apache-2.0; the manuscript and supplements use CC BY 4.0. See `LICENSE`, `NOTICE`, and `CITATION.cff`. Historical release records remain attached to their original sources.

The corrected [supplementary v0.2.1](https://doi.org/10.5281/zenodo.23127468) includes the current review ledger, matching P6/S6/R131 PDFs and corrected comparison labels. All 29 tagged files match its archive. Final P7/S7 cites both releases; the [current ledger](docs/paper-lean-audit/review-status.json) records the complete review scope and pending human approvals.
