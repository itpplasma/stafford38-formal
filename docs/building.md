# Building and verification

## Pins

- Lean: `leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`).
- Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e`.
- AlgebraicAnalysis: `bbbbf3fc358ca8100b158cec4cf47f336ab70163`.

The last two are set in `lakefile.toml` and resolved in
`lake-manifest.json`. Keep them unchanged unless the full verification is
rerun afterwards.

## Build

```sh
lake exe cache get
lake build
```

The default targets are `Stafford38`, `Solution` and `FixedSourceSolution`.

## Repository verifier

```sh
scripts/verify.sh
```

The verifier checks the repository layout and the comparator source policy,
runs the Python behaviour tests under `tests/`, builds every module under
`Stafford38/` together with all solution and challenge roots, and runs the
dependency guard (`scripts/dependency-guard/`) to confirm that the solution
roots use only permitted dependencies and axioms. Logs go to
`.lake/verification/`.

## Comparator replay

Each `*Challenge.lean` file states a theorem with Mathlib-only definitions and
ends in an intentional `sorry`; the matching `*Solution.lean` proves it
without importing the challenge. The four `comparator*.json` files select the
pairs. After building:

```sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh comparator.json
scripts/verify-palomar.sh comparator-fixed-source.json
scripts/verify-palomar.sh comparator-alternative.json
scripts/verify-palomar.sh comparator-alternative-fixed-source.json
```

## Earlier releases

Earlier releases used Lean `v4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` and AlgebraicAnalysis
`4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`. To reproduce a recorded result,
check out the source revision named in [verification.md](verification.md) and
use the pins of that checkout. Release notes are in [releases/](releases/).
