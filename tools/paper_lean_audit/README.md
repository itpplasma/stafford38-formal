# Paper and Lean audit

This generator compares the manuscript with named declarations at immutable
Git revisions. The curated map records statement scope, proof-route differences,
dependencies, and issues for review. It validates source correspondence; a
successful build does not prove that arbitrary LaTeX prose is equivalent to a
Lean proposition, or supply a human mathematical sign-off.

## Build

The formal repository includes a pinned manuscript snapshot. Run this copy of
the generator against that repository and sibling `algebraic-analysis` and
`global-stafford-formal` checkouts. The research copy may instead use the
Overleaf-synchronized `stafford38-paper` checkout.

```sh
npm ci
npm test
node build.mjs --check --paper ../.. --formal ../..
CHROMIUM_PATH=/usr/bin/chromium node build.mjs --check --paper ../.. --formal ../.. --pdf
```

Use `--paper`, `--formal`, `--library`, `--global`, `--map`, `--reviews`, and
`--out` to select other locations. Source reads use the commits in the map,
not uncommitted working-tree edits. Build outputs and installed dependencies
are excluded from Git.

## Review

Follow each card's source links, read the statement and proof route, then
record each review check under your name. Export the JSON to retain the
review. An edited statement, proof source, correspondence assessment, or
relevant pin invalidates inherited checks. Imported reviews are validated;
missing hashes and unnamed reviews do not count as sign-offs.

Commit a reviewed export under `docs/paper-lean-audit/reviews/` using the
repository's signed-commit policy. Browser storage is a convenience, and is
not a cryptographic signature or evidence of human approval by itself.

## Ownership

The Overleaf-synchronized manuscript remains the source of truth for its
prose. The formal repository owns mathematical declarations and release
verification. The research repository retains the discovery history. The
formal release includes a copy of this audit generator and its pinned map;
correspondence updates after DOI assignment do not change the released proofs.
