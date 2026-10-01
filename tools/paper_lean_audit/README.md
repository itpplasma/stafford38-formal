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


## What the Lean panel shows

Theorems and lemmas show their full signatures, with proof bodies linked at the
pinned revision. Definitions include their bodies and pattern-match branches.
Named result predicates are resolved through enclosing namespaces in mapped
source files; `expands` can list exact repository/file/name references when a
predicate is imported under another namespace. Their source excerpts appear
beside the theorem, and enter its review hash and reverse index. Unresolved
named results and truncated excerpts are explicitly marked. This source view
is not a kernel-generated semantic unfolding.

Each card explains whether it displays a theorem, notation/definitions only,
or no mapped declaration. Supporting and proof-step signatures can be opened
without leaving the card. Historical issue status is retained; an AI comment
addressing an issue is linked without treating it as human approval.


## Full display review

The panel includes scoped variables, local instance signatures, notation and
plain open declarations with source links. Named-result expansion respects
parameter shadowing and plain open scopes; ambiguous duplicate FQNs require
an explicit file-pinned `expands` entry. Complex open/renaming syntax and
imported instances remain in the linked full module rather than guessed.
The review digest includes the generator, review rubric and relation vocabulary.
Excerpt checks reject split markup; a child excerpt wholly in a replacement
inherits its addition style and is explicitly marked as proposed.

Standard Mathlib length definitions use `--mathlib DIR` (default: the formal
repository lake package) and its exact pinned commit in the map. Repository
and revision labels belong to each declaration, including external libraries.

## Current publication review

Use https://itpplasma.github.io/stafford38-formal/ for the current paper and source pins. The default queue has 23 publication claims; six optional routes are separate. Start with the proved Challenge/Solution endpoints and the 31 curated definitions (including Field, CharZero, the quotient relations and intrinsic Bernstein degree). Click linked identifiers to open definitions and source parents. Direct dependency links reveal only the requested reference; they do not require reviewing every reference card.

The reusable Apache-2.0 generator now lives at https://github.com/itpplasma/paper-lean-audit . This embedded copy keeps existing paper builds reproducible. The frozen companion at https://github.com/itpplasma/stafford38-supplementary keeps manuscript content separate from software. Both new Zenodo integrations must be enabled before publishing their prepared releases; no DOI is claimed until archival succeeds.
