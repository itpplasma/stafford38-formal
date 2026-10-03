# Paper–Lean audit tool

This browser tool helps reviewers compare a pinned manuscript with named Lean declarations. Its map records source revisions, statement scope, proof-route differences, dependencies, and review issues. Links and checks aid navigation and comparison; they do not prove arbitrary prose equivalent to Lean or provide human approval.

## Build and check

Run from this directory with Node.js and the locked dependencies:

```sh
npm ci
npm test
node build.mjs --check --paper ../../../stafford38-paper --formal ../..
CHROMIUM_PATH=/usr/bin/chromium node build.mjs --check --paper ../../../stafford38-paper --formal ../.. --pdf
```

The options --paper, --formal, --library, --global, --map, --reviews, and --out select source checkouts, map files, review exports, and output paths. Source reads use the immutable revisions in the map. Build outputs and installed dependencies are excluded from Git.

## Review workflow

Each card links the mapped statement, supporting declarations, proof steps, and source excerpts. Definitions and pattern-match branches appear where mapped. Unresolved or truncated references are marked. The review digest includes mapped inputs, so changing a relevant source or map entry makes an earlier review stale.

Reviewer notes export as JSON. Browser storage is local convenience, not a cryptographic signature or shared approval. A committed review export records a review against a source snapshot; it does not make an AI comment or correspondence badge a human sign-off. Read the card's statement and proof route before recording a judgment.

The Stafford map is a curated comparison surface. Consult the formal repository's docs/paper-route-alignment.json for its current scope and status; the map does not replace whole-proof or human review.
