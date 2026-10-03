# T81 guided review interface preparation

Status: generator UI candidate prepared; controller integration and the complete pinned-site walkthrough remain pending.

## Frozen generator input

- Generator base: `f0ce035538b4fa704109a34d14aa22265dec2a31` (`/home/ert/proj/paper-lean-audit`).
- SHA-256 of `git diff --binary HEAD`: `92314b4910efadf0c975389e0afff7d10e96015f8a04e580fb9340fdb2a26972`.
- Changed paths: `build.mjs`, `review.js`, `style.css`, `test/build-validation.test.mjs`, and `test/review.browser.test.mjs` only.
- MAIN when this note was prepared: `f40e4be74a3129e18398f8d90d4120abb692aafd`.

## Interface changes

`build.mjs` derives a stable claim sequence from the section order and each section's entry order, matching the generated page. The overview has one start link; every claim has previous/next navigation and its position in the sequence. The browser records the current claim after a guided/TOC jump or a claim finding/check edit. A resume link names that claim on the next visit.

The resume position lives in browser review state separately from each claim's checks and notes. Export/import carries it as optional `last_entry`; older review JSON without that field remains accepted. Starting over returns to the first claim. Navigation does not alter per-claim notes or checkboxes. Technical source context and supporting proof detail keep their existing collapsed presentation; statement, hypothesis, correction/gap and correspondence content remain as rendered by the selected map.

## Verification

- `npm test`: exit 0; 64 passed, 1 skipped, 65 total. The skip is the existing integration check requiring the sibling paper clone.
- The test suite ran its Chromium browser checks, including a guided walkthrough that starts at claim one, records a finding and check, advances to claim two, reloads and resumes there, exports/imports the findings and position, and confirms notes/checks persist. It also confirms Start returns to the first claim.
- The build-validation fixture checks that the generated start link, first/last position labels, previous/next targets, and initially hidden resume link match the miniature map's rendered order.
- `git diff --check`, `node --check build.mjs`, and `node --check review.js` passed.
- Environment used Node `v22.23.0` and `/usr/bin/chromium`; the generator README specifies Node 24, so the supported Node 24 runtime was not separately exercised.

## Limits and handoff

The browser walk used a two-claim synthetic fixture and the generator build-validation used independent miniature Git repositories. I did not run `scripts/build-review-site.py` against the live Stafford map or claim that the complete Max sequence, paper/source links, full map coverage, or frozen-source inputs have been accepted. T80 mapping, root-owned pins and generated paths remain prerequisites. The controller should integrate these five paths, build the exact pinned map, check generated links and gaps, and walk every claim from the start link before marking T81 accepted. The actual final review site will fingerprint the updated generator under its existing revision checks; stored notes remain available for review/export.
