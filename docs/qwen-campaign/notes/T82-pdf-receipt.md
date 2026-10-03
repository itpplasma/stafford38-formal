# T82 manuscript PDF rebuild receipt

Status: complete; all three builds exited 0; source hashes unchanged.

This receipt labels the exact local paper snapshot below. It does not certify a final formal release or complete paper-to-Lean correspondence. Overleaf remains the manuscript editing authority.

## Frozen inputs

- PAPER: `/Users/ert/proj/stafford38-paper`
- HEAD: `357b7d9db8e5d363a11500b301f04607654bd809`
- Initial `git status --porcelain=v1 --untracked-files=all`: `(clean)`
- Source and reference SHA-256 before compilation:
  - `human_readable_main.tex`: `fd707283bda604800400fd86cb31f9e3ab083f29a3fb8e556c230ccd83aaaa3b`
  - `lean_proof_details.tex`: `6cf5525911ae434cd9d2cf5189ab0ac7337d3260442c4618bdc5d6fda67e11f0`
  - `main.tex`: `b55ef1f254b7611b37b4bdf7633991400cdb4512bd03e0532d1f90f561cf7cbe`
  - `references.bib`: `3a67a7cbe002d13c7d4d5356be3cdeabd02dd46924223af7fc77a5019a3701d4`
  - `README.md`: `ce5d79c55cf748753dda1b3172230b631ee50aade650e250eac60ae7b320ae49`
  - `STATUS.md`: `de9d706bbff39cc005ba16e2a2e3664666d674f58274bf1e2c19a37eb118faf9`
  - `ai_review.tex`: `2caf807a9c4c7462cd6c550070fea2d3b62870d3ced57edb5cacc39a95f8029c`
  - `LICENSE.txt`: `98b6fde2693d4044dce4a071640e90bd8d250dd789d9033dbd5b77c79f389de4`
- Initial PDF SHA-256 (existing files, before compilation):
  - `human_readable_main.pdf`: `absent`
  - `lean_proof_details.pdf`: `absent`
  - `main.pdf`: `572d4daad8e791a82b116344e1f8c06b8834634e05fcb767fb457c56c47675a3`

## Commands and results

Sequential builds were run per `README.md`:

1. `cd /Users/ert/proj/stafford38-paper && latexmk -pdf human_readable_main.tex`
2. `cd /Users/ert/proj/stafford38-paper && latexmk -pdf lean_proof_details.tex`
3. `cd /Users/ert/proj/stafford38-paper && latexmk -pdf main.tex`

Build commands exited 0 in the README order above. `latexmk` reported version 4.87 (15 June 2025); pdfTeX came from TeX Live 2026. Final log inspection found zero lines containing `undefined` in each build log. No Lean-name or cross-reference warning appeared.

## Final artifact and log checks

- `human_readable_main.pdf`: 34 pages, 830239 bytes, SHA-256 `3a298f24c88642562739f73d2a58c18ad2e0fd322e7d6712f59222189cf104a9`; `human_readable_main.log` SHA-256 `3d2484519f1392da6d803919a9133244232ce99dee4b8f5e61cc9b563717cabe`; undefined lines: 0.
- `lean_proof_details.pdf`: 11 pages, 405905 bytes, SHA-256 `d99f8f88e04b14df43cb2f940a776e48b8761cd17cdeb2c12a3023287f9fb6df`; `lean_proof_details.log` SHA-256 `830a5aafb0bc16a2b166c4f9d55b60b0f1fe28901c94e182b5ea9d8f3efbc776`; undefined lines: 0.
- `main.pdf`: 34 pages, 830239 bytes, SHA-256 `6819cf8ae9e675ce79c5de9ecaa4c7992ae80f81af7ee4ad19a3579004650e26`; `main.log` SHA-256 `f9bca8208f35aba44d0e23350cba4a08faf739e86b2ac83afcecfa7fc0db9bad`; undefined lines: 0.

- Post-build source/reference SHA-256 values match the frozen values above: **true** (all eight rechecked).
- Post-build PAPER `git status --porcelain=v1 --untracked-files=all`: `(clean; generated outputs ignored)`.
- Visual inspection via rendered first/proof/end pages: first pages and sampled proof pages have readable text and equations, with no visible clipping or overlap. The selected manuscript’s final page is sparse: it has the final formal-comparison note and the Graz University of Technology affiliation. This is recorded for author/controller review; no manuscript layout or source edits were made.
- PDFs: `/Users/ert/proj/stafford38-paper/human_readable_main.pdf`, `/Users/ert/proj/stafford38-paper/lean_proof_details.pdf`, `/Users/ert/proj/stafford38-paper/main.pdf`.

