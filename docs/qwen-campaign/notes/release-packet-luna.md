# Nonauthoritative release packet proposal

Prepared read-only for the controller from the campaign plan, ledger, provenance rule, release-resume audit, and archived templates. This file is a working proposal only. It records no accepted theorem, completed release gate, human review, publication, or DOI. The controller owns edits to authoritative state and release metadata.

## Current gate status and blockers

At the inspected `STATE.md`, T70 (frozen public source), T71–T74 (Linux replay and official Palomar), T80–T81 (map and review site), T83 (supplementary build), T84 (review handover), T90–T93 (release, archive comparison, citations) are pending. T82 is an earlier manuscript build receipt; the receipt itself requires revalidation if source changes. T51's verifier receipt and T73's Linux receipt are absent. Thus no release body can yet make final source or verification claims.

Before T90, the controller needs: accepted integration and unchanged target statement; strict dependency guard; full verifier and its axiom/consumer/import reports; frozen, pushed source commit; T73 clean replay with both comparator results; T74 official dispatch and actual Comparator artifacts; T80 map checks; T81 review-site build; final paper PDF compilation and zero undefined references; and T83 assets rebuilt from the exact final paper, formal and generator commits. Human review scopes must remain explicit and pending until Johanna and Max respond.

The formal terminal theorem receipt and paper-route correspondence are separate claims. The current provenance names `human_readable_main.tex` as the selected review surface, preserves Johanna's visible author proof and marked local proposals, and assigns Max the whole-paper and both Challenge/Solution comparisons. Neither a terminal theorem receipt nor the existing Palomar v2 entry establishes whole-proof correspondence or certifies the new source.

## Required release inputs and assets

Formal v1.3.0 source release, based on `docs/audits/paused-2026-10-02/release-preparation/PROPOSAL.md` and `docs/release-runbook.md`:

- Freeze the exact public formal commit and record it under `STATE.md` only after accepted source is pushed. Attach exact T51/T73 receipt paths and T74 dispatch/artifact identifiers. Rebuild the candidate manifest in a clean release checkout; verify the proposed Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, and AlgebraicAnalysis `bbbbf3fc358ca8100b158cec4cf47f336ab70163` pins against accepted source and the regenerated `lake-manifest.json` before retaining them.
- Finalized tracked release paths from the archived command template: `CITATION.cff`, `.zenodo.json`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and `docs/releases/v1.3.0.md`; stage only paths that actually changed. Do not rewrite historical receipts. Release body is supplied as the GitHub release notes file, not presumed to be an uploaded asset; attach any dossier or other artifact only if the runbook's final release scope includes it and its source/hash matches the freeze.
- Keep `CITATION.cff`'s concept DOI `10.5281/zenodo.22390721`; omit a v1.3.0 version DOI/date until Zenodo publication and archive verification. Keep `.zenodo.json`'s AlgebraicAnalysis v0.3.3 dependency DOI `10.5281/zenodo.23104842`; that DOI is for the dependency, never this release.

Supplementary companion proposal: preserve published/history-tagged v0.1.3 and its current draft. Propose `v0.2.0` for the new immutable snapshot, subject to controller selection and validation. No DOI is known or proposed. Build the snapshot from exact frozen paper, formal, and generator commits, then update together: `manifest.json`, `version.json`, `paper-lean-map.json`, `index.html`, `README.md`, `STATUS.md`, `.zenodo.json`, `CITATION.cff`, `SHA256SUMS`, `human_readable_main.pdf`, `lean_proof_details.pdf`, and `ESM_2.pdf`; regenerate `ESM_1.zip` from the same contents. Retain and check `NOTICE`, `LICENSES/manuscript-CC-BY-4.0.txt`, `LICENSES/generator-Apache-2.0.txt`, `LICENSES/KaTeX-MIT.txt`, and the rebuild script/locked generator inputs. Include the full file list in the final archive comparison. `scripts/rebuild.py` rebuilds/checks HTML only; it does not regenerate PDFs or `ESM_1.zip`.

The companion manifest must identify paper-origin commit, public paper snapshot, formal source commit and release DOI if assigned, generator commit, mapping version, all current asset hashes, and `zenodo_version_doi: null` before publication. Only after a zero-mismatch archive check may the controller propagate the minted companion DOI to the manifest, `.zenodo.json`, `CITATION.cff`, README/release history, formal citation draft, and manuscript citation on paper `main`; sync accepted manuscript changes to Overleaf and verify the remote head. Keep each repository's release DOI distinct. Do not invent a DOI or infer one from GitHub release creation.

## Controller checklist and command skeletons

1. Complete and record T70–T74 and T80–T84. Keep `docs/paper-route-alignment.json`'s scope/status synchronized with accepted evidence; don't upgrade human-review status based on automated checks.
2. From a clean formal checkout at `<FROZEN_FORMAL_SHA>`, rebuild/verify release metadata, inspect exact staged diffs, then sign and publish formal v1.3.0. Archived command template: `docs/audits/paused-2026-10-02/release-preparation/future-commands.sh.txt`.

```sh
git -C <FORMAL_RELEASE_CHECKOUT> diff --cached --check
git -C <FORMAL_RELEASE_CHECKOUT> diff --cached
git -C <FORMAL_RELEASE_CHECKOUT> tag -s v1.3.0 -m "Stafford38 v1.3.0"
git -C <FORMAL_RELEASE_CHECKOUT> tag -v v1.3.0
git -C <FORMAL_RELEASE_CHECKOUT> push origin v1.3.0
gh release create v1.3.0 --repo itpplasma/stafford38-formal --title "Stafford38 v1.3.0" --verify-tag --notes-file <FORMAL_RELEASE_BODY>
```

3. Prepare and verify supplementary v0.2.0 from exact final pins using `/home/ert/proj/stafford38-supplementary/docs/release-preparation.md`; run `python3 scripts/rebuild.py` in its clean snapshot, separately regenerate/check PDFs and ZIP, verify render/source links/map/layout/archive contents, and retain commands, exit codes and log hashes. Then use the selected version in the archived audit's supplementary sequence:

```sh
git -C <SUPPLEMENTARY_CHECKOUT> diff --check
git -C <SUPPLEMENTARY_CHECKOUT> diff
git -C <SUPPLEMENTARY_CHECKOUT> tag -s v0.2.0 -m "Stafford38 supplementary 0.2.0"
git -C <SUPPLEMENTARY_CHECKOUT> tag -v v0.2.0
git -C <SUPPLEMENTARY_CHECKOUT> push origin v0.2.0
gh release create v0.2.0 --repo itpplasma/stafford38-supplementary --title "Stafford38 supplementary 0.2.0" --verify-tag --notes-file <SUPPLEMENTARY_RELEASE_BODY> <verified-assets-if-needed>
```

4. For each GitHub release, obtain Zenodo record ID, archive key/filename, URL, checksum and size from the actual record API response. Download to a fresh directory; compare every archive file byte-for-byte and by SHA-256 with `git archive <immutable-tag>`, recording file counts, extras and mismatches in separate formal/supplementary receipts. Formal template commands include:

```sh
curl -fsSL "https://zenodo.org/api/records/${ZENODO_RECORD_ID}" -o <RECORD_JSON>
jq -r '.files[] | [.key, .links.self, .checksum, .size] | @tsv' <RECORD_JSON>
curl -fL "https://zenodo.org/api/records/${ZENODO_RECORD_ID}/files/${ZENODO_ARCHIVE_KEY}/content" -o <ARCHIVE_ZIP>
sha256sum <ARCHIVE_ZIP>
git -C <RELEASE_CHECKOUT> archive <IMMUTABLE_TAG> | tar -t
```

Extract safely and perform per-file byte/hash comparison; `tar -t` listing alone is not acceptance. Require zero mismatches. Record the actual DOI only after this gate. Do not move either tag; follow-up metadata/citation changes belong in later commits.
5. Complete T93 citations for formal repo, companion, and manuscript using the actual version DOIs and exact released versions. Controller applies formal/companion edits; paper citations are changed by the owner through Overleaf authority. Verify all citations point to their own release and that map/manifest/source links still target the frozen commits.
6. Only after both releases, both verified Zenodo archives, final citations and concrete T84 package exist may the controller send the requested email to Johanna and Max. Review remains pending until they respond.

## Proposed formal GitHub release body

Proposed concise body based on `docs/audits/paused-2026-10-02/release-preparation/release-body.template.md`. Replace bracketed fields only from the frozen receipt. This is not publication-ready while any field remains unresolved.

> Stafford's Conjecture 3.8 for Weyl algebras: Lean 4 formalization v1.3.0
>
> This release records the verified formal source at `<FROZEN_FORMAL_SHA>`.
>
> - Lean: `leanprover/lean4:v4.35.0-rc3`
> - Mathlib: `<VERIFIED_MATHLIB_REVISION>`
> - AlgebraicAnalysis: `<VERIFIED_AA_REVISION>` ([dependency DOI](https://doi.org/10.5281/zenodo.23104842))
> - Verification: `<T51_RECEIPT>`; replay and comparator evidence: `<T73_RECEIPT>` and `<T74_OFFICIAL_ARTIFACTS>`
> - Manuscript comparison scope/status: `<PAPER_ROUTE_ALIGNMENT_AND_HUMAN_REVIEW_STATUS>`
>
> The theorem verification and manuscript correspondence are separate review claims. The existing Palomar v2 entry covers only its recorded theorem and source. This release's Zenodo version DOI will be recorded after its archive is retrieved and compared file by file with the signed tag.
>
> Chris&AI

## Proposed supplementary GitHub release body

Proposed concise adaptation of `/home/ert/proj/stafford38-supplementary/docs/release-body-draft.md`. Do not claim whole-paper correspondence beyond the final map's explicitly reviewed scope.

> Stafford Conjecture 3.8 supplementary reviewer companion v0.2.0
>
> This release packages the review site, mapped paper, proof accounts and source manifest for the exact revisions below.
>
> - Manuscript source: `<FROZEN_PAPER_SHA>`
> - Formal source: `<FROZEN_FORMAL_SHA>` (Stafford38 v1.3.0; DOI `<FORMAL_VERSION_DOI_AFTER_VERIFICATION>`)
> - Audit generator: `<FROZEN_GENERATOR_SHA>`
> - Verification and asset receipts: `<T51_T73_T74_AND_T83_RECEIPTS>`
> - Review scope: Johanna's marked manuscript proposals and Max's full paper/Lean comparison remain pending human review.
>
> The supplementary Zenodo version DOI will be added after the published archive is compared file by file with this tag.
>
> Chris&AI

## Proposed final review email

Send only after both releases, archive checks, citations, and review package are complete. Draft follows the audited owner-requested handover and preserves separate review roles.

> Hi Johanna and Max,
>
> The updated Stafford 3.8 review materials and releases are ready. Johanna, please review the marked proposals in the Overleaf paper proof and record your decisions there. Max, please use the paper–Lean comparison tools in the supplementary bundle to compare the full paper proof with both Lean Challenge/Solution statements and proof routes. Please send me any findings or corrections.
>
> Chris&AI

## Source templates consulted

- `docs/qwen-campaign/PLAN.md`, T80–T93; `docs/qwen-campaign/STATE.md`.
- `docs/proof-source-provenance.md`.
- `docs/qwen-campaign/notes/release-resume-audit.md`.
- `docs/audits/paused-2026-10-02/release-preparation/{PROPOSAL.md,RELEASE-NOTES-PENDING.md,release-body.template.md,future-commands.sh.txt}`.
- `docs/release-runbook.md`.
- `/home/ert/proj/stafford38-supplementary/{docs/release-preparation.md,docs/release-body-draft.md,README.md,STATUS.md}`.
