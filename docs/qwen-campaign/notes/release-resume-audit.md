# T70–T93 release and review prerequisites audit

Read-only audit prepared for the controller. No release, tag, build, upload,
Overleaf push, workflow dispatch, commit, or remote update was performed.

## Frozen audit inputs

| Repository/input | Exact revision or digest | State |
| --- | --- | --- |
| formal controller checkout | `3214f5c8f336de67d3e90af0594f420a41e9056b` | `main`; one unrelated untracked `docs/qwen-campaign/cluster-guard.py` |
| formal `PLAN.md` | SHA-256 `b55360e7f1b408356bff72cf70430af982bcb61b69210c6de37cad5cdf05e5fa` | T70–T93 and release runbook inspected |
| formal `STATE.md` | SHA-256 `b4197a677d625f14b5700f4f1a806b10c866e477e455ed35a99606c75bab2f46` | T70 owner gate is not done; “Frozen commit” is empty; T71–T73 todo, T74 owner gate, T80–T81 todo, T82 historical receipt only, T83 todo, T84 owner gate, T90 todo, T91 owner gate, T92–T93 todo |
| formal provenance | SHA-256 `6a3439d839c77425228a31bd5e9079dbc9ee686d1b0efaa670e942b3fe5b06cc` | selected paper and formal claims remain distinct |
| formal release runbook | SHA-256 `d5e49778c3f380cd6b523597c6c62875fa7947524bd3708505e652b2e1f788c0` | clean verified source, signed immutable tag, archive comparison, DOI only after publication/verification |
| formal release command template | SHA-256 `f6cd1cbaf99dde975e137c4ab928e254055cbc192527c835f7d71f0b26572f0b` | `docs/audits/paused-2026-10-02/release-preparation/future-commands.sh.txt` |
| supplementary checkout | `25f23c1a3e7db42be894d2e95db30591691e33af` | clean `main`, tracks `origin/main` |
| supplementary release instructions | SHA-256 `6c8884cdffbe8b095ae3674b96367f4671f4497c53303e0f5383fbdcbfe581f4` | `docs/release-preparation.md`; immutable new snapshot is pending |
| paper checkout | `53882beb19c1491c43867fa78ee3b5bba3f18169` | clean `main`, tracks `github/main`; also has `overleaf` remote |

The current manuscript inputs at the paper checkout have SHA-256:
`human_readable_main.tex` `fd707283bda604800400fd86cb31f9e3ab083f29a3fb8e556c230ccd83aaaa3b`,
`lean_proof_details.tex` `6cf5525911ae434cd9d2cf5189ab0ac7337d3260442c4618bdc5d6fda67e11f0`,
and `main.tex` `b55ef1f254b7611b37b4bdf7633991400cdb4512bd03e0532d1f90f561cf7cbe`.
The current supplementary `manifest.json` is SHA-256
`2d373dfcaa62e126da1d6571f0785e07817ddfb3b92e595f2dfcc9aa25cb508d` and still
declares version `0.1.3`, formal source `ba18817c4cd4e5cfeab11da44ce76623f4c2b508`
(v1.2.3), and `zenodo_version_doi: null`. Its map and PDFs are likewise the
historical bundle. Current supplementary assets are not release-ready evidence:
`ESM_1.zip` SHA-256 `6dc8032017b45f29ffc72a8d2089e3bad4530767e54e9401f56724f4fd579c46`,
`ESM_2.pdf` SHA-256 `ebaa365c139e283d7b5f909f113ec97f7c11479d4bfc64f6444ae003cc357658`.

## Release blockers and required evidence

1. **Freeze one accepted public formal source.** Complete integration, full
   verifier, proof/source map checks, Linux replay and both Comparator runs;
   record the public commit under `STATE.md` “Frozen commit” only after the
   accepted commit is pushed. Current formal `main` is an audit base, not that
   freeze. T51 and T73 receipts are absent; the existing T82 receipt validates
   earlier source inputs only and says final-source changes require revalidation.
2. **Review package and supplementary assets.** Complete T80/T81 and the final
   manuscript checks; perform T83 from the exact frozen paper, formal and
   generator commits. `scripts/rebuild.py` rebuilds/checks HTML against pins,
   but does not rebuild PDFs or `ESM_1.zip`; those need matching regenerated
   artifacts, hashes, and source-link/layout/archive checks. The old bundle is
   explicitly identified as historical and must not be retagged or reused.
3. **Select supplementary version/tag.** The supplementary preparation does
   not name a next version or provide a release command script. The controller
   must select the version, finish metadata/body/assets at that snapshot, and
   validate the candidate. Its current `v0.1.3` is a published Git tag but the
   GitHub release is a draft for the historical bundle. Do not overwrite it.
4. **Prepare formal v1.3.0 only after gates.** The archived proposal identifies
   v1.3.0 and proposed dependency pins, but requires the final verified source
   and exact T51/T73 receipts first. Its proposal says regenerate and verify
   `lake-manifest.json` in the release checkout; no candidate metadata is itself
   authorization to promote the pins or make a release claim.
5. **Zenodo.** Supplementary preparation records owner confirmation that GitHub
   integration is enabled, while its account setting is not publicly
   inspectable. No public companion version DOI exists. For each new release,
   obtain the actual record id, archive key/filename and URL after publication;
   compare every file with the corresponding immutable Git tag. Record counts,
   extras and mismatches, and write the version DOI only after a zero-mismatch
   result. Do not infer or reuse the existing formal DOI as a new version DOI.
6. **Palomar.** Existing Palomar v2 covers only its recorded theorem/source.
   T74 must use the official dispatch contract after local and Linux checks.
   The formal workflow `.github/workflows/palomar-preflight.yml` dispatch takes
   the immutable full commit and the authorization relationship; its workflow
   description says this is a preflight and does not register a new entry.
   Capture both Comparator artifacts and dispatch details; do not call local
   evidence an official registry result.
7. **Overleaf and handover.** Overleaf remains manuscript authority. The
   historical restoration `bd913a381b714fd8f909159a33fe845b5373ba0f` is recorded
   as pushed to Overleaf, but the final release-time citation/map synchronization
   remains pending. After T92/T93, the owner must sync accepted manuscript
   citation/map changes on the paper `main` branch to the `overleaf` remote,
   then verify the remote head matches the intended paper commit. T84 package
   and short email to Johanna Moser and Max must identify Johanna’s marked
   Overleaf proof review and Max’s full paper/Lean comparison tooling, with
   review still pending until each reports back.

## Commands and available credentials

Formal release template (run only in the frozen formal release checkout after
the gates):

```sh
git diff --cached --check
git diff --cached
git tag -s v1.3.0 -m "Stafford38 v1.3.0"
git tag -v v1.3.0
git push origin v1.3.0
gh release create v1.3.0 --repo itpplasma/stafford38-formal --title "Stafford38 v1.3.0" --verify-tag --notes-file /path/to/final-release-body.md
```

The preceding template stages only finalized `CITATION.cff`, `.zenodo.json`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and
`docs/releases/v1.3.0.md` (excluding unchanged paths), then commits them. Use
the actual final release body and source receipt; no placeholders may remain.
The follow-up archive commands in that template fetch record JSON and archive
content by returned record id/key, then checksum and compare the unpacked tree
against the signed tag. Preserve the tag and DOI provenance in subsequent
metadata commits.

Supplementary release command sequence after T83 and review:

```sh
git -C /home/ert/proj/stafford38-supplementary diff --check
git -C /home/ert/proj/stafford38-supplementary diff
git -C /home/ert/proj/stafford38-supplementary tag -s <selected-version-tag> -m "Stafford38 supplementary <selected-version>"
git -C /home/ert/proj/stafford38-supplementary tag -v <selected-version-tag>
git -C /home/ert/proj/stafford38-supplementary push origin <selected-version-tag>
gh release create <selected-version-tag> --repo itpplasma/stafford38-supplementary --title "Stafford38 supplementary <selected-version>" --verify-tag --notes-file <final-supplementary-release-body>
```

This is a command outline, not a tested repository script; the version,
finalized metadata paths, body and any assets must be selected from the
verified T83 snapshot. Its `.github/workflows/pages.yml` publishes Pages on
main pushes or manual dispatch only; it is not the Zenodo release workflow.
After GitHub publication, follow formal T92’s safe-download/file-hash
comparison procedure against the supplementary tag as well.

Read-only availability checks: `gh auth status` succeeded; Git has a configured
SSH signing format/key, `ssh-add -l` reports an available identity, and the
existing formal `v1.2.3` and supplementary `v0.1.3` signatures both verify.
These checks do not establish write permission to both GitHub repositories,
Palomar dispatch permission, Zenodo access, or Overleaf push permission. No
Zenodo, Palomar or Overleaf credential variable was found by name; an unrelated
Hugging Face token variable exists. Credential values were neither read nor
recorded. `gh release list` showed formal v1.2.3 as latest and supplementary
v0.1.3 as Draft.

## Final review email prerequisite

Do not send until both repositories have their new signed releases, archive
checks pass, citations are finalized, and T84 review materials are concrete.
Suggested short body, to be signed `Chris&AI`:

> Hi Johanna and Max,
>
> The updated Stafford 3.8 review materials and releases are ready. Johanna,
> please review the AI-marked proposals in the Overleaf paper proof and leave
> your decisions there. Max, please use the paper–Lean comparison tools in the
> supplementary review bundle to compare the full paper proof with both Lean
> Challenge/Solution statements and proof routes. Please send me any findings
> or corrections.
>
> Chris&AI

