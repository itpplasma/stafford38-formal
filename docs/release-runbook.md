# Human release runbook

These are instructions for later human-authorized actions. They do not grant
authorization to change visibility, publish tags or deposits, register with
Palomar, upload to arXiv, or submit to a journal. Independent expert review and
the author's release decision remain separate from the machine checks.

## Select the verified snapshot

Use a Bash terminal in the canonical formal checkout. The independently
checked proof snapshot is `79188b4b6c1ca7d21a50d6e965d0fb070f69b3d7`, recorded
in the [verification report](verification-results.json) as
`96de78e238a25ca62f7e5c18f51e360c77bf49a2daa8b8f81d862e10e897becf`. Select the final metadata-bearing HEAD for release,
not the earlier snapshot's descriptive metadata. Its proof, build, and verifier
bytes must be identical to that checked snapshot, and the latest authorized
external release receipt must approve the exact selected HEAD. This avoids
embedding a commit's own hash in its contents.

```bash
proof_commit='79188b4b6c1ca7d21a50d6e965d0fb070f69b3d7'
formal_commit=$(git rev-parse HEAD)
aa_commit='dfdd2da091a9d67e7a29cc7914f192d746a2400d'
paper_commit='b3f3edf0741b6a70b6e5011690e16bf58561cffb'
[[ "$formal_commit" =~ ^[0-9a-f]{40}$ ]] || exit 1
git fetch origin
git verify-commit "$formal_commit"
git merge-base --is-ancestor "$proof_commit" "$formal_commit"
git merge-base --is-ancestor "$formal_commit" origin/main
test -z "$(git status --porcelain)"
git diff --exit-code "$proof_commit" "$formal_commit" -- . \
  ':(exclude)README.md' ':(exclude)CITATION.cff' ':(exclude)NOTICE' \
  ':(exclude)formalization.yaml' ':(exclude)docs/**'
read -r -p 'Latest authorized external release receipt: ' release_receipt
python3 - "$release_receipt" "$formal_commit" <<'PY'
import hashlib
import json
import sys
from pathlib import Path
receipt = json.loads(Path(sys.argv[1]).read_text())
assert receipt['formal_commit'] == sys.argv[2], 'Receipt does not select HEAD'
for name in ('formal', 'isolation', 'comparator'):
    check = receipt['verification'][name]
    assert check['status'] == 'passed' and check['commit'] == sys.argv[2]
    assert hashlib.sha256(Path(check['artifact']).read_bytes()).hexdigest() == check['artifact_sha256']
PY
```

If an authorized manuscript correction changes the paper commit, update its
correspondence record and repeat the affected checks before selecting a new
release snapshot. Preserve existing Git history.

## Repository visibility

The formal repository was made public on 2026-09-05 under the author's
explicit authorization, so that the Zenodo GitHub integration can archive a
release and Palomar can read the commit. AlgebraicAnalysis is public. The paper
mirror and the research archive remain private. Public visibility is not a
release: a release is the signed tag below, and registration is the separate
Palomar submission.

## Sign release tags

Proposed version names are `v1.0.0-rc1` for the formal package and
`stafford38-paper-v1.0.0-rc1` for the synchronized paper snapshot. These are
proposals, not existing releases. A human must choose and approve them.

With the existing global SSH signing configuration and key agent available:

```bash
formal_tag='v1.0.0-rc1'
git tag -s "$formal_tag" "$formal_commit" \
  -m "Stafford 3.8 formal release candidate"
git verify-tag "$formal_tag"
git push origin "refs/tags/$formal_tag"
```

Do not replace an existing tag or bypass signing if the key is unavailable.
The exact library commit remains pinned regardless of any library release tag.
Any new library tag requires the library maintainer's own version choice and
authorization; it is not created by the formal release procedure.

For the paper, use the existing authenticated mirror checkout whose remotes
are named `overleaf` and `github`. Supply that checkout's path, then verify
the source selected by Overleaf before signing its separate tag:

```bash
read -r -p 'Synchronized paper checkout: ' paper_checkout
git -C "$paper_checkout" fetch overleaf
git -C "$paper_checkout" fetch github
test "$(git -C "$paper_checkout" rev-parse overleaf/main)" = "$paper_commit"
test "$(git -C "$paper_checkout" rev-parse github/main)" = "$paper_commit"
paper_tag='stafford38-paper-v1.0.0-rc1'
git -C "$paper_checkout" tag -s "$paper_tag" "$paper_commit" \
  -m "Overleaf-synchronized Stafford 3.8 paper candidate"
git -C "$paper_checkout" verify-tag "$paper_tag"
git -C "$paper_checkout" push github "refs/tags/$paper_tag"
```

The signed tag certifies the synchronized paper snapshot. It does not make
the mirror an independently editable manuscript authority.

## Prepare separate source archives

Choose an existing output directory outside all Git checkouts. These commands
create source-only archives without working-tree caches or build outputs:

```bash
read -r -p 'Release archive output directory: ' release_dir
test -d "$release_dir"
release_dir=$(cd "$release_dir" && pwd)
git archive --format=tar.gz --prefix=stafford38-formal/ \
  --output="$release_dir/stafford38-formal.tar.gz" "$formal_commit"
git -C "$paper_checkout" archive --format=tar.gz --prefix=stafford38-paper/ \
  --output="$release_dir/stafford38-paper.tar.gz" "$paper_commit" \
  main.tex proof_map.tex references.bib LICENSE.txt
sha256sum "$release_dir/stafford38-formal.tar.gz" \
  "$release_dir/stafford38-paper.tar.gz" > "$release_dir/SHA256SUMS"
```

The formal archive retains Apache-2.0 `LICENSE`, `NOTICE`, citation metadata,
and its immutable external dependency. It does not vendor AlgebraicAnalysis.
The manuscript archive retains its CC BY 4.0 license and contains only the
authorized main manuscript, proof-map supplement, and bibliography. The
independent unfinished cyclicity draft is outside this manuscript release.

If a separate library source archive is desired, a maintainer can create it
from the exact public library checkout:

```bash
read -r -p 'AlgebraicAnalysis checkout: ' aa_checkout
git -C "$aa_checkout" fetch origin
git -C "$aa_checkout" verify-commit "$aa_commit"
git -C "$aa_checkout" archive --format=tar.gz --prefix=algebraic-analysis/ \
  --output="$release_dir/algebraic-analysis.tar.gz" "$aa_commit"
sha256sum "$release_dir/algebraic-analysis.tar.gz"
```

Keep the three artifacts and their licenses distinct. Inspect each archive
before any upload; the source archives are not generated paper PDFs.

## Zenodo

Zenodo archives GitHub releases through its GitHub integration and reads the
deposit metadata from [`.zenodo.json`](../.zenodo.json) at the released
commit. The procedure, once, for the repository:

1. Sign in at <https://zenodo.org/> with the GitHub account that owns
   `itpplasma/stafford38-formal`, open
   <https://zenodo.org/account/settings/github/>, and switch the repository
   on. The repository must be public for it to be listed.
2. Publish a GitHub release for the signed tag:

```bash
gh release create "$formal_tag" --verify-tag \
  --title "Stafford 3.8 formal release candidate $formal_tag" \
  --notes "Kernel-checked Lean 4 formalization of Stafford's Conjecture 3.8. See docs/verification.md." \
  "$release_dir/stafford38-formal.tar.gz" "$release_dir/SHA256SUMS"
```

3. Zenodo receives the release event, archives the tagged source tree, and
   mints a version DOI and a concept DOI within minutes. Read both from the
   Zenodo record page or from the badge on the GitHub settings page.
4. Record the DOIs in a follow-up commit: add `doi:` to `CITATION.cff` and
   the concept DOI to the README citation line. Do not edit `.zenodo.json`
   with the DOI; Zenodo assigns it.

Use only the identifiers Zenodo actually issues. The manuscript is not part of
this deposit; it remains CC BY 4.0 and is archived separately if ever
released.

## Palomar

After the formal repository is public and submission is explicitly authorized,
the responsible human opens the [official submission form](https://submit.palomar-registry.org/).
Use these exact inputs:

| Field | Value |
| --- | --- |
| Repository | `itpplasma/stafford38-formal` |
| Commit | The selected `$formal_commit`, full 40-character HEAD SHA approved by the external release receipt |
| Project directory | Repository root; leave the optional field blank |
| Comparator configuration | `comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Compared declaration | `Stafford38Challenge.universalStatement` |

The human signs in with GitHub, states the responsible-maintainer relationship
or its approval, and retains the returned status-page link. Review the result
there before separately choosing registration. No Palomar ID exists before
registration. These are the official [submission instructions](https://palomar-registry.org/how-to-submit);
this runbook provides no invented API or automated submission command.

## arXiv

Only after explicit manuscript-submission approval, open the authoritative
Overleaf project, compile the approved main document, and inspect its PDF.
Use Overleaf's arXiv export workflow to obtain the submission sources, including
the appropriate bibliography output and figures. Compare them with the
approved paper snapshot and inspect the upload archive; no Lean repository,
research archive, credentials, or unrelated draft belongs in that package.

The human submits through arXiv's account interface and inspects the PDF
produced by arXiv before completing submission. Follow the current
[TeX submission instructions](https://info.arxiv.org/help/submit_tex.html),
including their guidance for Overleaf exports. The manuscript remains CC BY
4.0, subject to the author's selected submission license. Record only the
identifier actually assigned by arXiv. Journal submission and contact with
reviewers require their own authorization.
