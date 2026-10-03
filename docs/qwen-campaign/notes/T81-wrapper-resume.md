# T81 separate-paper review wrapper

The T81 wrapper now accepts an explicit local checkout for a paper source
whose repository differs from the formal source. It reads every manuscript
and compilation input from the selected paper commit with `git show`, checks
the checkout’s GitHub remote against the repository in the map, and checks
that the formal checkout matches its mapped repository and contains the pinned
formal commit. The existing receipt checks still require matching manuscript,
formal/library source metadata, bibliography/TeX source hashes, and both PDF
hashes. The renderer receives separate `--paper` and `--formal` roots; its
existing library, GlobalStafford and Mathlib pinned fetches are unchanged.

With distinct repositories in the map, the wrapper requires an explicit path:

```sh
python3 scripts/build-review-site.py --paper /home/ert/proj/stafford38-paper
```

Use `--check-assets` with the same `--paper` path for the receipt gate only.
The wrapper still refuses `candidate.status: pending-final-source-pins`; final
map pins, new theorem rows and release assets remain controller work after
formal acceptance and source freeze.

Implementation scope is limited to WT `scripts/build-review-site.py` and its
existing fixture suite `scripts/tests/test_review_site_assets.py`. The suite
adds independent separate-repository fixtures for successful frozen-byte
reads despite working-tree edits, missing explicit checkout, wrong repository
identity and unavailable paper commit. All 10 tests pass; `--help` renders and
`git diff --check` passes. No Lean or PDF build was run.

The WT input base was `c3dccd4b3f931d15df623229771126f6500fb6ea`; pre-existing
uncommitted SameWitness edits were left untouched. This task's only MAIN write
is this note. The controller should include the `--paper` path in the T81
command after choosing the exact public paper checkout/commit and updating the
review PDF receipt to those same frozen inputs.
