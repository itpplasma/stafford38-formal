# Stafford38 literal anchor refresh

`refresh-anchors.mjs` defaults to a dry run. It reads Lean source only through
`git show <full-commit>:<path>`, resolves every literal `\\leandecl` and
`\\leanlib` with the existing `tools/paper_lean_audit/lean.mjs` resolver,
requires one exported exact FQN, and proposes changes only to numeric line
arguments and the two source commit pins in `ai_review.tex`.

Example:

```sh
node refresh-anchors.mjs --paper /path/to/stafford38-paper \
  --formal /path/to/stafford38-formal --formal-commit <40-hex> \
  --library /path/to/algebraicAnalysis --library-commit <40-hex>
```

Dry run prints a manifest and atomically writes `anchor-refresh.patch` beside
the script (or to `--patch-out`). `--apply` uses `git apply` after rechecking
paper inputs; it is unavailable with `--preparation-only`. That flag permits
referenced Lean files to differ in index/worktree from the supplied commit,
but all resolution still uses exact commit object bytes and the manifest lists
the dirty relevant paths. Use it only for explicitly preparation-only candidate
runs. A normal run refuses relevant dirty source files.

The resolver is loaded from the formal checkout itself. Its unused rendering
import is replaced in-memory with a stub so no dependency install or repository
write is needed. This utility checks navigation and source integrity; it makes
no claim about proof correctness or paper/proof correspondence.
