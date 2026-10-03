# T80 source-resolution diagnostic

This is a bounded locator diagnostic for the pending paper-map candidate. It does not accept the map, establish manuscript proof correspondence, or satisfy the T81 review-site gate. The renderer completed, but its check failed on the supplied candidate sources; the generated HTML is diagnostic output only.

## Frozen inputs

- Candidate map source: formal commit `3bd3b2926464c440acba0daaca63532c326bda2a`, path `tools/paper_lean_audit/paper-lean-map.json`.
- Paper: `/home/ert/proj/stafford38-paper`, commit `53882beb19c1491c43867fa78ee3b5bba3f18169`, selected file `human_readable_main.tex`, SHA-256 `fd707283bda604800400fd86cb31f9e3ab083f29a3fb8e556c230ccd83aaaa3b`.
- Formal diagnostic source: `/home/ert/proj/stafford38-qwen`, pinned to base commit `fcd866f9dcf736d624b96a8fd5ea086ca910f9ad`. This is a candidate diagnostic pin, not an accepted freeze; uncommitted worktree changes were visible to `git show` only through this pinned commit.
- AlgebraicAnalysis: `/home/ert/proj/stafford38-qwen/.lake/packages/algebraicAnalysis`, commit `bbbbf3fc358ca8100b158cec4cf47f336ab70163`.
- Mathlib: `/home/ert/proj/stafford38-qwen/.lake/packages/mathlib`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`.
- Standalone renderer: `/home/ert/proj/paper-lean-audit`, commit `f0ce035538b4fa704109a34d14aa22265dec2a31`; `build.mjs` SHA-256 `70908923650dd2777d4681646ba0555f791845295e5a4bd772bfc42115cf303c`.
- The scratch map was re-anchored with `scripts/reanchor-review-map.py`; it contains 55 cards and 28 visible comments. Its status remains `pending-final-source-pins`. Scratch map SHA-256: `93acb2a5297f66e997b7c1d3c201b7ac65b43887aea96c4521579d3ff323321e`.

All scratch files are under `/tmp/stafford-map-resolution-luna/`.

## Renderer result

Exact command (run from the standalone renderer checkout):

```sh
node build.mjs --map /tmp/stafford-map-resolution-luna/candidate-map.json --check \
  --source paper=/home/ert/proj/stafford38-paper \
  --source formal=/home/ert/proj/stafford38-qwen \
  --source library=/home/ert/proj/stafford38-qwen/.lake/packages/algebraicAnalysis \
  --source mathlib=/home/ert/proj/stafford38-qwen/.lake/packages/mathlib \
  --source global=/home/ert/proj/global-stafford-formal \
  --out /tmp/stafford-map-resolution-luna/render
```

Exit code: `1`. The renderer wrote `/tmp/stafford-map-resolution-luna/render/stafford38-paper-lean-audit.html`, then reported `410 warnings` and `116 ERRORS`. Complete stdout/stderr is `/tmp/stafford-map-resolution-luna/render.log`, SHA-256 `089766107764d4ec9c6d7aa0843abdb053c0f83eb871e76984486a78f20abdc3` (529 lines).

The 116 errors split into 115 stale \leandecl line arguments and one wrong declaration owner in the candidate map. For each of the 115 manuscript references the named declaration resolves as an exact exported declaration, but its stored source-line argument differs from the declaration line at formal commit fcd866f9dcf736d624b96a8fd5ea086ca910f9ad. The remaining map error is item cyclicity: its definition row names Stafford38.TorsionCyclicity.IsRightTorsion at the wrong source file/line (Stafford38/TorsionCyclicity.lean:18). Its canonical definition in the pinned source is Stafford38/ChallengeDefinitions.lean:203 inside namespace Stafford38.TorsionCyclicity; the narrow map-row repair is to update that row's file and line to this exact owner/line. The paper's own IsRightTorsion link is not among the 115 line-only changes and needs a separate source-file correction if the paper authority accepts it.

The selected theorem references at paper lines 1310–1314 resolve against the pinned formal source; their errors are stale line arguments, not missing declarations. This includes PaperSameWitnessTangentDimension, PaperActualWitnessConormalData, GeneralConormalAxis, GeneralAsymptoticLaurentAxis, and the principal endpoint GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure. The full log lists every old locator and resolved line exactly.

The 410 warnings are locator mismatches in the map, with candidate-formal declaration lines differing from saved map lines. For example, Stafford38.Characteristic.poissonBracket resolves at line 31 while the map says 28; Stafford38.Geometry.GeneralAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure resolves at line 32 while the map says 28. These are source-location diagnostics, not proof-correspondence findings.

## Non-authoritative paper locator patch

docs/qwen-campaign/notes/T80-paper-locators.patch proposes updating only the numeric second argument of 115 \leandecl/\leanlib references in the frozen human_readable_main.tex, using exact exported declaration lines from the candidate formal and library commits above. It changes 115 references across 114 manuscript lines. The source file/name arguments, visible prose, proof text, and marked proposals are unchanged. A normalization that replaces only the second locator argument in each reference yields byte-identical manuscript text before and after the patch. The patch is not applied to the paper checkout and does not repair the separate wrong-owner IsRightTorsion map row.

## Narrow map-fix proposals

1. Preserve the current pending status. Do not make the renderer output or this diagnostic a T81 gate.
2. On the accepted map only, repair cyclicity's definition row to Stafford38/ChallengeDefinitions.lean:203 after confirming the accepted formal source retains that declaration.
3. Consider the non-authoritative paper locator patch only through the paper's authority/review process; it does not change visible manuscript prose or marked proposals.
4. Repeat source resolution only after accepted paper/formal/dependency pins are available; keep the rendering incomplete while the map remains pending.

No authoritative map, registry, manuscript, formal proof, supplementary artifact, or shared state was changed. The only repository edit is this note; the unrelated pre-existing untracked `docs/qwen-campaign/cluster-guard.py` was left untouched. No Lean command, package installation, PDF build, network write, or protected-host access was performed.
