# T60 and T61 draft preparation

These artifacts give the controller reviewable proposals for four new definition owners and a locator map for the current same-witness theorem sources. They leave `docs/definition-owners.md` and `docs/paper-route-alignment.json` unchanged.

`T60-definition-owners.patch` adds owners for `ChartSetup`, `CoordinatePresentation`, `CommonOpenArcData`, and `CommonOpenEtaleData`. Exact-name searches in the current registry found no existing owner for these packages. Their constituent concepts already have owners, but those owners do not retain the combined data carried by these structures.

There is no `docs/qwen-campaign/notes/new-definitions.md`; the entries were supplied separately in T30, T31, T33, and T35 notes. T32 and T34 notes also describe `CommonOpenData` and `CommonOpenPositionData` (and a planned `CommonOpenColumnsData`). They were outside this worker's assigned definition-entry set and are not added by the T60 patch. The current worktree has `CommonOpenData` and `CommonOpenPositionData`, but no `CommonOpenColumns.lean`; `AffineFibreClosure.lean` imports that missing module and calls `commonOpenColumnsData_of_arc`. The controller should resolve this source gap and review the T32/T34 ownership entries before promoting either patch.

`T61-paper-map.patch` proposes 17 declaration rows under a new `same_witness_route.declaration_map_draft` field. It points to the selected paper file at repository commit `357b7d9db8e5d363a11500b301f04607654bd809`, SHA-256 `fd707283bda604800400fd86cb31f9e3ab083f29a3fb8e556c230ccd83aaaa3b`. The locations are candidate mathematical analogues, statement matches, or explicit “no direct counterpart” notes. In particular, the original-prime theorem is mapped to the statement of Theorem `asymptotic-conormal`, while its row states that proof routes remain separately reviewed. The patch retains `same_witness_route.status` as “checked components; end-to-end closure open,” leaves all existing non-claims intact, and names the Max and Johanna review roles already recorded in the file. The visible author proof and marked proposals remain untouched.

The 17 rows include the two current CommonOpen construction theorems and both private top-level bridge theorems. Private declarations are identified by their source names and lines, not by generated private kernel names. The map remains provisional: the WT sources are uncommitted, and the missing `CommonOpenColumns.lean` prevents this note from asserting that the affine-fibre assembly has an accepted source snapshot.

Both patches passed `git apply --check` against the WT destination paths. Neither patch was applied. No Lean command was run, and no source, state, destination registry, or manuscript file was changed.

## Frozen inputs

- MAIN campaign base: `PLAN.md` SHA-256 `5d3748ba44ca4d71163856746a4df671d5809b25a7922b0fc7b4a87c92ef3114`.
- Provenance rules: `proof-source-provenance.md` SHA-256 `6a3439d839c77425228a31bd5e9079dbc9ee686d1b0efaa670e942b3fe5b06cc`.
- Existing definition registry: SHA-256 `d78fcb1e40dc27e0f77855fa0055d571b0821e326b7aeeb335ecfa9d81e78765`.
- Existing alignment map: SHA-256 `c54090f44f93d39bde30d79ed00aba761df09eb507287a086062b167c75578bd`.
- Entry notes: T30 `4d5ccb7ccd61db8cc420b62681785965ad06e5f21fcc795f46b6b42af0624374`; T31 `94e08c78ec12642420b7a7d7ee4f03a5c6cde158ee560e9d19113e95bd8af41f`; T33 `4325e5e8f4a8961fbeb58324f7ef232982100f38e8c528ada6b8eb42455bfa2f`; T35 `c313f7e3fffc5a5f35ba85de81d83de282330bb6288e0b53b010ef63797b1ac7`.
- WT source base commit: `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`. The 12 mapped source files, hashed in path order (AwayFactorToAtPrime, AxisLiftFromGroundPoint, ChartGroundMap, ChartSetup, CoordinatePresentation, CommonOpen, CommonOpenArc, CommonOpenEtale, CommonOpenPositions, EndpointOfAlgHoms, AffineFibreClosure, OriginalPrimeAxis), have a combined SHA-256 manifest digest `586bbc9d7b6d5557ec0ce6c87f1396ef56337ed78282b03c72e0523aeacc1b0b`.
- Patch SHA-256 values: T60 `52687881065662e065bfb04bbbe25b199f7a86e830c7c71a29858d43622d322e`; T61 `f429ef5b17ccc4f1e5c474961ee32632ddb40577973f47808280c02661b1e430`.
