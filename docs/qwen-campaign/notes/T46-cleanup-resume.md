# T46 package cleanup reference audit

Status: report only; no deletion, Lean source edit, verifier run, or promotion.

## Frozen candidate identity

- MAIN: `4593b857030efa79bd94395db9fe2c1d6aa86611`.
- WT base: `da00639e7d2fd3cbb188f137d228c99d5cfcdbcd`.
- WT is concurrently dirty. SHA-256 of `git diff --binary HEAD`: `71c3cf6de744e1e5ddb779d5765bcca03d23612a5f57b1774d38a21d8f54afac`.
- SHA-256 of the sorted untracked path/content-hash manifest: `f4220932e147000b66a3e5ec3f5af2b5897446057de4edc845ae06a0f1d09592`.
- Combined digest of those two digests (newline-delimited): `edf1929ffa68e633975777ae1ba9b2e2b849641a5bed73e61eaa8402b14370c7`.

The source audit used the WT at that identity, including the concurrent untracked alternative front doors and alternative geometry module. It did not read or alter MAIN's unrelated untracked `docs/qwen-campaign/cluster-guard.py`.

## Method and result

Read `docs/proof-source-provenance.md`, both campaign plans, the campaign ledger, WT `AGENTS.md`, and the current verifier roots. Parsed local `import` and `public import` edges across the 578 Lean files. Reachability roots were the seven roots specified by the campaign T62 instructions—`Stafford38.lean`, both current solution roots, both alternative solution roots, `CorollaryChallenge.lean`, `PaperPairChallenge.lean`—plus all 131 `tests/**/*.lean` files (138 roots total). The graph reaches 570 local modules. Only two `Stafford38/Geometry` files are unreachable from these roots; each has zero direct Lean importers.

No strict deletion candidate was found. The smallest safe deletion list from this audit is empty:

| Unreachable file | Direct Lean importers | Other references | Disposition |
| --- | ---: | --- | --- |
| `Stafford38/Geometry/PaperLaurentArcTangency.lean` | 0 | One source comment in `ContinuousPowerSeriesTangentFrame.lean`; one historical build-input record and two migration-input records | Retain: it contains a substantive generic Laurent tangency theorem and is mathematical material associated with the preserved Laurent route. |
| `Stafford38/Geometry/PrescribedCompletionNonzeroConsumer.lean` | 0 | One historical build-input record and two migration-input records | Retain: it proves the concrete edge case that a centered coordinate vanishes at the chosen residue point while its completed series is nonzero. This is a useful consumer theorem, not scaffolding. |

The graph is an import/reference audit, not a behavioral verification. `scripts/verify.sh` currently enumerates every `Stafford38/**/*.lean` source into its explicit `lake build` module list, so both files are also compiled by the full verifier.

## Entry-point and package references

Zero direct local Lean importers alone does not establish that a package front door is obsolete. The current `scripts/verify.sh` (module roots at lines 40–44 and comparator/closure checks near lines 330–336), `scripts/verify-palomar.sh`, `scripts/check-import-closure.sh`, `scripts/check-palomar-policy.py`, and `tests/palomar-comparator-behavior.sh` explicitly qualify the alternative entry points and unchanged challenge pairs. Local Lean import counts are:

| Entry point | Direct local Lean importers | Disposition |
| --- | ---: | --- |
| `Solution.lean` | 0 | Retain as the paper-route Palomar solution root. |
| `FixedSourceSolution.lean` | 1 | Retain; `tests/FixedSourceChallengeConsumer.lean` imports it. |
| `AlternativeSolution.lean` | 0 | Retain as the generic/Laurent variant root; verifier, policy, and comparator tooling name it. |
| `AlternativeFixedSourceSolution.lean` | 0 | Retain as its fixed-source variant root; verifier, policy, and comparator tooling name it. |
| `Challenge.lean` | 0 | Retain as the unchanged Palomar challenge root. |
| `FixedSourceChallenge.lean` | 0 | Retain as the unchanged fixed-source challenge root. |
| `CorollaryChallenge.lean` | 2 | Retain; imported by the corollary owner consumer and torsion consumer. |
| `PaperPairChallenge.lean` | 1 | Retain; imported by `tests/PaperPairConsumer.lean`. |

The existing `AlternativeSolution.lean` and `AlternativeFixedSourceSolution.lean` explicitly route through `Stafford38.GenericLaurentVariant`; the proposed `AlternativeAsymptoticConormal` endpoint is referenced by the modified coisotropic modules. Those names and their comparator JSON files therefore belong in the final release package. The challenge definitions remain in their existing shared challenge modules.

## Documentation and receipts

Keep `docs/verification-results.json`, the historical `docs/verification/` and `docs/audits/` receipts, dependency pins/manifests, and the selected paper materials. This follows the provenance instructions and the campaign T46/T62 scope. The current README/STATUS/paper-route map still describe the pre-integration route and open gates; revise their route/status wording only after the controller accepts the final candidate and freezes its evidence. No documentation or release metadata patch is proposed at this checkpoint.

No `scripts/`, selected-paper, review-tool, test-fixture, or named scratch asset met the deletion criterion “obsolete and unused” while also lacking a preservation or verifier role. Controller integration and the complete verifier remain outstanding; this report does not claim either.
