# T45 variant tooling resume

Date: 2026-10-03. This note records the bounded tooling candidate prepared in
`/home/ert/proj/stafford38-qwen`. It is not a proof or Comparator receipt.

The assigned comparison base is `8fa692f4f72c4ff01f4c0d22ff4dd5be6cd22ba7`.
The Qwen branch advanced to `da00639e7d2fd3cbb188f137d228c99d5cfcdbcd` while
workers were active, so the tooling patch digest below is explicitly computed
against the assigned base and only across the tooling-owned paths. Its SHA-256
is `ae4fe0c41569687ee79a7be217c2b767481af8d8422b419133b301440dc15445`
(31,681 patch bytes). The solution proof files and concurrent proof-worker
changes are outside that digest.

`Challenge.lean` and `FixedSourceChallenge.lean` remain byte-identical to the
assigned worktree snapshot: SHA-256 `da107b2555a4923ec5e013c710ed3dcdee74b9d2bd33a6fc25b39e0fa8b50605`
and `403dc92296114ad6e52dcec1d627ad65bfd04f76058f260f12845c7f73a69f5c`,
respectively.

The tooling candidate adds two exact Comparator configs for the alternative
solution modules and extends the selector, source-policy config gate, Lake
library roots, solution import audit, source audit, and behavior oracles. The
existing main configs and default selector remain unchanged. The strict
terminal dependency guard keeps the same four roots and Laurent producer
denials. Its new additive route command checks exact required and forbidden
declarations while retaining fail-closed body inspection. `scripts/verify.sh`
uses separate main and alternative guard processes because both isolated
solution pairs intentionally export the same challenge theorem names.

Non-Lean checks passed: all four policy contracts were accepted; a mixed
alternative/main config was rejected; the dependency pin and vendored-policy
tamper cases still reject; Python syntax, shell syntax, and JSON parsing pass.
The full policy preflight was attempted and rejected four concurrent proof
consumer files missing the required `module` header; the controller owns those
repairs. No Lean or Comparator invocation was run in this candidate.

After the controller grants the Linux Lean slot, the route-specific checks are
available through `scripts/verify.sh`. The standalone exact route commands are:

```sh
python3 scripts/dependency-guard/run_guard.py \
  --base-module Solution --base-module FixedSourceSolution \
  --route Stafford38Challenge.universalStatement Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38FixedSourceChallenge.universalFixedSourceStatement Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure

python3 scripts/dependency-guard/run_guard.py \
  --base-module AlternativeSolution --base-module AlternativeFixedSourceSolution \
  --route Stafford38Challenge.universalStatement Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure \
  --route Stafford38FixedSourceChallenge.universalFixedSourceStatement Stafford38.Geometry.AlternativeAsymptoticConormal.coordinate_axis_mem_smooth_fibre_closure Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure
```

The isolated Comparator checks are:

```sh
bash scripts/verify-palomar.sh comparator-alternative.json
bash scripts/verify-palomar.sh comparator-alternative-fixed-source.json
```

The fixture oracle is `python3 tests/dependency-guard-fixtures/test_behavior.py`;
it covers an accepted required/excluded route, an opaque body whose owner is
fully loaded, missing required and reached forbidden endpoints, and an
incomplete closure. These checks still need execution under the authorized
guarded Linux slot. No solution module, whole-proof correspondence, or new
Palomar service receipt is certified by this note.
