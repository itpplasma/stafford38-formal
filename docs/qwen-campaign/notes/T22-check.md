# T22 endpoint adapter source freeze

## Frozen candidate

- WT base commit: `0340cf2b1601de7a8895c0b450d4bcbbb9867bed`
- Endpoint source SHA-256: `14d8f3abf5119a63a0ee287a6dd9524c8ad1d8c9acf29af84f920052de6dabdd`
- Literal consumer SHA-256: `6d3b5ab88a2bf74374be91339e1ff1a1a2eccae24b97088e8135957be9d2b4d2`
- Combined named-file content digest (path, NUL, bytes, NUL in the order above):
  `dc0e5451da57ea6c014b80a0449af299da41965b1918be4cdab4938f7cfd3aed`
- Frozen old endpoint dependency SHA-256:
  `32d6cb82af078383adfe0a3cdfc5353e9635bc7fd90e85ee25cc82e6cb55f674`

Other workers have concurrent uncommitted WT candidates. The digest above
therefore names only the two T22 files, with the base commit and endpoint
dependency hash identifying their relevant input; it is not a digest of the
whole WT worktree.

## Interface and proof sketch

The public declaration is
`Stafford38.Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_algHoms`
in `Stafford38/Geometry/SameWitness/EndpointOfAlgHoms.lean`. Its scalar
structures are supplied by `φ` and `ψ`; the result type installs the ψ action,
its k tower, `hψEtale`, and the original Laurent-series prelude before the
coordinate-derivative binders. All endpoint binders remain in their original
order, with only `hchart` using `φ (Ideal.Quotient.mk I ...)`.

The proof installs the quotient, polynomial-composite, and ψ actions on
abstract E; then builds the four scalar towers and the two formally étale
instances before applying the current endpoint. No extra mathematical
hypothesis or concrete E instance is introduced.

Relevant source signatures: `AlgHom.comp_algebraMap` is
Mathlib/Algebra/Algebra/Hom.lean:223; `IsScalarTower.of_algebraMap_eq'` is
Mathlib/Algebra/Algebra/Tower.lean:119 and consumes the reverse of
`AlgHom.comp_algebraMap`, hence the `.symm` used for φ and ψ. The quotient
algebra map is implemented as quotient-map composition at
Mathlib/RingTheory/Ideal/Quotient/Operations.lean:366 and its same-ring map
is definitional at line 402. `RingHom.FormallyEtale` is defined at
Mathlib/RingTheory/Etale/Basic.lean:289. `coordinateDerivation` requires the
chart action, k/chart/E tower and formally étale instance, as well as the
E/Laurent, k/Laurent actions and k/E/Laurent tower.

## Checks and remaining work

- `git diff --check`: passed before the final edits; the current source hashes
  above include those edits, but this check has not been repeated on the
  frozen files.
- Guarded build attempt 1 log SHA-256:
  `586e0ed4bb0007335512b11d330078b13887e988b0cf6d28609416f66c4541b6`.
  It found the k-to-polynomial tower proof, polynomial-to-quotient tower,
  hchart conversion, and section closing were incomplete. The candidate was
  revised for these findings.
- Guarded build attempt 2 log SHA-256:
  `9c8f76a780d13c411010360581d54b419710c66731ac7fc4eb1a0758cacfdc3e`.
  It found the constant-map equality in the k-to-polynomial tower proof,
  an underconstrained extension variable for the polynomial-to-quotient
  tower, the hchart conversion, and endpoint-name resolution. Those source
  sites were revised afterward; the revisions are frozen above but remain
  unverified.
- The next required checks remain the guarded module build (2700 s) and the
  guarded `--trust=0 -M 32000` literal-consumer check (900 s). No successful
  build, consumer run, or axiom receipt is claimed.
- The controller reported `free_mem_gb=25`, disk 552 GiB, no Lean process,
  and an unrelated 33 GiB `omlx-server` process. Guard execution is paused
  until the controller grants a new slot after memory recovers. No process
  was killed or restarted.

- On the later granted slot, source SHA-256 was rechecked as
  `14d8f3abf5119a63a0ee287a6dd9524c8ad1d8c9acf29af84f920052de6dabdd`.
  Third guarded build command:
  `guard.sh run --timeout 2700 --log .lake/qwen/logs/T22-luna-build-3.log -- lake build Stafford38.Geometry.SameWitness.EndpointOfAlgHoms`.
  It exited 1 after 15 s; GUARD reported peak RSS 1883 MiB, 2 Lean threads,
  69 GiB free RAM and no memory/disk kill. Log SHA-256:
  `a24f48e79b56ab159e4cf22c0cee73e9f77b26d64c02841fa91e5bd78bc2cae0`.
  The only source errors were `EndpointOfAlgHoms.lean:110:8: No goals to be
  solved` (the `rw [← φ.commutes c]` had already closed the goal before the
  following `congr 1; rfl`) and `:134:12: No goals to be solved` (the `congr
  1` had already closed the `hchart'` equality before the following `rfl`).
  Earlier tower, endpoint-name, and hchart type errors no longer appeared.
  Per the controller's instruction, no fourth build or source repair was
  attempted; the consumer has not run.

## Static risks to resolve after the guarded slot returns

1. Remove redundant tactics at source lines 110 and 134, then obtain a newly
   granted guarded module build.
2. Confirm the consumer's theorem statement is literally the same result
   type and reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Sol escalation: final checked candidate

This section supersedes the outstanding-check and static-risk sections
above. The historical Luna freezes and failed receipts remain preserved.
The final change removes only the two redundant `rfl` tactics. In the tower
proof, `rw [← φ.commutes c]` leaves a quotient-constant equality, and
`congr 1` closes it. In the hchart conversion, `congr 1` also closes the
remaining equality. No mathematical premise, public statement, scalar
budget, dependency, or consumer source was changed.

Final freeze, relative to WT base
`0340cf2b1601de7a8895c0b450d4bcbbb9867bed`:

- Source SHA-256:
  `690f8008bee2e7105d208306c91208f46c60d5e32de6040a9cfcda879d91a720`.
- Consumer SHA-256, unchanged:
  `6d3b5ab88a2bf74374be91339e1ff1a1a2eccae24b97088e8135957be9d2b4d2`.
- Named two-file patch `.lake/qwen/review/T22-sol-final/candidate.patch`:
  `069840c2f2e97833931de2128be5def4043cfd76ff49e9cee4fc8a926235edf2`.
  It contains only these two new files against the base; unrelated WT
  candidates are excluded.
- Repair against the original static-review source, frozen at
  `.lake/qwen/review/T22-sol-final/repair.patch`:
  `ba94d110d1691c931e59647afd9bc5d0383ae63076e50a5735ea47a6d1b18d1a`.
- Combined named-file content digest, using the original note's convention:
  `ac555742ed136c29f7d25a1f06f25bdea70b44a737fa103c6800bd9e1c8301e3`.
- Source/import receipt
  `.lake/qwen/review/T22-sol-final/source-receipt.json`:
  `905d1edb09cafbb77dfc11fbb14445d80706045465405b0622d9ec82aac2c6b6`.
  It records all 113 recursive project source paths and hashes, with zero
  unresolved imports, plus the unchanged toolchain/manifest hashes.
  The pinned endpoint hash remains
  `32d6cb82af078383adfe0a3cdfc5353e9635bc7fd90e85ee25cc82e6cb55f674`.

Static comparisons confirm the complete statement body equals both the
original reviewed freeze and the literal consumer, character for character;
the consumer bytes are unchanged. No-index whitespace checks against
`/dev/null` passed for both new files. These comparisons are static checks,
not substitutes for the following Lean results.

Commands ran serially from `/Users/ert/proj/stafford38-qwen` through the
controller's guard, with its unchanged 8 GiB RSS cap, two-thread CPU budget,
12 GiB start floor and 4 GiB kill floor:

```text
/Users/ert/proj/stafford38-formal/docs/qwen-campaign/guard.sh run --timeout 2700 --log .lake/qwen/logs/T22-sol-build-2.log -- lake build Stafford38.Geometry.SameWitness.EndpointOfAlgHoms
```

Result: exit0. Final guard summary:

```text
GUARD exit=0 reason=finished wall_s=5 peak_rss_gb=1 peak_rss_mb=2009 peak_cpu_percent=149 rss_cap_gb=8 cpu_cap=2 lean_threads=2 free_mem_gb=76 disk_free_gb=652 swap_used_gb=0
```

Build log SHA-256:
`3fc6d8ef875e369158a872af1014246dca7f23f6be94bd8b4efb12adc920fa73`.
The build finished well inside T22's 120-second acceptance bound. Existing
style/deprecation warnings remain; there were no source errors or resource
kills. No repository-wide verifier receipt is claimed by this bounded task.

```text
/Users/ert/proj/stafford38-formal/docs/qwen-campaign/guard.sh run --timeout 900 --log .lake/qwen/logs/T22-sol-consumer.log -- lake env lean --trust=0 -M8000 tests/SameWitness/EndpointOfAlgHomsConsumer.lean
```

Result: exit0. The literal consumer prints exactly
`[propext, Classical.choice, Quot.sound]`. Final guard summary:

```text
GUARD exit=0 reason=finished wall_s=5 peak_rss_gb=1 peak_rss_mb=1860 peak_cpu_percent=47 rss_cap_gb=8 cpu_cap=2 lean_threads=2 free_mem_gb=75 disk_free_gb=652 swap_used_gb=0
```

Consumer log SHA-256:
`0d58f9f29812288568d2be8e2c33534bd5ec5f56cc3d89da74e153707aebd044`.
This check uses the controller's reduced `-M8000` per-process cap; no
heartbeat limit was increased.

The first Sol build, `.lake/qwen/logs/T22-sol-build.log`, exited1 in5 s
because removing `congr 1` as well as `rfl` left the quotient-constant
identity unsolved. Its log hash is
`bb494e6810ed9c62eed5afc3490565dcf5e4d2835f292735d82bcf3272175e11`.
The exact failed source and patch are preserved in
`.lake/qwen/review/T22-sol-frozen/`; source hash
`fc6a79837adebfeace0a9145c82ac6380a61cf9138fc39da676388406fce7316`.
Restoring `congr 1` produced the checked final source above.

The original independent audit is a static PASS for its older freeze.
The controller has been notified of the final hashes for reanchoring under
that audit's reopening condition. This worker does not edit or promote the
audit, ledger, release state, commits, or pushes. The adapter still assumes
its maps and geometric data and does not prove the unconditional closure
or manuscript correspondence.

## Controller acceptance

The controller checked the final source and accepted build/consumer evidence. Source, logs and the final frozen packet are archived in `T22-accepted-checks.tar.gz` (SHA-256 `da6e2bd380532c87b9780b25f407b2715d5d565b1e6b13a773d2e673439e3af1`). These checks establish this helper's recorded scope; full route and repository verification remain separate gates.
