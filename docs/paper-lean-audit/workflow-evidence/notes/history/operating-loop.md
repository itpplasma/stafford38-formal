# Stafford operating loop

This is the execution protocol for persistent Goal Mode.

- `PLAN.md` is the compact human dashboard.
- `notes/history/task-pool.yaml` is the authoritative machine state.
- `notes/history/frontier-ledger.md` and
  `notes/history/decision-log.md` are append-only mathematical history.
- `notes/history/index.md` and `notes/history/claim-dag.tsv` are generated
  navigation, not independent status sources.

## Mission

The terminal mission is Stafford 3.8 for every characteristic-zero field and
every Weyl algebra `A_n`:

```text
for every nonzero d in A_n, find F, R, S with 1 = d*R + F*d*S.
```

The current control-plane identifier retains the historical name
`STAFFORD-3.8-A2`; its scope is universal `A_n`. `A_2` is a subordinate work
lane. A fixed cofactor, generic stratum, bounded search, special class, or
formal boundary is never terminal progress by itself.

## Fast cycle

1. Read `AGENTS.md`, `PLAN.md`, the task pool, and the active task's declared
   verifier and evidence paths.
2. Select exactly one task with `status: OPEN` and `active: true`.
3. Complete one coherent load-bearing block; routine supporting lemmas stay in
   the same block rather than becoming separate checkpoints.
4. Run its declared verifier and retain the command output.
5. Record exactly one result: `PROVED`, `FORMALIZED`, `COMPUTED`, `REFUTED`,
   `CONDITIONAL`, `BLOCKED`, or `NO_PROGRESS`.
6. Use focused independent review at major frontier boundaries, terminal
   assembly, and release; do not review every incremental lemma.
7. When the truth state changes, update the dashboard, task pool, ledger,
   decision log, and generated navigation in one controller integration.

The active task is the task marked `active_task` in
`notes/history/task-pool.yaml` (currently `FORMAL-END-TO-END`). Its three
formalization frontiers are listed only under `FORMAL-END-TO-END` in that
file; this protocol does not duplicate their mutable route descriptions.
Workers return evidence. The controller owns authoritative state, integration,
and promotion.

## Parallel computation without extra state

Parallelism is a property of one active attack, not a reason to create more
tasks. Freeze one input statement and dispatch up to four independent lanes.
Each lane gets a declared core budget and scratch directory and returns only:
the command, tool version, input digest, exact output or certificate, and scope.
The controller alone updates the plan, task pool, ledgers, claims, and proofs.

Detect the controller host's available cores at runtime. Use all cores for one
large build or partition them among disjoint lanes without oversubscription.
For independent processes set `OMP_NUM_THREADS=1` and
`OPENBLAS_NUM_THREADS=1`. Pause workers during final integration when their
load would compete with verification.

For the current active task, dispatch distinct theorem-sized producers from
the task pool. Use CAS tools only against a named identity, obstruction, or
counterexample and use Lean for reviewed universal statements. A lane that
only emits additional special examples has not met its contract.

## Integration and blocked leaves

Integrate after a coherent load-bearing block, active-leaf closure or
refutation, a conceptual block, or an interface change. Reconcile the declared
evidence with the actual files before promotion.

A blocked leaf is not the terminal mission. Record the exact missing input,
preserve the evidence, and select the highest-information executable open leaf.
Do not declare a mission hard stop without the required independent inventory
and review.

## Guardrails

- All ideals are right ideals unless explicitly marked otherwise; retain
  explicit right cofactors.
- Localization, completion, GK/Fitting arguments, cancellation, and
  associated-graded lifting require their noncommutative hypotheses.
- The companion matrix unit does not descend through an equivalence that
  manufactures an identity block.
- Bounded negatives are window-scoped, and positive generation decisions need
  explicit certificates.
- Do not replay blacklisted routes without new input that defeats their
  recorded obstruction.
