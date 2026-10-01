---
name: program-loop
description: Manage progress in a long-horizon project with a terminal mission, durable state, milestone dependencies, executable tasks, and explicit continuation rules.
---

# Program Loop

Use this skill for any long-horizon project that has:

- a terminal mission;
- a roadmap, milestone plan, or dependency graph;
- durable repository state;
- executable or reviewable intermediate tasks;
- a need to continue past intermediate successes.

This skill manages progress. It does not supply domain expertise.

## Activation

Activate at the start of a long-horizon project iteration, at a milestone
boundary, after a substantial interface or dependency change, or whenever the
project needs to continue beyond an intermediate success.

## Inputs

Before beginning, locate or create project-local equivalents of:

- terminal mission;
- roadmap or milestone DAG;
- current status;
- task pool or active task;
- evidence ledger;
- decision log;
- verifier commands;
- stop conditions.

Project-local state is authoritative. Never replace it with a skill-global
state file.

## Workflow

The terminal mission remains active until a declared terminal condition is
met. Passing a task or milestone is evidence of progress, not terminal
completion.

For each normal iteration:

1. Read durable project state.
2. Select exactly one active task.
3. State the desired result, verifier, expected evidence, and failure
   condition.
4. Execute only that task.
5. Run the declared verifier.
6. Record exactly one result from the valid outputs below.
7. Update only the state records affected by that result.
8. Do not silently redefine the task, milestone, or mission.

Run an integration cycle when any trigger occurs:

- four verified task deltas;
- three consecutive `NO_PROGRESS` results;
- milestone pass or refutation;
- cross-component interface change;
- major external dependency update;
- conceptual block;
- explicit user request.

During integration:

1. Re-read the terminal mission and roadmap.
2. Reconcile state records with actual evidence and verifier outputs.
3. Check whether milestone prerequisites are truly satisfied.
4. Promote the next eligible milestone only if all promotion gates pass.
5. Retire duplicate, disproved, stale, superseded, or assumption-dependent
   tasks.
6. Run the broadest relevant regression or reproducibility suite.
7. Tidy documentation, generated artifacts, pins, and dead work only after
   verification passes.
8. If the active frontier is stagnant, invoke `bounded-exploration`.

## Valid outputs

Record exactly one of:

```text
PASS
FAIL
BLOCKED
REFUTED
CONDITIONAL
NO_PROGRESS
```

A task may be marked `PASS` only if its declared verifier was actually run or
the required review protocol was completed. A milestone may be marked `PASS`
only if all prerequisite tasks pass, no unresolved blocking review remains,
evidence is recorded, relevant regression checks pass, and scope is explicit.

## Verification

For `NO_PROGRESS`, record what was attempted, the exact commands or
derivation, the first blocker, and whether the route should be retried,
revised, or retired. For every promotion, retain the verifier output and the
evidence-ledger entry that supports it.

## Forbidden pseudo-progress

Never manufacture notes, code, proofs, tests, diagrams, or refactors merely to
avoid a `NO_PROGRESS` result. Do not stop merely because an intermediate
milestone passed, and do not promote a milestone with missing prerequisites or
unresolved blocking review.

## Escalation

If the active frontier is stagnant, use `bounded-exploration`. Escalate to
`expert-escalation` only after the exploration or the required distinct failed
attempts meet that skill's trigger conditions. A hard stop must identify the
exact missing external dependency, experiment, theorem, decision, resource,
or human input.

## Composition

Use a domain skill to perform the active task, `evidence-gate` to assess its
result, and `parallel-luna` to audit substantive promotions. Keep authoritative
state mutation serial through one controller. Add `bounded-exploration` and
`expert-escalation` only when their activation conditions are met.

## Terminal conditions

Continue automatically unless one of these holds:

1. the terminal mission is complete;
2. the terminal mission is refuted;
3. a reviewed hard stop identifies the exact missing external dependency,
   experiment, theorem, decision, resource, or human input.

## Parallel work policy

Parallelize only independent reconnaissance or review with fixed inputs. Do
not parallelize overlapping implementation edits, changes to authoritative
state, or dependent tasks whose inputs are not fixed.
