---
name: bounded-exploration
description: Explore a blocked project task with at most three distinct, testable candidate routes without promoting claims or changing authoritative implementation state.
---

# Bounded Exploration

Use this skill when normal execution is blocked and the project needs new
ideas, alternatives, or design-space exploration. This skill creates
proposals. It does not directly promote claims or modify implementation state.

## Activation

Invoke only after at least one of these conditions holds:

- two materially distinct failed technical attempts;
- three `NO_PROGRESS` cycles;
- an active task has no executable next step;
- a new milestone requires a design choice;
- a required theorem, interface, or oracle is genuinely underdetermined;
- an integration cycle identifies a strategic gap.

Do not invoke merely because a task is difficult.

## Inputs

Require a packet containing:

- terminal mission;
- exact active task;
- established facts;
- current evidence;
- failed attempts;
- blacklisted routes;
- constraints;
- available tools;
- time and compute budget;
- required verifier or falsification test.

## Workflow

Privately generate qualitatively distinct routes. For each candidate, state:

1. one-sentence mechanism;
2. which assumption, invariant, representation, interface, or decomposition it
   changes;
3. why it differs from failed routes;
4. smallest executable test;
5. expected information gain if it passes;
6. expected information gain if it fails;
7. first technical bottleneck;
8. required dependencies;
9. whether it can be pursued safely in parallel with other work.

Return at most three candidates. Rank them by:

```text
expected information gain
× testability
× relevance to terminal mission
÷ estimated cost and duplication risk
```

The controller promotes at most one candidate into the active task pool.

## Valid outputs

Every exploration result ends with exactly one of:

```text
PROMOTE candidate X
REQUIRE expert consultation
NO USEFUL CANDIDATE
```

`PROMOTE` means only that one bounded candidate may enter the task pool; it is
not a claim, milestone pass, or implementation result.

## Verification

Every candidate must name its smallest executable test and the required
verifier or falsification test. The controller must create a bounded task with
an explicit verifier before any candidate is pursued.

## Forbidden pseudo-progress

Exploration must not claim the mission solved, rewrite the roadmap, silently
revive blacklisted routes, add implementation artifacts, create unverified
architecture, use “be generic” or “one should” as a mechanism, or hide the
first unsupported inference.

## Escalation

Return `REQUIRE expert consultation` when no candidate has an executable,
mission-relevant test and the block requires specialist knowledge. Invoke
`expert-escalation` only with this bounded packet and the failed-attempt record.
Do not use exploration to bypass an evidence gate or independent review.

## Composition

Invoke from `program-loop` after its stagnation triggers. Feed established facts
and failures into the exploration packet, then send one promoted candidate back
to `program-loop` as a verifier-bearing task. Pair the resulting task with the
relevant domain skill, `evidence-gate`, and `parallel-luna` as appropriate.

## Parallel work policy

Independent candidate tests may run in parallel only when their inputs and
resource budgets are fixed. Keep route selection, task-pool promotion, and
decision-log mutation serial; never run overlapping implementation edits.
