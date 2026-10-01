---
name: bounded-exploration
description: Explore at most three distinct, testable routes after normal execution is genuinely blocked.
---

# Bounded Exploration

This skill proposes routes. It does not promote claims, edit authoritative
state, or replace the project verifier.

## Activation

Use only after two materially distinct failures, three `NO_PROGRESS` cycles,
no executable next step, a new design choice, an underdetermined theorem or
oracle, or an integration-identified strategic gap. Difficulty alone is not a
trigger.

## Packet and candidates

The packet must include the mission, active task, established facts, evidence,
failed and blacklisted routes, constraints, tools, budget, and verifier.

Return at most three qualitatively distinct candidates. For each give:

- mechanism and changed assumption/invariant/representation;
- difference from failed routes;
- cheapest executable test and falsification condition;
- expected information gain on pass and fail;
- first bottleneck, dependencies, and parallel-safety.

Rank by information gain, testability, mission relevance, and cost divided by
duplication risk. The controller may promote at most one candidate, and only as
a verifier-bearing task.

## Outputs and limits

Return exactly `PROMOTE candidate X`, `REQUIRE expert consultation`, or
`NO USEFUL CANDIDATE`. A candidate is not a claim. Preserve it only if
selected, disproved, or made into a durable premise. Independent candidate
tests may run in parallel only with fixed inputs and budgets; route selection
and state mutation remain serial.
