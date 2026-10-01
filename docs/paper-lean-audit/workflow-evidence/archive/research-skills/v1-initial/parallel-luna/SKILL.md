---
name: parallel-luna
description: Run independent, adversarial review of a substantive task, claim, milestone, interface change, proof, experiment, or release using a fixed evidence packet.
---

# Parallel Luna Review

Use this skill when a project needs independent, adversarial review of a
substantive task, claim, milestone promotion, interface change, proof,
experiment, or release. “Luna” means an independent reviewer agent or fresh
review context; it is not a required model or service.

## Activation

Invoke for milestone promotion, a release candidate, a theorem or proof claim,
a cross-component interface change, an irreversible architecture decision, a
new external dependency, a major generated-artifact change, a scientific claim
promotion, an evidence-gate `PASS` request, or an explicit independent-audit
request. Do not invoke for trivial formatting-only changes unless they affect
generated artifacts, reproducibility, or public interfaces.

## Inputs

Every reviewer receives the same immutable evidence packet, the exact claim or
task, the assigned scope, and the required verdict format. Reviewers must not
see other reviewers' conclusions, the controller's preferred outcome, or
irrelevant implementation proposals.

## Workflow

The controller selects only relevant scopes:

### Scope A: statement and scope

Check the exact claim, quantifiers or API contract, success condition, scope
exclusions, and whether the result says more than the evidence supports.

### Scope B: assumptions and dependencies

Check hidden assumptions, version and pin compatibility, dependency
preconditions, interface invariants, and circular dependencies.

### Scope C: adversarial correctness

Check counterexamples, boundary cases, invalid inputs, race and failure paths,
side conventions, exception behavior, and regression risks.

### Scope D: evidence and reproducibility

Check that the command actually ran, the independent oracle exists, clean
replay is possible, deterministic-artifact policy is clear, traces and hashes
are complete, and tests are adequate.

### Scope E: maintainability and integration

Check public API effects, migration path, generated-file policy,
documentation consistency, stale code or tasks, and cross-component impact.

Run independent scopes in parallel when their inputs are fixed. One controller
integrates authoritative state serially.

## Valid outputs

Each reviewer returns exactly:

```markdown
Verdict: PASS | NEEDS FIX | INVALID

First fatal issue:
[none if PASS; otherwise one exact issue]

Evidence:
[file path, command output, counterexample, or dependency]

Required correction:
[one minimal corrective action]
```

The controller promotes only if all required reviewers return `PASS`. A valid
fatal issue is not removed by majority vote.

## Verification

Reviewers inspect the immutable evidence packet and independently check the
assigned scope. Review is a correctness and reproducibility audit, not a
substitute for the task's verifier or for primary evidence. Record all
verdicts in project-local evidence before promotion.

## Forbidden pseudo-progress

Do not reveal the controller's preferred outcome, let one reviewer see another
reviewer's conclusion, majority-vote away a valid fatal issue, or replace the
requested verdict with a broad redesign. Do not parallelize overlapping edits,
changes to the same generated artifact, changes to the same authoritative
ledger, dependent tasks with unfixed inputs, or conflicting architecture
decisions.

## Escalation

Send the first fatal issue to the active task when any reviewer returns `NEEDS
FIX` or `INVALID`. Rerun review only after a correction or new evidence exists.
If review identifies a conceptual block, return control to `bounded-exploration`
or `expert-escalation` according to their trigger conditions.

## Composition

Invoke after `evidence-gate` has assembled a promotion packet and before
`program-loop` records a substantive `PASS`. Safe parallel work includes
independent reviews, oracle and interface audits, counterexample searches,
literature reconnaissance, disjoint component reconnaissance, and independent
experimental replications. Use one controller for authoritative state changes.

## Parallel work policy

Parallelize independent review scopes and discovery tasks only after the claim
and evidence packet are frozen. Do not parallelize overlapping implementation
edits, shared generated artifacts, or shared authoritative state.
