---
name: evidence-gate
description: Evaluate whether a task, claim, result, release, milestone, or architectural decision has enough independently reproducible evidence for promotion.
---

# Evidence Gate

Use this skill before promoting any task, claim, result, release, milestone,
or architectural decision. It distinguishes verified evidence from plausible
work.

## Activation

Activate at every requested promotion, at an evidence-gate `PASS` request, or
when a result is about to become an authoritative project claim.

## Inputs

Collect an evidence record containing:

- exact statement or observable;
- project or repository revision;
- dependencies or pinned revisions;
- input identifiers and hashes where applicable;
- command or derivation;
- tool and runtime versions where applicable;
- expected result;
- actual result;
- evidence paths;
- scope;
- explicit non-claims.

## Workflow

Classify evidence honestly:

```text
PROOF
FORMAL
EXECUTED
REPRODUCIBLE
LITERATURE
REVIEWED
CONDITIONAL
PROPOSED
REFUTED
```

Before `PASS`, answer all applicable gate questions:

1. What exact claim, feature, behavior, or theorem is being promoted?
2. What evidence establishes it?
3. Was the evidence actually produced in this repository state?
4. Is the expected result independent of the implementation or argument under
   test?
5. Are all dependencies pinned or identified?
6. What assumptions are required?
7. What does this result explicitly not prove?
8. What counterexample, regression, or failure mode was attempted?
9. What would falsify the claim?
10. Which project-local ledger item changes if this passes?

## Valid outputs

Return exactly one:

```text
PASS
NEEDS EVIDENCE
CONDITIONAL
REFUTED
INVALID
```

For every non-`PASS` verdict, identify only the first missing or invalid
evidence.

## Verification

For executable claims, require a replayable command from a clean checkout or
state exactly why this is impossible. For non-executable claims, require a
minimal derivation, source reference, or review record sufficient for an
independent reader to reproduce the reasoning.

Where an expected behavior is involved, require at least one independent
source of expectation:

- normative source;
- reviewed golden result;
- independent implementation;
- differential comparison;
- metamorphic invariant;
- formal proof assistant;
- hand-derived proof independent of the implementation;
- adversarial review with an explicit test.

## Forbidden pseudo-progress

Do not classify a script that has not run as `EXECUTED`, a finite experiment as
a universal theorem, a cited theorem with unchecked hypotheses as verified, or
a generated artifact that compiles as automatically correct. A passing build,
existing trace file, copied expected result without provenance, commit message,
or model self-assessment is not a sole oracle.

## Escalation

Return `NEEDS EVIDENCE` when any applicable gate question lacks an answer.
Invoke `parallel-luna` for an independent audit when the result is substantive.
Use `expert-escalation` only for a genuine conceptual block after its stated
trigger conditions; expert advice remains `PROPOSED` until independently
verified.

## Composition

Run after the domain skill has produced a result and before
`program-loop` promotes it. Pair with `parallel-luna` for substantive claims,
and record the verdict and evidence paths in the project-local ledger. This
skill evaluates evidence; it does not supply domain expertise or silently
repair a failed claim.

## Parallel work policy

Independent oracle checks and evidence audits may run in parallel when their
inputs are immutable. Keep the verdict and ledger update serial, and never let
parallel reviewers replace the declared verifier.
