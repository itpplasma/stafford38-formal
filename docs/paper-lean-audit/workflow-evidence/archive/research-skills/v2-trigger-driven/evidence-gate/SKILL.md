---
name: evidence-gate
description: Decide whether a result has enough independent, reproducible evidence for durable promotion.
---

# Evidence Gate

Use the full gate only for a durable theorem/refutation, milestone, release,
reusable artifact, external premise, or cross-repository interface/pin. For
ordinary work use the smallest relevant check: test, compiler run, Lean/CAS
check, derivation check, or reproducible command.

## Evidence record

Record only when the result may be promoted:

- exact claim or observable and project revision;
- inputs, dependencies, versions, and hashes;
- command or derivation, expected result, and actual result;
- scope, explicit non-claims, and evidence paths;
- the independent oracle or falsification attempt.

Evidence kinds are:

```text
HAND_DERIVATION  FORMAL_CHECK  EXECUTION  REPRODUCTION
LITERATURE_SOURCE  INDEPENDENT_REVIEW  BENCHMARK  ORACLE
```

These are not claim or task states. The gate verdict is one of:
`PASS`, `NEEDS EVIDENCE`, `CONDITIONAL`, `REFUTED`, or `INVALID`.

## Gate questions

Before `PASS`, ask:

1. What exact claim is promoted, and what remains outside its scope?
2. Was the evidence produced for this project revision?
3. Are assumptions, dependencies, and versions identified?
4. Is the expected result independent of the implementation or argument?
5. Was a counterexample, regression, or falsification attempt made?
6. Can an independent reader reproduce the result?
7. Which project-local state changes if it passes?

A finite experiment is not a universal theorem; a compiling formalization is
not evidence for the intended theorem; an unchecked citation is not a verified
literature premise.

## Review and state

Use `parallel-luna` for an independent audit when the result is substantive.
Micro review is ephemeral. Focused or full review is required only at the
project's stated promotion boundary. Keep the verdict and ledger update
serial. A state commit may record a blocker or decision, but must not claim a
theorem or feature `PASS` without its evidence.

The controller verifies and promotes; workers and reviewers remain provisional.
