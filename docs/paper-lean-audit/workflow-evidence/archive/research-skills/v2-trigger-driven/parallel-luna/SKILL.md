---
name: parallel-luna
description: Run an independent adversarial review from a frozen evidence packet.
---

# Parallel Luna Review

“Luna” means a fresh independent review context, not a required model. Use
this skill for meaningful code, derivations, experiments, claims, interfaces,
milestones, releases, and proofs.

## Levels

- `micro`: one reviewer, cheap and ephemeral; use when a small adversarial
  check is useful. Return `PASS` or the first issue and minimal fix.
- `focused`: two or three independent reviewers for theorem/refutation or
  milestone promotion, cross-component interfaces, major reusable artifacts,
  and high-risk claims.
- `full`: all relevant scopes for publication, release, terminal theorem or
  refutation, irreversible architecture, or explicit request.

Full review is not the default. Project rules may require a stricter tier.

## Packet and scopes

Freeze one immutable packet containing the exact claim/task, revision, inputs,
verifier, expected result, scope exclusions, and evidence. Do not reveal the
controller's preferred outcome or another reviewer's verdict.

Select only relevant scopes:

```text
A statement and scope
B assumptions and dependencies
C adversarial correctness and counterexamples
D evidence and reproducibility
E integration and maintainability
```

Review is not a substitute for the declared verifier or primary evidence.

## Verdicts

`micro` returns:

```text
PASS
FIRST ISSUE: ...
MINIMAL FIX: ...
```

Focused and full reviews return `PASS`, `NEEDS FIX`, or `INVALID`, with the
first fatal issue, evidence, and one required correction. A valid fatal issue
cannot be voted away. The controller changes state only after required reviews
and verifiers agree.

Review results are ephemeral unless they expose a defect or support a durable
promotion. Rerun only after a correction or new evidence. A conceptual block
returns to `bounded-exploration` or `expert-escalation`.
