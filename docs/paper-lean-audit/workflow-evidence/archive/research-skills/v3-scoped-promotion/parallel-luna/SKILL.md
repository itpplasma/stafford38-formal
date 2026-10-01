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

Freeze one immutable packet containing the exact claim/task ID, revision,
inputs, verifier, expected result, scope exclusions, and evidence. The
revision must identify `base_commit`, `worktree_patch_sha256` (or an exact
committed revision), and changed paths. A dirty worktree is reviewable when
that patch digest is recorded; reviewers must audit the frozen packet rather
than an unbounded moving worktree.

Status is ID-scoped. Distinguish the packet's `leaf_status`, its
`parent_status`, the evidence-gate verdict, and the review verdict. A child
record may validly have `leaf_status: PASS`, `claim_status: CLOSED`, and
`parent_status: OPEN` for its named parent; that is the normal dependency
state, not an evidence contradiction. Use the exact record below rather than
an unqualified “closes/open” sentence:

```text
leaf_id: <exact task ID>
claim_id: <exact registered claim ID>
parent_id: <exact parent/umbrella ID>
leaf_status: PASS
claim_status: CLOSED
parent_status: OPEN
evidence_gate_verdict: PENDING
review_verdict: PASS
```

Do not raise `NEEDS FIX` merely because those parent and child states differ;
raise it only for a field inconsistency, evidence/scope defect, or failed
verifier. The evidence-gate verdict is separate and must not be inferred from
the review verdict; use `PENDING` until that gate has run.

Do not reveal the controller's preferred outcome or another reviewer's verdict.

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
