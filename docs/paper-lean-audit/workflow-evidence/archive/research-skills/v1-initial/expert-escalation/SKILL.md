---
name: expert-escalation
description: Consult a specialist model, senior agent, domain expert, literature process, or human reviewer after a genuine conceptual block, while keeping all advice provisional until independently verified.
---

# Expert Escalation

Use this skill to consult an external specialist model, senior agent, domain
expert, literature process, or human reviewer after bounded exploration or
technical execution reaches a genuine conceptual block. This skill is generic
and does not assume a particular domain or service.

## Activation

Escalate only when:

- two materially different technical attempts failed;
- bounded exploration produced no executable candidate;
- a decision depends on specialist knowledge;
- a theorem, specification, or interface interpretation is genuinely
  ambiguous;
- a project-local protocol explicitly requires expert approval.

Do not escalate for routine coding, formatting, simple debugging, or work
already answerable by existing project state.

## Inputs

Prepare this consultation packet:

```markdown
Terminal mission:
[exact]

Active task:
[exact]

Established facts:
[only verified facts with evidence paths]

Current evidence:
[commands, outputs, proofs, traces]

Failed attempts:
[at least two, with first blocker]

Blacklisted routes:
[exact]

Constraints:
[domain conventions, compatibility requirements, resources]

Available tools:
[list]

Request:
[one bounded question]

Required falsification test:
[what would refute each proposed route]
```

## Workflow

Ask for at most three candidate mechanisms or decisions. For each candidate,
require:

- exact intermediate claim or decision;
- assumptions;
- reason it is noncircular;
- cheapest falsification test;
- first bottleneck;
- expected output artifact;
- next executable action.

Do not ask the expert for a full solution unless the active task is already a
narrowly bounded implementation or review task.

If a configured specialist agent is available, launch it using the
project-local consultation protocol. If unavailable, write a consultation
packet to the project-local evidence directory, mark the active task
`BLOCKED`, and do not simulate the specialist response.

## Valid outputs

Treat every response as `PROPOSED`. Preserve the response, its assumptions,
and any dissenting or rejected alternatives in the decision log. A consultation
does not itself produce `PASS`, close a task, or promote a project claim.

## Verification

After consultation, the controller must:

1. run an independent evidence gate;
2. add a bounded task only if it has a verifier;
3. preserve dissenting and rejected alternatives in the decision log;
4. independently falsify or verify the proposed route before promotion.

## Forbidden pseudo-progress

Do not present advice as an established fact, hide failed attempts or
blacklisted routes, ask an expert to replace the project verifier, or convert a
plausible mechanism into an implementation or milestone without independent
evidence.

## Escalation

This skill is the final specialist-consultation step for the current block.
If the response still leaves no verifier-bearing route, return to
`program-loop` with a reviewed hard stop or a new `bounded-exploration` packet;
do not escalate repeatedly without new evidence or a changed question.

## Composition

Invoke after `bounded-exploration` or two distinct failed attempts. Feed the
response to `evidence-gate`, then use `parallel-luna` for substantive proposed
decisions before `program-loop` changes authoritative state. Domain skills may
execute the resulting bounded task, but none may bypass independent
verification.

## Parallel work policy

Independent consultations may run in parallel only with the same immutable
packet and bounded questions. Integrate advice, evidence, and authoritative
state changes serially; do not ask parallel experts to edit the same artifact.
