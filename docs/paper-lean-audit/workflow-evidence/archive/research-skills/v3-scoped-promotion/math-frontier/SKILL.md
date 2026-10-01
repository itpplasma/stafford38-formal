---
name: math-frontier
description: Run a domain-neutral workflow for open or conjectural mathematics while preserving claim status, proof obligations, counterexamples, formalization faithfulness, and reproducible artifacts.
---

# Mathematical frontier

Use for unresolved, conjectural, or partially formalized mathematics. Do not
use for exposition, coursework, routine proof completion, or standard theorem
retrieval. The skill is domain-neutral; project-local conventions and records
are authoritative.

Use `program-loop` as the baseline. Activate `evidence-gate`,
`parallel-luna`, `bounded-exploration`, `expert-escalation`, and domain skills
only when their triggers apply.

## Fast-cycle discipline

Before a new attack, load the active task and its verifier; load the full
ledger, literature, contracts, and review protocol only when named or at
integration. Freeze:

- the exact quantifiers, domains, conventions, hypotheses, and terminal claim;
- the first unresolved dependency and the route's falsification condition;
- the scope boundary and the artifact that can verify it.

Use one mode per active task:

- `FOUNDATION`: audit definitions, hypotheses, conventions, literature, and
  dependencies;
- `EXPERIMENT`: run a bounded symbolic, numerical, finite, or counterexample
  search with inputs, command, environment, output, and scope;
- `PROOF`: prove one precise lemma, reduction, no-go result, special class, or
  formal statement, stopping at the first unsupported inference;
- `REVIEW`: attack proof gaps, side conditions, theorem faithfulness,
  reproducibility, and literature applicability;
- `SYNTHESIS`: integration only; reconcile evidence and choose the next leaf.

Do not formalize or record routine reading, scratch work, failed attempts, or
`NO_PROGRESS` unless a durable result, blocker, decision, or reusable artifact
must survive restart.

## Claim classification and lifecycle status

Every substantive claim has exactly one project classification:

```text
LITERATURE ESTABLISHED DERIVED FORMAL COMPUTATIONAL CONDITIONAL
CONJECTURAL REFUTED OPEN BLACKLISTED
```

`LITERATURE` requires checked hypotheses; `ESTABLISHED` is accepted project
knowledge; `DERIVED` follows from established facts; `FORMAL` is mechanically
checked; `COMPUTATIONAL` is executed bounded evidence; `CONDITIONAL` displays
unproved assumptions; `CONJECTURAL` is a proposed route; `REFUTED` has an
exact counterexample or fatal inference; `OPEN` is unresolved; `BLACKLISTED`
is not to be replayed without new input.

Never silently promote status. In particular:

```text
COMPUTATIONAL != DERIVED
FORMAL proof != faithfulness of the formalized statement
special case != universal theorem
CONDITIONAL implication != proof of its hypothesis
literature result != verified applicability
```

These classifications are not the fast-cycle result and must not replace the
lifecycle state record. For every durable promotion, also emit the
program-loop tuple with the exact `leaf_id`, `claim_id`, `parent_id`,
`leaf_status`, `claim_status`, `parent_status`, `evidence_gate_verdict`, and
`review_verdict`. Durable blocker, decision, and `NO_PROGRESS` records may
remain records of those outcomes without a promotion tuple. In particular,
`claim_status: CLOSED` for one named child and `parent_status: OPEN` for its
named umbrella is a valid state, not a review failure. Do not report it only
as “closes” versus “open”.

## Verification and outputs

Run the smallest relevant verifier for ordinary work. A durable claim or
promotion records the exact command, environment, inputs, outputs, evidence,
and scope. A literature premise records the primary source, version,
hypotheses, applicability check, and remaining gap.

For Lean or another proof assistant, check the intended statement first, then
imports/axioms, definitions, quantifiers, sides, domains, and hypotheses. A
compiling proof of the wrong theorem is `INVALID`.

Every fast cycle returns exactly one:

```text
PROVED FORMALIZED COMPUTED REFUTED CONDITIONAL BLOCKED NO_PROGRESS
```

Return the active leaf, mode, result, scope, evidence/artifact pointer, first
gap (or `NONE`), non-claims, and next executable action. Keep a full proof or
certificate in an artifact; the coordinator receives a compact pointer and
critical verification facts.

An exact counterexample is successful progress. Search low-dimensional,
degenerate, symmetry-breaking, smallest-parameter, side/quotient/lift,
uniform-bound, and excluded-hypothesis cases before broad proof machinery.
Bounded positive or negative evidence never becomes universal evidence by
implication.

## Composition and escalation

`program-loop` owns progression and state; the domain skill executes the
task; `evidence-gate` handles durable promotion; `parallel-luna` independently
reviews substantive claims; one controller integrates authoritative state.
Parallelize only distinct frozen-input tasks with positive coordination value.

Use `bounded-exploration` only after its stagnation trigger and at most three
falsifiable routes. Use `expert-escalation` only after its conceptual-block
trigger; every consultation remains `CONJECTURAL` until independently
verified.

At integration, reconcile claims with artifacts and reviews, run the relevant
regressions, retire duplicate or refuted routes, and select the next
dependency-ready leaf. Do not stop at a special case, bounded experiment,
formal lemma, or one refuted route. Stop only at a checked terminal proof,
checked terminal refutation, or a reviewed hard stop naming the exact missing
external input.
