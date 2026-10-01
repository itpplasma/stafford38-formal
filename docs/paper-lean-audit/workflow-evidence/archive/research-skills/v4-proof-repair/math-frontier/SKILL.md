---
name: math-frontier
description: Pursue an open or conjectural mathematical claim through focused discovery, falsification, repair, review, and sparse integration without confusing experiments or formal shells with proof.
---

# Mathematical Frontier

Use for open, conjectural, or genuinely unresolved mathematics. Do not use for
routine exercises, exposition, or standard theorem retrieval. Project-local
definitions, conventions, state, and verifiers remain authoritative.

## Start from the load-bearing frontier

Read only the current map, active claim, first unresolved dependency, and its
verifier. Load history, failed routes, literature, and review records when the
active question needs them or at integration.

Freeze a compact frontier packet:

```text
TERMINAL CLAIM: exact quantifiers, domain, conventions, and conclusion
ESTABLISHED: only facts used by the proposed next step
FIRST GAP: one unsupported implication or missing construction
FALSIFIER: what would refute the step or route
FORBIDDEN INFERENCES: exact known errors, not broad subject areas
CHECK: proof obligation, counterexample, source audit, or executable oracle
```

Prefer the smallest equivalent object or abstract question. Creative work is
usually stronger when it receives the load-bearing packet rather than the full
repository narrative.

## Choose one mode

- `DISCOVER`: seek a new mechanism or abstraction for the first gap.
- `FALSIFY`: search for a structural counterexample or missing hypothesis.
- `REPAIR`: replace the first invalid bridge in a promising proof while
  preserving everything downstream that remains valid.
- `REVIEW`: independently attack a frozen candidate; use `proof-audit` when
  available.
- `INTEGRATE`: minimize dependencies, reconcile evidence, and update durable
  state after a real mathematical delta.

Stop at the first unsupported inference. A precise counterexample or proof
repair is progress; another special case is not progress unless it tests a
named universal mechanism.

## Repair before abandoning

When review rejects a candidate:

1. name the first invalid implication;
2. retain later steps as a conditional suffix when they remain sound;
3. ask whether changing the intermediate object, category, filtration, or
   compactification repairs that implication;
4. retire the route only when an exact obstruction defeats the mechanism.

Blacklist the failed inference, not the whole mathematical domain. Reopen a
route when a new prerequisite directly addresses its recorded obstruction.

After a repair, strip away accidental hypotheses and ask for the strongest
abstract statement that still drives the proof. Then rerun adversarial review.

## Parallel discovery

One controller owns authoritative state and promotion. Parallel workers return
evidence and never edit current-status files.

Parallelize only genuinely different questions. Useful lanes include a direct
proof, a falsifier, a repair of a known bridge, and an abstraction/generalization.
Do not ask several workers the same unresolved question with cosmetic wording.
Idle capacity is preferable to correlated duplication.

Give each role the context it needs:

- creative worker: compact frontier packet and one mechanism;
- falsifier: exact claim, weakest hypotheses, and required counterexample data;
- reviewer: complete immutable candidate and named audit scopes;
- implementer: already reviewed statement, allowed files, and behavioral oracle.

Implementation and formalization follow mathematical review. They do not
substitute for it.

## Evidence discipline

Keep these distinctions explicit:

```text
finite computation != universal proof
formal proof != faithfulness of the encoded statement
conditional consumer != construction of its hypothesis
special class != terminal theorem
literature theorem != verified applicability
review verdict != project promotion
```

Use a CAS, proof assistant, or search tool only against a named information
target: an identity, obstruction, recurrence, hypothesis, or exact
counterexample. Record bounded evidence with its declared range and non-claims.

For a durable theorem or refutation, freeze the exact revision, preserve the
proof or certificate, verify cited hypotheses, run the smallest independent
oracle available, and obtain an adversarial audit. Terminal claims deserve
separate reviews of distinct load-bearing scopes and one final integration
check; duplicated reviews add little confidence.

## Sparse persistence

Keep scratch derivations, routine failed attempts, bounded probes, and ordinary
reviews ephemeral. Persist only a theorem, counterexample, reusable lemma,
route-changing obstruction, verified external premise, or restart-relevant
decision.

Prefer one current dashboard, one machine task record when needed, a small
load-bearing claim graph, and one integration commit per research wave. Do not
create a claim, checker, formalization, review, and status update merely because
a small result exists.

At integration:

1. minimize the proof's dependencies and remove superseded assumptions;
2. distinguish logical dependencies from exploratory history;
3. retire only the exact defeated inference or mechanism;
4. run relevant checks and freeze review inputs;
5. update authoritative state once and select the next highest-information gap.

An honest open handoff is not a terminal condition while an executable route
or persistent user goal remains. Continue with the next distinct repair,
falsifier, or abstraction. Stop only at a checked terminal proof, checked
terminal refutation, or a reviewed hard stop naming the exact missing external
input.

## Cycle output

Return a compact record:

```text
MODE / RESULT:
CLAIM AND SCOPE:
EVIDENCE:
FIRST GAP: none | exact implication
SURVIVING CONDITIONAL SUFFIX:
NON-CLAIMS:
NEXT DISTINCT ACTION:
```
